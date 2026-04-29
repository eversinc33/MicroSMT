import sys
import traceback
import idc
import idaapi
import ida_ua          

try:
    import ida_hexrays as hr
    _HR_LOADED = hr.init_hexrays_plugin()
except Exception:
    _HR_LOADED = False
    hr = None

try:
    import z3 as _z3
    _Z3_LOADED = True
except ImportError:
    _Z3_LOADED = False
    _z3 = None

# Config
PATCH_PREDICATES = False

# Globals
_BAR = "=" * 68
ALWAYS_TAKEN = "Always taken/true   [opaque predicate]"
NEVER_TAKEN  = "Never taken/false   [opaque predicate]"
REAL_BRANCH  = "Real branch/cond    [condition-dependent]"
INCONCLUSIVE = "Inconclusive        [unsupported / unknown]"

# ---------------------------------------------------------------------------

def _addr_bits():
    try:
        return 64 if idaapi.get_inf_structure().is_64bit() else 32
    except Exception:
        return 64

# ---------------------------------------------------------------------------
# Z3 bit-vector helpers

def expr_to_text(expr):
    if _z3.is_bv_value(expr):
        return str(expr.as_long())

    if _z3.is_const(expr) and expr.num_args() == 0:
        return str(expr)

    if _z3.is_true(expr):
        return "true"

    if _z3.is_false(expr):
        return "false"

    if _z3.is_bv_value(expr):
        return str(expr.as_long())

    if _z3.is_const(expr) and expr.num_args() == 0:
        return str(expr)

    decl = expr.decl().kind()
    args = [expr_to_text(a) for a in expr.children()]

    # extract condition if we are in a setcc modeled expr
    if decl == _z3.Z3_OP_ITE:
        cond, tval, fval = expr.children()

        if (_z3.is_bv_value(tval)
            and _z3.is_bv_value(fval)
            and tval.as_long() == 1
            and fval.as_long() == 0
        ):
            return expr_to_text(cond)
        raise RuntimeError(f"Unsupported ITE: {expr}")

    # Bool ops
    if decl == _z3.Z3_OP_EQ:
        return f"({args[0]} == {args[1]})"

    if decl == _z3.Z3_OP_DISTINCT:
        return f"({args[0]} != {args[1]})"

    if decl == _z3.Z3_OP_NOT:
        return f"(!{args[0]})"

    if decl == _z3.Z3_OP_AND:
        return f"({' && '.join(args)})"

    if decl == _z3.Z3_OP_OR:
        return f"({' || '.join(args)})"

    # BitVec ops
    if decl == _z3.Z3_OP_BADD:
        return f"({args[0]} + {args[1]})"

    if decl == _z3.Z3_OP_BSUB:
        return f"({args[0]} - {args[1]})"

    if decl == _z3.Z3_OP_BMUL:
        return f"({args[0]} * {args[1]})"

    if decl == _z3.Z3_OP_BAND:
        return f"({args[0]} & {args[1]})"

    if decl == _z3.Z3_OP_BOR:
        return f"({args[0]} | {args[1]})"

    if decl == _z3.Z3_OP_BXOR:
        return f"({args[0]} ^ {args[1]})"

    if decl == _z3.Z3_OP_BNOT:
        return f"(~{args[0]})"

    if decl == _z3.Z3_OP_BNEG:
        return f"(-{args[0]})"

    if decl == _z3.Z3_OP_BSHL:
        return f"({args[0]} << {args[1]})"

    if decl == _z3.Z3_OP_BLSHR:
        return f"({args[0]} >> {args[1]})"

    if decl == _z3.Z3_OP_ZERO_EXT:
        return args[0]

    if decl == _z3.Z3_OP_SIGN_EXT:
        return args[0]

    # BitVec comparisons
    if decl == _z3.Z3_OP_ULT:
        return f"({args[0]} < {args[1]})"

    if decl == _z3.Z3_OP_ULEQ:
        return f"({args[0]} <= {args[1]})"

    if decl == _z3.Z3_OP_UGT:
        return f"({args[0]} > {args[1]})"

    if decl == _z3.Z3_OP_UGEQ:
        return f"({args[0]} >= {args[1]})"

    if decl == _z3.Z3_OP_SLT:
        return f"({args[0]} <s {args[1]})"

    if decl == _z3.Z3_OP_SLEQ:
        return f"({args[0]} <=s {args[1]})"

    if decl == _z3.Z3_OP_SGT:
        return f"({args[0]} >s {args[1]})"

    if decl == _z3.Z3_OP_SGEQ:
        return f"({args[0]} >=s {args[1]})"

    raise RuntimeError(f"Unsupported op: {expr}")

def bv_val(val, bits):
    """Create a Z3 BitVecVal, masking val to the appropriate width."""
    return _z3.BitVecVal(val & ((1 << bits) - 1), bits)

def bv_sym(name, bits, cache):
    """Return a cached Z3 BitVec symbolic variable."""
    key = (name, bits)
    if key not in cache:
        cache[key] = _z3.BitVec(name, bits)
    return cache[key]

def bv_resize(bv, bits):
    """Zero-extend or truncate a Z3 BitVec to exactly `bits` bits."""
    cur = bv.size()
    if cur == bits:
        return bv
    if cur > bits:
        return _z3.Extract(bits - 1, 0, bv)
    return _z3.ZeroExt(bits - cur, bv)

def bool_to_bv8(cond):
    """Convert a Z3 Bool to an 8-bit BitVec (1 = true, 0 = false)."""
    return _z3.If(cond, bv_val(1, 8), bv_val(0, 8))

# ---------------------------------------------------------------------------
# Microcode helpers

def _mop_def_key(mop):
    """
    Return a hashable key that uniquely identifies the storage location
    that this mop writes to (or reads from), or None if not applicable.
    Used to build the definition table.
    """
    t = mop.t
    if t == hr.mop_r:
        return ('r', mop.r, mop.size)
    if t == hr.mop_l:
        return ('l', mop.l.idx, mop.size)
    if t == hr.mop_S:
        return ('S', mop.s.off, mop.size)
    return None

def _def_table_lookup(table, fuzzy, key):
    """
    Look up key in the def table.  First tries an exact (type, id, size)
    match; if that fails, retries ignoring size so that a write to a wider
    register (e.g. eax) can resolve a later read of a sub-register (e.g. al).
    The fuzzy dict is pre-built to map (type, id) -> last-written minsn_t,
    guaranteeing "last write wins" semantics for the size-agnostic fallback.
    Returns the minsn_t, or None.
    """
    insn = table.get(key)
    if insn is not None:
        return insn
    # Size-agnostic fallback: use pre-built dict so we always get the last write,
    # not an arbitrary earlier one from dict iteration order.
    return fuzzy.get((key[0], key[1]))

def _build_def_table(block, stop_insn):
    """
    Scan mblock_t instructions forward (from head, stopping before
    stop_insn) and return:
      table : (type, id, size) -> last minsn_t  (exact match)
      fuzzy : (type, id)       -> last minsn_t  (size-agnostic, last write wins)
    """
    table = {}
    fuzzy = {}
    stop_this = stop_insn.this  # SWIG creates a new proxy object on each access,
                                # so `insn is stop_insn` is always False. Compare
                                # the underlying C++ pointers via .this instead.
    insn = block.head
    while insn is not None and insn.this != stop_this:
        if insn.d.t != hr.mop_z:
            key = _mop_def_key(insn.d)
            if key is not None:
                table[key] = insn
                fuzzy[(key[0], key[1])] = insn
        insn = insn.next
    return table, fuzzy

def _is_cond_branch_op(op):
    """Return True for any microcode conditional branch opcode."""
    return op in (hr.m_jcnd, hr.m_jnz, hr.m_jz,
                  hr.m_jae, hr.m_jb, hr.m_ja, hr.m_jbe,
                  hr.m_jg, hr.m_jge, hr.m_jl, hr.m_jle)

def _is_setcc_op(op):
    """Return True for any modelable microcode set-on-condition opcode."""
    # m_seto / m_setp excluded — can't model overflow/parity flag soundly
    return op in (hr.m_setz, hr.m_setnz, hr.m_setae, hr.m_setb,
                  hr.m_seta, hr.m_setbe, hr.m_setg, hr.m_setge,
                  hr.m_setl, hr.m_setle, hr.m_sets)

def _find_jcnd_block(mba, target_ea):
    """
    Search all microcode blocks for a conditional branch instruction
    that corresponds to the assembly conditional branch at target_ea.
    Returns (mblock_t, minsn_t) or (None, None).
    """
    for i in range(mba.qty):
        blk = mba.get_mblock(i)
        tail = blk.tail
        if tail is None or not _is_cond_branch_op(tail.opcode):
            continue
        # Prefer an exact ea match on the tail instruction
        if tail.ea == target_ea:
            return blk, tail
        # otherwise, the assembly address lies within this block's range
        if blk.start <= target_ea < blk.end:
            return blk, tail
    return None, None

def _find_setcc_insn(mba, target_ea):
    """
    Search all microcode blocks for a set-on-condition instruction at target_ea.
    Unlike jcnd, setcc can appear anywhere in a block (not only at the tail).
    Returns (mblock_t, minsn_t) or (None, None).
    """
    # First pass: exact EA match anywhere in the MBA
    for i in range(mba.qty):
        blk = mba.get_mblock(i)
        insn = blk.head
        while insn is not None:
            if _is_setcc_op(insn.opcode) and insn.ea == target_ea:
                return blk, insn
            insn = insn.next
    # Second pass: target_ea falls within a block range — take the first setcc in that block
    for i in range(mba.qty):
        blk = mba.get_mblock(i)
        if blk.start <= target_ea < blk.end:
            insn = blk.head
            while insn is not None:
                if _is_setcc_op(insn.opcode):
                    return blk, insn
                insn = insn.next
    return None, None

def _slice_count(block, stop_insn):
    """Count instructions in block before stop_insn to get slice size."""
    n = 0
    stop_this = stop_insn.this
    insn = block.head
    while insn is not None and insn.this != stop_this:
        n += 1
        insn = insn.next
    return n

def _reg_name(reg, size):
    """Human-readable register name for use as a z3 symbol."""
    name = hr.get_mreg_name(reg, size)
    if name:
        return name
    return f"mreg{reg}_s{size}"

# ---------------------------------------------------------------------------
# z3 Lifter

class LiftError(Exception):
    """Raised when the lifter cannot model a microcode construct."""

class Z3Lifter:
    """
    Lifts a Hex-Rays microcode condition (and its backward-sliced
    dependencies) into a Z3 expression tree.

    Strategy:
      - Follow mop_d chains directly (inline SSA defs).
      - For mop_r / mop_l / mop_S operands that lack an mop_d link,
        consult the pre-built definition table for the block.
      - Unknown / cross-block values become unconstrained z3 BitVec
        symbols.
      - Bail with LiftError on constructs that cannot be modeled
        soundly (memory aliasing, flag helpers, etc.).
    """

    MAX_DEPTH = 128

    def __init__(self, mba, block, jcnd_insn):
        self.mba        = mba
        self.block      = block
        self.jcnd       = jcnd_insn
        self.abits      = _addr_bits()
        self.sym_cache  = {}          # (name, bits) -> z3.BitVec
        self.def_table, self.fuzzy_table = _build_def_table(block, jcnd_insn)
        self._depth     = 0
        self._unk_seq   = 0           # Counter for anonymous unknowns
        # EA range of this block — used to guard against cross-block mop_d refs.
        self._blk_start = block.start
        self._blk_end   = block.end
        # List of SwigPyObject .this values for instructions actually in the
        # block linked list.  mop_d sub-expressions can point to synthetic
        # instructions whose EA falls inside the block range but that are NOT in
        # the list.  Calling _build_def_table with such a stop_insn scans the
        # entire block (stop is never found), producing a def_table that can
        # create cycles through self-referential writes (e.g. var = f(var)).
        # We only rebuild scope for real list members.
        # NOTE: SwigPyObject defines __eq__ (compares C++ addresses) but NOT
        # __hash__, so we store them in a list and use any() with == for lookup.
        self._blk_insn_thises = []
        insn = block.head
        while insn is not None:
            self._blk_insn_thises.append(insn.this)
            insn = insn.next

    def lift_condition(self):
        """
        Return a z3 Bool: True when the branch is taken.

        At MMAT_LOCOPT, Hex-Rays uses comparison-style jump opcodes
        (m_jnz, m_jz, m_jg, ...) with semantics "if l <op> r, goto d".
        The generic m_jcnd (higher maturity) tests "if l != 0, goto r".
        """
        op = self.jcnd.opcode

        if op == hr.m_jcnd:
            # Generic: taken if l != 0  — compare at original width, not truncated to 8
            bv = self._mop(self.jcnd.l)
            return bv != bv_val(0, bv.size())

        # Comparison-style opcodes: l <op> r
        lv = self._mop(self.jcnd.l)
        rv = self._mop(self.jcnd.r)
        bits = max(lv.size(), rv.size())
        lv = bv_resize(lv, bits)
        rv = bv_resize(rv, bits)

        if op == hr.m_jnz:   return lv != rv
        if op == hr.m_jz:    return lv == rv
        if op == hr.m_jg:    return lv > rv               # signed >
        if op == hr.m_jge:   return lv >= rv              # signed >=
        if op == hr.m_jl:    return lv < rv               # signed <
        if op == hr.m_jle:   return lv <= rv              # signed <=
        if op == hr.m_ja:    return _z3.UGT(lv, rv)       # unsigned >
        if op == hr.m_jae:   return _z3.UGE(lv, rv)       # unsigned >=
        if op == hr.m_jb:    return _z3.ULT(lv, rv)       # unsigned <
        if op == hr.m_jbe:   return _z3.ULE(lv, rv)       # unsigned <=

        raise LiftError(f"Unsupported branch opcode: {op}")

    def lift_setcc_condition(self, insn):
        """
        Return a z3 Bool: True when the setcc instruction would write 1.
        insn is the m_setz / m_setnz / … microcode instruction.
        """
        op = insn.opcode

        if op == hr.m_sets:
            # sets: result = MSB of l (no r operand)
            lv = self._mop(insn.l)
            msb = _z3.Extract(lv.size() - 1, lv.size() - 1, lv)
            return msb == bv_val(1, 1)

        lv = self._mop(insn.l)
        rv = self._mop(insn.r)
        bits = max(lv.size(), rv.size())
        lv = bv_resize(lv, bits)
        rv = bv_resize(rv, bits)

        if op == hr.m_setz:   return lv == rv
        if op == hr.m_setnz:  return lv != rv
        if op == hr.m_setl:   return lv < rv               # signed <
        if op == hr.m_setg:   return lv > rv               # signed >
        if op == hr.m_setle:  return lv <= rv              # signed <=
        if op == hr.m_setge:  return lv >= rv              # signed >=
        if op == hr.m_setb:   return _z3.ULT(lv, rv)      # unsigned <
        if op == hr.m_seta:   return _z3.UGT(lv, rv)      # unsigned >
        if op == hr.m_setbe:  return _z3.ULE(lv, rv)      # unsigned <=
        if op == hr.m_setae:  return _z3.UGE(lv, rv)      # unsigned >=

        raise LiftError(f"Unsupported setcc opcode: {op}")

    def symbols(self):
        """Return {name: z3.BitVec} for every symbolic variable introduced."""
        return {name: var for (name, _bits), var in self.sym_cache.items()}

    def _mop(self, mop):
        """Lift an mop_t to a z3 BitVec. Raises LiftError on failure."""
        self._depth += 1
        if self._depth > self.MAX_DEPTH:
            self._depth -= 1
            raise LiftError("Recursion depth exceeded - slice too deep or cyclic")
        try:
            return self._mop_inner(mop)
        finally:
            self._depth -= 1

    def _mop_inner(self, mop):
        t    = mop.t
        bits = max(mop.size * 8, 1)

        # ---- Numeric constant ----
        if t == hr.mop_n:
            return bv_val(mop.nnn.value, bits)

        # ---- Inline result of another instruction (SSA def) ----
        if t == hr.mop_d:
            dep = mop.d
            # Guard: reject refs to instructions outside this block's EA range.
            # Synthetic instructions (ea == BADADDR) are assumed to be local.
            dep_ea = dep.ea
            if dep_ea != idaapi.BADADDR and not (self._blk_start <= dep_ea < self._blk_end):
                self._unk_seq += 1
                return _z3.BitVec(f"unk{self._unk_seq}_xblk_{dep_ea:x}_{bits}b", bits)
            return self._insn_result(dep)

        # ---- Register ----
        if t == hr.mop_r:
            key = _mop_def_key(mop)
            if key is not None:
                insn = _def_table_lookup(self.def_table, self.fuzzy_table, key)
                if insn is not None:
                    return bv_resize(self._insn_result(insn), bits)
            return bv_sym(_reg_name(mop.r, mop.size), bits, self.sym_cache)

        # ---- Local variable ----
        if t == hr.mop_l:
            key = _mop_def_key(mop)
            if key is not None:
                insn = _def_table_lookup(self.def_table, self.fuzzy_table, key)
                if insn is not None:
                    return bv_resize(self._insn_result(insn), bits)
            return bv_sym(f"lvar{mop.l.idx}", bits, self.sym_cache)

        # ---- Stack variable ----
        if t == hr.mop_S:
            key = _mop_def_key(mop)
            if key is not None:
                insn = _def_table_lookup(self.def_table, self.fuzzy_table, key)
                if insn is not None:
                    return bv_resize(self._insn_result(insn), bits)
            return bv_sym(f"stk_{mop.s.off & 0xFFFFFFFF:x}", bits, self.sym_cache)

        # ---- Global variable — treat as unconstrained symbolic ----
        if t == hr.mop_v:
            gname = idc.get_name(mop.g) or f"g_{mop.g:x}"
            return bv_sym(gname, bits, self.sym_cache)

        # ---- Operand pair — lift low half ----
        if t == hr.mop_p:
            return self._mop(mop.pair.lop)

        # ---- Anything else: fresh unconstrained unknown ----
        self._unk_seq += 1
        return _z3.BitVec(f"unk{self._unk_seq}_t{t}_{bits}b", bits)

    def _insn_result(self, insn):
        """Lift one microcode instruction to z3"""
        op     = insn.opcode
        d_bits = max(insn.d.size * 8, 1)

        # Each instruction's register operands must be resolved against the
        # definitions that existed *before* that instruction, not before the
        # outer target (jcnd/setcc).  Rebuild a scoped def_table and restore
        # the caller's table via finally so the outer context is unaffected.
        #
        # IMPORTANT: only rebuild scope when the instruction is a real member of
        # the block's linked list (its C++ pointer is in _blk_insn_ptrs).
        # Synthetic mop_d sub-instructions may have EAs inside the block range
        # but are NOT in the list.  For those, _build_def_table never finds the
        # stop pointer and scans the full block — this can produce cycles when a
        # later instruction writes to a variable that the sub-expression reads
        # (e.g.  var_x = 8 * (var_x >> 11) + C).  For synthetic sub-expressions
        # the caller's def_table is already correctly scoped.
        rebuild = insn.this in self._blk_insn_thises
        if rebuild:
            saved_dt, saved_ft = self.def_table, self.fuzzy_table
            self.def_table, self.fuzzy_table = _build_def_table(self.block, insn)

        # Helpers that lift operands and normalize sizes
        def L():
            return self._mop(insn.l)

        def R():
            return self._mop(insn.r)

        def LR():
            """Lift both operands, widen to the same size."""
            lv = self._mop(insn.l)
            rv = self._mop(insn.r)
            tb = max(lv.size(), rv.size(), d_bits)
            return bv_resize(lv, tb), bv_resize(rv, tb)

        try:
            # ---- Move ----
            if op == hr.m_mov:
                return bv_resize(L(), d_bits)

            # ---- Unary arithmetic / logic ----
            if op == hr.m_neg:
                return bv_resize(-L(), d_bits)
            if op == hr.m_bnot:          # bitwise NOT
                return bv_resize(~L(), d_bits)
            if op == hr.m_lnot:          # logical NOT: result is 0 or 1
                lv = L()
                return bool_to_bv8(lv == bv_val(0, lv.size()))

            # ---- Binary arithmetic ----
            if op == hr.m_add:
                lv, rv = LR()
                return bv_resize(lv + rv, d_bits)
            if op == hr.m_sub:
                lv, rv = LR()
                return bv_resize(lv - rv, d_bits)
            if op == hr.m_mul:
                lv, rv = LR()
                return bv_resize(lv * rv, d_bits)
            if op == hr.m_udiv:
                lv, rv = LR()
                return bv_resize(_z3.UDiv(lv, rv), d_bits)
            if op == hr.m_sdiv:
                lv, rv = LR()
                return bv_resize(lv / rv, d_bits)
            if op == hr.m_umod:
                lv, rv = LR()
                return bv_resize(_z3.URem(lv, rv), d_bits)
            if op == hr.m_smod:
                lv, rv = LR()
                return bv_resize(_z3.SRem(lv, rv), d_bits)
            # ---- Bitwise ----
            if op == hr.m_and:
                lv, rv = LR()
                return bv_resize(lv & rv, d_bits)
            if op == hr.m_or:
                lv, rv = LR()
                return bv_resize(lv | rv, d_bits)
            if op == hr.m_xor:
                lv, rv = LR()
                return bv_resize(lv ^ rv, d_bits)

            # ---- Shifts ----
            if op == hr.m_shl:
                lv = L()
                rv = bv_resize(R(), lv.size())
                return bv_resize(lv << rv, d_bits)
            if op == hr.m_shr:           # logical right shift
                lv = L()
                rv = bv_resize(R(), lv.size())
                return bv_resize(_z3.LShR(lv, rv), d_bits)
            if op == hr.m_sar:           # arithmetic right shift
                lv = L()
                rv = bv_resize(R(), lv.size())
                return bv_resize(lv >> rv, d_bits)
            # ---- Extension / truncation ----
            if op == hr.m_xdu:           # zero-extend
                lv = L()
                if lv.size() >= d_bits:
                    return bv_resize(lv, d_bits)
                return _z3.ZeroExt(d_bits - lv.size(), lv)
            if op == hr.m_xds:           # sign-extend
                lv = L()
                if lv.size() >= d_bits:
                    return bv_resize(lv, d_bits)
                return _z3.SignExt(d_bits - lv.size(), lv)
            if op == hr.m_low:           # low bytes (truncate)
                return bv_resize(L(), d_bits)
            if op == hr.m_high:          # high bytes
                lv = L()
                if lv.size() > d_bits:
                    return _z3.Extract(lv.size() - 1, lv.size() - d_bits, lv)
                # Source narrower than dest — undefined in valid microcode; conservatively unknown
                self._unk_seq += 1
                return _z3.BitVec(f"unk{self._unk_seq}_high_narrow_{d_bits}b", d_bits)

            # ---- Set-on-condition (result: 1-byte boolean) ----
            if op == hr.m_setz:
                lv, rv = LR()
                return bool_to_bv8(lv == rv)
            if op == hr.m_setnz:
                lv, rv = LR()
                return bool_to_bv8(lv != rv)
            if op == hr.m_setl:          # signed <
                lv, rv = LR()
                return bool_to_bv8(lv < rv)
            if op == hr.m_setg:          # signed >
                lv, rv = LR()
                return bool_to_bv8(lv > rv)
            if op == hr.m_setle:         # signed <=
                lv, rv = LR()
                return bool_to_bv8(lv <= rv)
            if op == hr.m_setge:         # signed >=
                lv, rv = LR()
                return bool_to_bv8(lv >= rv)
            if op == hr.m_setb:          # unsigned < (below)
                lv, rv = LR()
                return bool_to_bv8(_z3.ULT(lv, rv))
            if op == hr.m_seta:          # unsigned > (above)
                lv, rv = LR()
                return bool_to_bv8(_z3.UGT(lv, rv))
            if op == hr.m_setbe:         # unsigned <=
                lv, rv = LR()
                return bool_to_bv8(_z3.ULE(lv, rv))
            if op == hr.m_setae:         # unsigned >=
                lv, rv = LR()
                return bool_to_bv8(_z3.UGE(lv, rv))
            if op == hr.m_sets:          # sign flag (MSB == 1)
                lv = L()
                msb = _z3.Extract(lv.size() - 1, lv.size() - 1, lv)
                return bool_to_bv8(msb == bv_val(1, 1))
            if op == hr.m_seto:
                raise LiftError("m_seto (overflow flag) not modeled")
            if op == hr.m_setp:
                raise LiftError("m_setp (parity flag) not modeled")
            if op in (hr.m_cfadd, hr.m_ofadd, hr.m_cfshl, hr.m_cfshr):
                raise LiftError(f"Flag carry/overflow helper opcode {op} not modeled")
            if op == hr.m_ldx:
                raise LiftError("m_ldx (memory load) — aliasing too ambiguous")

            # ---- Fallback: introduce a fresh symbolic result ----
            # This covers any other opcodes (calls, etc.) conservatively.
            self._unk_seq += 1
            sym_name = f"insn_op{op}_ea{insn.ea:x}"
            return bv_sym(sym_name, d_bits, self.sym_cache)

        except LiftError:
            raise
        except Exception as exc:
            raise LiftError(f"Error lifting opcode {op} at {insn.ea:#x}: {exc}") from exc
        finally:
            if rebuild:
                self.def_table, self.fuzzy_table = saved_dt, saved_ft


# ---------------------------------------------------------------------------
# Solver

def _solve(z3_bool, timeout_ms=10_000):
    """
    Given a Z3 Bool (True = branch taken), check satisfiability of
    both outcomes using push/pop.

    Returns:
        (taken_sat: bool, not_taken_sat: bool, classification: str)
    """
    s = _z3.Solver()
    s.set("timeout", timeout_ms)

    # Can the branch be taken?
    s.push()
    s.add(z3_bool)
    r_taken = s.check()
    s.pop()

    # Can the branch be NOT taken?
    s.push()
    s.add(_z3.Not(z3_bool))
    r_not_taken = s.check()
    s.pop()

    taken     = (r_taken     == _z3.sat)
    not_taken = (r_not_taken == _z3.sat)

    if taken and not not_taken:
        cls = ALWAYS_TAKEN
    elif not taken and not_taken:
        cls = NEVER_TAKEN
    elif taken and not_taken:
        cls = REAL_BRANCH
    else:
        cls = INCONCLUSIVE

    return taken, not_taken, cls

def _print_predicate_info(ea, predicate_str, slice_size, symbols, taken, not_taken, cls, expression=None, error=None):
    print(_BAR)
    print(f"  MicroSMT -  branch @ {ea:#x}")
    if expression is not None: print(f"  {expr_to_text(expression)}")
    if error:
        print(f"  ERROR: {error}")
        print(_BAR)
        return
    print(f"  Address        : {ea:#x}")
    #print(f"  Predicate      : {predicate_str}")
    print(f"  Slice size     : {slice_size} instruction(s)")
    if symbols:
        names = sorted(symbols.keys())
        sym_str = ", ".join(names[:8])
        if len(names) > 8:
            sym_str += f"  (+{len(names) - 8} more)"
        print(f"  Symbolic var        : {sym_str}")
    print(f"  Taken SAT           : {'yes' if taken else 'no'}")
    print(f"  Not-Taken SAT       : {'yes' if not_taken else 'no'}")
    print(f"  >>  {cls}")
    print(_BAR)

# ---------------------------------------------------------------------------
# Conditional branch itype set (x86/x86-64, built dynamically)

def _build_cond_jmps():
    _names = [
        'NN_jz',  'NN_jnz',  'NN_ja',    'NN_jb',   'NN_jg',
        'NN_jl',  'NN_jge',  'NN_jle',   'NN_jbe',  'NN_jae',
        'NN_jo',  'NN_jno',  'NN_js',    'NN_jns',  'NN_jp',
        'NN_jnp', 'NN_jcxz', 'NN_jecxz', 'NN_jrcxz',
    ]
    result = set()
    for n in _names:
        v = getattr(idaapi, n, None)
        if v is not None:
            result.add(v)
    return frozenset(result)

_COND_JMPS = _build_cond_jmps()

def _build_setcc_itypes():
    _names = [
        'NN_setz',  'NN_sete',  'NN_setnz', 'NN_setne',
        'NN_seta',  'NN_setae', 'NN_setb',  'NN_setbe',
        'NN_setg',  'NN_setge', 'NN_setl',  'NN_setle',
        'NN_sets',  'NN_setns', 'NN_seto',  'NN_setno',
        'NN_setp',  'NN_setnp',
    ]
    result = set()
    for n in _names:
        v = getattr(idaapi, n, None)
        if v is not None:
            result.add(v)
    return frozenset(result)

_SETCC_ITYPES = _build_setcc_itypes()

# ---------------------------------------------------------------------------
# Shellcode block-range finder

def _find_block_range(ea, max_back_insns=200):
    """
    Heuristically locate the basic-block range [start, end) containing ea
    without needing a defined function (e.g. shellcode).

    Walk backward until:
      - a branch target is found (address has incoming xrefs), or
      - the preceding instruction does not fall through (CF_STOP set), or
      - max_back_insns is exhausted.
    Walk forward until:
      - a block terminator is found (CF_STOP or CF_JUMP set).

    Returns (start, end) or (None, None) on failure.
    """
    # --- Backward: find block start ---
    # Stop on branch targets, non-fall-through predecessors, or data gaps
    # (prev_head can silently skip data regions in shellcode).
    start = ea
    for _ in range(max_back_insns):
        prev = idc.prev_head(start)
        if prev == idaapi.BADADDR:
            break
        # start is a branch target — it begins a new block
        if idaapi.has_xref(idaapi.get_flags(start)):
            break
        prev_insn = idaapi.insn_t()
        if not idaapi.decode_insn(prev_insn, prev):
            break
        # Guard against data gaps: prev must be contiguous with start
        if prev + prev_insn.size != start:
            break
        # prev doesn't fall through — start is the first insn of a new block
        if prev_insn.get_canon_feature() & idaapi.CF_STOP:
            break
        start = prev

    # --- Forward: find block end (one past the terminator).
    # If we hit a terminator before reaching ea (e.g. data gap caused the
    # backward walk to land in the wrong block), restart from ea.
    cur = start
    while cur - start < 65536:
        insn = idaapi.insn_t()
        if not idaapi.decode_insn(insn, cur):
            # Non-code bytes — treat as boundary
            end = cur
            break
        next_cur = cur + insn.size
        feat = insn.get_canon_feature()
        if feat & (idaapi.CF_STOP | idaapi.CF_JUMP):
            end = next_cur
            if next_cur > ea:
                break
            # Terminator before ea — we walked into the wrong block.
            # Reset: treat ea as the block start and scan forward from there.
            start = ea
            cur = ea
            continue
        cur = next_cur
    else:
        end = cur

    return (start, end) if start <= ea < end else (None, None)

# ---------------------------------------------------------------------------
# Patcher

def _patch_branch(ea, cls):
    insn = idaapi.insn_t()
    if not idaapi.decode_insn(insn, ea):
        print(f"[MicroSMT patch] Cannot decode instruction at {ea:#x}")
        return False

    insn_len = insn.size

    if cls == ALWAYS_TAKEN:
        # Resolve the branch target at the IDA level (handles all encodings).
        target_ea = idc.get_operand_value(ea, 0)
        if target_ea == idaapi.BADADDR:
            print(f"[MicroSMT patch] Cannot resolve branch target at {ea:#x}")
            return False

        if insn_len == 2:
            # Short Jcc: 0x7x <rel8>  →  0xEB <rel8> (same displacement, same size)
            idc.patch_byte(ea, 0xEB)
            # rel8 byte at ea+1 is unchanged — target stays the same
        elif insn_len >= 5:
            # Near Jcc (6 bytes: 0F 8x xx xx xx xx) → E9 <new_rel32> + NOPs
            # JMP rel32 offset is relative to the byte after the 5-byte JMP opcode.
            new_rel = (target_ea - (ea + 5)) & 0xFFFFFFFF
            idc.patch_byte(ea, 0xE9)
            idc.patch_dword(ea + 1, new_rel)
            for i in range(5, insn_len):
                idc.patch_byte(ea + i, 0x90)  # NOP any remaining bytes
        else:
            print(f"[MicroSMT patch] Unexpected Jcc size {insn_len} at {ea:#x} — skipping")
            return False

        print(f"[MicroSMT patch] {ea:#x}: Jcc ({insn_len} bytes) → unconditional JMP "
              f"to {target_ea:#x}")

    elif cls == NEVER_TAKEN:
        for i in range(insn_len):
            idc.patch_byte(ea + i, 0x90)
        print(f"[MicroSMT patch] {ea:#x}: NOPed {insn_len} bytes (branch never taken)")

    else:
        # Not an opaque predicate — nothing to patch
        return False

    # Reanalyse the patched region so IDA updates its disassembly view.
    idaapi.plan_and_wait(ea, ea + insn_len)
    return True

def _patch_setcc(ea, cls):
    """
    Patch a SETcc instruction at `ea` to MOV r/m8, 0 or MOV r/m8, 1.
    """
    if cls not in (ALWAYS_TAKEN, NEVER_TAKEN):
        return False

    value = 1 if cls == ALWAYS_TAKEN else 0

    insn = idaapi.insn_t()
    if not idaapi.decode_insn(insn, ea):
        print(f"[MicroSMT patch] Cannot decode instruction at {ea:#x}")
        return False

    insn_len = insn.size
    raw = bytes([idc.get_wide_byte(ea + i) for i in range(insn_len)])

    # Detect optional REX prefix (0x40–0x4F)
    has_rex   = (raw[0] & 0xF0) == 0x40
    modrm_off = 3 if has_rex else 2   # position of ModRM after [REX] 0F 9x

    if modrm_off >= insn_len:
        print(f"[MicroSMT patch] Unexpected SETcc byte layout at {ea:#x}")
        return False

    modrm = raw[modrm_off]

    # Build replacement: [REX]  C6  ModRM  imm8  [padding NOPs]
    if has_rex:
        patch = [raw[0], 0xC6, modrm, value]
    else:
        patch = [0xC6, modrm, value]

    # Pad to original size (covers memory operands with SIB / displacement)
    patch += [0x90] * (insn_len - len(patch))

    if len(patch) != insn_len:
        print(f"[MicroSMT patch] Size mismatch at {ea:#x}: "
              f"built {len(patch)} bytes, expected {insn_len}")
        return False

    for i, b in enumerate(patch):
        idc.patch_byte(ea + i, b)

    print(f"[MicroSMT patch] {ea:#x}: SETcc → MOV r/m8, {value} ({insn_len} bytes)")
    idaapi.plan_and_wait(ea, ea + insn_len)
    return True

# ---------------------------------------------------------------------------

def analyze(ea=None):
    """
    Analyze the instruction at ea (or IDA cursor if None).
    """
    if ea is None:
        ea = idc.here()

    # get instruction under cursor and get its type
    insn = idaapi.insn_t()
    if not idaapi.decode_insn(insn, ea):
        err = f"Cannot decode instruction at {ea:#x}"
        _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err

    mnem = idc.print_insn_mnem(ea).lower()
    is_cond_jmp = (
        insn.itype in _COND_JMPS
        or (mnem.startswith('j') and mnem not in ('jmp', 'jmpf', 'jmpni', 'jmpshort'))
    )
    is_setcc = (
        insn.itype in _SETCC_ITYPES
        or mnem.startswith('set')
    )

    if not is_cond_jmp and not is_setcc:
        err = f"Not a conditional branch or SETcc: '{mnem}' @ {ea:#x}"
        _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err

    # Locate the containing function or derive a range for shellcode
    func = idaapi.get_func(ea)

    # Build mba_ranges_t
    try:
        hf = hr.hexrays_failure_t()
        if func is not None:
            mbr = hr.mba_ranges_t(func)
        else:
            # No function defined (e.g. shellcode): lift the containing basic block only
            blk_start, blk_end = _find_block_range(ea)
            if blk_start is None:
                err = (f"No function at {ea:#x} and cannot determine block range — try defining a function first (P key in IDA)")
                _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
                return INCONCLUSIVE, err
            mbr = hr.mba_ranges_t()
            mbr.ranges.push_back(idaapi.range_t(blk_start, blk_end))
    except Exception as exc:
        err = f"mba_ranges setup raised: {exc}"
        _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err

    # Find the corresponding microcode instruciton
    # fall back to MMAT_PREOPTIMIZED if the branch was constant-folded
    mba = block = target_insn = kind = None
    for maturity in (hr.MMAT_LOCOPT, hr.MMAT_PREOPTIMIZED):
        try:
            mba = hr.gen_microcode(mbr, hf, None, 0, maturity)
        except Exception as exc:
            err = f"gen_microcode raised: {exc}"
            _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
            return INCONCLUSIVE, err
        if mba is None:
            err = f"gen_microcode failed (errea={hf.errea:#x})"
            _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
            return INCONCLUSIVE, err

        if is_setcc:
            block, target_insn = _find_setcc_insn(mba, ea)
            kind = "setcc"
        else:
            block, target_insn = _find_jcnd_block(mba, ea)
            kind = "jcc"

        if target_insn is not None:
            break # found

    if target_insn is None:
        t = "setcc" if is_setcc else "m_jcnd"
        err = f"No {t} microcode instruction found for {ea:#x}"
        _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err

    # Lift condition to z3 
    lifter = Z3Lifter(mba, block, target_insn)
    try:
        if kind == "setcc":
            z3_cond = lifter.lift_setcc_condition(target_insn)
        else:
            z3_cond = lifter.lift_condition()
    except LiftError as exc:
        err = str(exc)
        _print_predicate_info(ea, f"<lift error: {err}>", 0, {}, False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err
    except Exception as exc:
        err = f"Unexpected error during lift: {exc}\n{traceback.format_exc()}"
        _print_predicate_info(ea, "", 0, {}, False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err

    # simplify condition 
    original_z3_cond = z3_cond
    try:
        z3_cond = _z3.simplify(z3_cond, som=True, blast_eq_value=True)
    except Exception:
        z3_cond = _z3.simplify(z3_cond)
    pred_str = str(z3_cond)

    # solve both outcomes
    try:
        taken, not_taken, cls = _solve(z3_cond)
    except Exception as exc:
        err = f"Solver error: {exc}"
        _print_predicate_info(ea, pred_str, _slice_count(block, target_insn), lifter.symbols(), False, False, INCONCLUSIVE, error=err)
        return INCONCLUSIVE, err

    _print_predicate_info(
        ea, pred_str,
        _slice_count(block, target_insn),
        lifter.symbols(),
        taken, not_taken, cls, original_z3_cond
    )

    # patch
    if PATCH_PREDICATES and cls in (ALWAYS_TAKEN, NEVER_TAKEN):
        if kind == "setcc":
            _patch_setcc(ea, cls)
        else:
            _patch_branch(ea, cls)

    return cls, None

# ---------------------------------------------------------------------------
# plugin boilerplate

def _show_config_dialog():
    """Show the MicroSMT settings dialog.  Called from Edit > Plugins."""
    global PATCH_PREDICATES
    try:
        from PySide6.QtWidgets import (QDialog, QVBoxLayout, QHBoxLayout,
                                     QCheckBox, QPushButton, QLabel, QGroupBox)
        from PySide6.QtCore import Qt
    except ImportError:
        result = idaapi.ask_yn(1 if PATCH_PREDICATES else 0,
                               "Patch opaque predicates?")
        if result in (0, 1):
            PATCH_PREDICATES = bool(result)
            idaapi.msg(f"[MicroSMT] PATCH_PREDICATES = {PATCH_PREDICATES}\n")
        return

    dlg = QDialog()
    dlg.setWindowTitle("MicroSMT — Settings")
    dlg.setMinimumWidth(360)

    layout = QVBoxLayout(dlg)
    layout.setSpacing(10)

    grp = QGroupBox("Patching")
    grp_layout = QVBoxLayout(grp)

    chk = QCheckBox("Patch opaque predicates after analysis")
    chk.setChecked(PATCH_PREDICATES)
    grp_layout.addWidget(chk)

    layout.addWidget(grp)

    btn_row = QHBoxLayout()
    btn_ok     = QPushButton("OK")
    btn_cancel = QPushButton("Cancel")
    btn_ok.setDefault(True)
    btn_row.addStretch()
    btn_row.addWidget(btn_ok)
    btn_row.addWidget(btn_cancel)
    layout.addLayout(btn_row)

    btn_ok.clicked.connect(dlg.accept)
    btn_cancel.clicked.connect(dlg.reject)

    if dlg.exec_() == QDialog.Accepted:
        PATCH_PREDICATES = chk.isChecked()
        idaapi.msg(f"[MicroSMT] PATCH_PREDICATES = {PATCH_PREDICATES}\n")

class _AnalyzeAction(idaapi.action_handler_t):
    def activate(self, ctx):
        analyze()
        return 1

    def update(self, ctx):
        return idaapi.AST_ENABLE_ALWAYS

class _MicroSMTPlugin(idaapi.plugin_t):
    flags         = idaapi.PLUGIN_PROC
    comment       = "Opaque Predicate Analyzer"
    help          = "Detect opaque predicates via Hex-Rays microcode + z3  (Alt-M to analyze)"
    wanted_name   = "MicroSMT"
    wanted_hotkey = ""         

    _ACTION_ID = "opaquesolver:analyze"

    def init(self):
        if not _HR_LOADED:
            return idaapi.PLUGIN_SKIP
        if not _Z3_LOADED:
            idaapi.msg("[MicroSMT] Warning: z3-solver not found "
                       "(pip install z3-solver)\n")

        desc = idaapi.action_desc_t(
            self._ACTION_ID,
            "MicroSMT: Analyze branch",
            _AnalyzeAction(),
            "Alt-M",
            "Analyze conditional branch / SETcc at cursor for opaque predicates",
            -1,
        )
        idaapi.register_action(desc)
        idaapi.attach_action_to_menu(
            "Edit/Plugins/",
            self._ACTION_ID,
            idaapi.SETMENU_APP,
        )

        idaapi.msg("[MicroSMT] Loaded — press Alt-M on a conditional "
                   "branch or SETcc to analyze.  Click the plugin entry to configure.\n")
        return idaapi.PLUGIN_KEEP

    def run(self, _arg):
        _show_config_dialog()

    def term(self):
        idaapi.detach_action_from_menu("Edit/Plugins/", self._ACTION_ID)
        idaapi.unregister_action(self._ACTION_ID)

def PLUGIN_ENTRY():
    return _MicroSMTPlugin()

if __name__ == "__main__":
    analyze()
