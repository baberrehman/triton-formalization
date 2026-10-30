"""Run the checkers the Lean development is linked to.

`scope_check.py` is the TLA birth-core walk. `semantic.py` is the `tl.*`
dtype and shape checker. The verdicts below are the ones proved in
`TAS/ScopeLink.lean` and `Triton/Examples.lean`, including the two places
the Python checker and the calculus differ.
"""

import ast
import importlib.util
import os
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
ASCEND = ROOT / "triton-ascend"
sys.path.insert(0, str(ASCEND / "python"))
os.environ.setdefault("TORCH_DEVICE_BACKEND_AUTOLOAD", "0")

_SCOPE = ASCEND / "third_party" / "ascend" / "language" / "tla" / "scope_check.py"
_spec = importlib.util.spec_from_file_location("tla_scope_check", _SCOPE)
_scope = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_scope)
check_scope_body = _scope.check_scope_body


def scope_accepts(src):
    tree = ast.parse(src)
    try:
        check_scope_body(tree.body[0].body, None, {})
    except ValueError:
        return False
    return True


class ScopeCheckLink(unittest.TestCase):
    """Same programs as `TAS/Examples.lean` and `scalarInside`."""

    def test_gemm_bias_accepted(self):
        src = """
def kernel():
    with tla.scope.cube():
        tla.copy(a_gm, a_l1)
        tla.copy(b_gm, b_l1)
        tla.cube.mmad(a_l1, b_l1, c_l0c)
        tla.copy(c_l0c, c_ub)
    with tla.scope.simd():
        bias = tla.splat(1)
        vreg = c_ub
        tla.store(c_ub, vreg, bias)
    tla.copy(c_ub, c_gm)
"""
        self.assertTrue(scope_accepts(src))

    def test_cross_scope_rejected(self):
        src = """
def kernel():
    with tla.scope.cube():
        bias = tla.splat(0)
    with tla.scope.simd():
        tla.store(c_ub, bias)
"""
        self.assertFalse(scope_accepts(src))

    def test_rebound_accepted(self):
        src = """
def kernel():
    with tla.scope.cube():
        bias = tla.splat(0)
    with tla.scope.simd():
        bias = tla.splat(1)
"""
        self.assertTrue(scope_accepts(src))

    def test_scalar_both_accepted(self):
        src = """
def kernel():
    bias = 3
    with tla.scope.cube():
        a_gm = bias + 1
    with tla.scope.simd():
        vreg = bias + 2
"""
        self.assertTrue(scope_accepts(src))

    def test_nested_cross_rejected(self):
        src = """
def kernel():
    with tla.scope.simd():
        vreg = tla.splat(1)
        with tla.scope.cube():
            bias = vreg
"""
        self.assertFalse(scope_accepts(src))

    def test_scalar_inside_rejected_by_scope_check(self):
        """TAS accepts this. `scope_check.py` rejects it. See `scalar_inside_tas_accepted`."""
        src = """
def kernel():
    with tla.scope.cube():
        bias = 1
    with tla.scope.simd():
        vreg = bias
"""
        self.assertFalse(scope_accepts(src))


def _semantic():
    from triton._C.libtriton import ir
    from triton.language.semantic import TritonSemantic

    ctx = ir.context()
    ir.load_dialects(ctx)
    builder = ir.builder(ctx)

    class Options:
        default_dot_input_precision = "ieee"
        allowed_dot_input_precisions = ("ieee", "hf32")
        deprecated_fp8_dot_operand_dtypes = ()
        arch = "ascend"
        sanitize_overflow = False

    builder.options = Options()
    builder.codegen_fns = {"min_dot_size": lambda _lhs, _rhs: (1, 1, 1)}
    sem = TritonSemantic(builder)
    # The builder borrows the context. Dropping `ctx` frees it and the next op segfaults.
    sem._ctx = ctx
    return sem


def _verdict(fn):
    try:
        fn()
    except (ValueError, AssertionError):
        return False
    return True


class SemanticLink(unittest.TestCase):
    """Calls `TritonSemantic` in `python/triton/language/semantic.py`."""

    def test_program_id_matches_calculus(self):
        import triton.language as tl
        sem = _semantic()
        accepted = sem.program_id(0)
        self.assertEqual(accepted.dtype, tl.int32)
        self.assertEqual(tuple(accepted.shape), ())
        self.assertFalse(_verdict(lambda: sem.program_id(3)))

    def test_dot_matches_calculus(self):
        import triton.language as tl
        sem = _semantic()
        lhs = sem.full([32, 16], 0, tl.float32)
        bad = sem.full([32, 16], 0, tl.float32)
        good = sem.full([16, 8], 0, tl.float32)
        self.assertFalse(_verdict(lambda: sem.dot(lhs, bad, None, None, 0, tl.float32)))
        out = sem.dot(lhs, good, None, None, 0, tl.float32)
        self.assertEqual(out.dtype, tl.float32)
        self.assertEqual([int(s) for s in out.shape], [32, 8])

    def test_arange_power_of_two_is_stricter_than_calculus(self):
        """`arange(0, 128)` is accepted by both. `arange(0, 3)` is accepted by Lean and rejected here."""
        import triton.language as tl
        sem = _semantic()
        accepted = sem.arange(0, 128)
        self.assertEqual(accepted.dtype, tl.int32)
        self.assertEqual([int(s) for s in accepted.shape], [128])
        self.assertFalse(_verdict(lambda: sem.arange(0, 3)))

    def test_load_f32_mask_is_accepted_by_semantic_py(self):
        """Lean `bad_mask_rejected` refuses an f32 mask. `semantic.load` does not."""
        import triton.language as tl
        sem = _semantic()
        builder = sem.builder
        offs = sem.arange(0, 128)
        ptr_ty = tl.pointer_type(tl.float32)
        scalar_ptr = tl.tensor(builder.create_int_to_ptr(builder.get_int64(0), ptr_ty.to_ir(builder)), ptr_ty)
        block_ty = tl.block_type(ptr_ty, [128])
        ptrs = tl.tensor(builder.create_splat(block_ty.to_ir(builder), scalar_ptr.handle), block_ty)
        ptrs = tl.tensor(builder.create_addptr(ptrs.handle, offs.handle), block_ty)
        mask = sem.full([128], 1, tl.float32)
        other = sem.full([128], 0, tl.float32)
        loaded = sem.load(ptrs, mask, other, (), "", "", "", False)
        self.assertEqual(loaded.dtype, tl.float32)
        self.assertEqual([int(s) for s in loaded.shape], [128])


if __name__ == "__main__":
    unittest.main()
