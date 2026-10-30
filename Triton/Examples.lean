import Triton.Typing

/-
A vector add, the programs the dtype and shape rules reject, and a loop that
may only reassign a name already in scope.
-/
set_option autoImplicit false

namespace Triton

def xPtr : Nat := 0
def yPtr : Nat := 1
def offs : Nat := 2
def xv : Nat := 3

def params : Ctx := [
  (xPtr, .ptr .f32),
  (yPtr, .ptr .f32)
]

def vecAdd : Cmd :=
  .seq (.assign offs (.arange 0 128)) <|
  .seq (.assign xv (.unary .load (.binary .ptrOffset (.var xPtr) (.var offs)))) <|
  .store
    (.binary .ptrOffset (.var yPtr) (.var offs))
    (.binary (.arith .add) (.var xv) (.full [128] .f32 1))

def badMask : Expr :=
  .ternary .loadMask
    (.binary .ptrOffset (.var xPtr) (.arange 0 128))
    (.full [128] .f32 1)
    (.full [128] .f32 0)

def tensorIf : Cmd :=
  .branch (.arange 0 4) .skip .skip

def withOffs : Ctx :=
  (offs, .tensor .i32 [128]) :: params

theorem vec_add_typed : (check params vecAdd).isSome = true := by
  native_decide

theorem bad_mask_rejected : infer params badMask = none := by
  native_decide

theorem tensor_if_rejected : check params tensorIf = none := by
  native_decide

theorem dot_rejected :
    infer [] (.binary .dot (.full [32, 16] .f32 0) (.full [32, 16] .f32 0)) = none := by
  native_decide

theorem dot_typed :
    infer [] (.binary .dot (.full [32, 16] .f32 0) (.full [16, 8] .f32 0)) =
      some (.tensor .f32 [32, 8]) := by
  native_decide

theorem program_id_typed : infer [] (.programId 0) = some (.scalar .i32) := by
  native_decide

theorem program_id_rejected : infer [] (.programId 3) = none := by
  native_decide

theorem loop_skip_typed : check params (.loop 4 .skip) = some params := by
  native_decide

theorem loop_fresh_rejected :
    check params (.loop 4 (.assign offs (.arange 0 128))) = none := by
  native_decide

theorem loop_reassign_typed :
    (check withOffs (.loop 4 (.assign offs (.arange 0 128)))).isSome = true := by
  native_decide

/-- `semantic.py` rejects this range because it is not a power of two. The calculus accepts it. -/
theorem arange_non_pow2_typed :
    infer [] (.arange 0 3) = some (.tensor .i32 [3]) := by
  native_decide

end Triton
