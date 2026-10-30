import TAS.Step

/-
The mixed kernel in `unittest/tla_ut/cube/gemm_bias.py`, cut down to one cell
per buffer, and the cross-scope program the checker rejects.
-/
set_option autoImplicit false

namespace TAS

def aGm : Nat := 0
def aL1 : Nat := 1
def bGm : Nat := 2
def bL1 : Nat := 3
def cL0c : Nat := 4
def cUb : Nat := 5
def bias : Nat := 6
def vreg : Nat := 7
def cGm : Nat := 8

def gemmCtx : Ctx := [
  (aGm, .buf .gm),
  (aL1, .buf .l1),
  (bGm, .buf .gm),
  (bL1, .buf .l1),
  (cL0c, .buf .l0c),
  (cUb, .buf .ub),
  (cGm, .buf .gm)
]

def cubeBody : Cmd :=
  .seq (.copy aGm aL1) <|
  .seq (.copy bGm bL1) <|
  .seq (.mmad aL1 bL1 cL0c)
       (.copy cL0c cUb)

def vecBody : Cmd :=
  .seq (.assign bias (.splat (.val (.scalar 1)))) <|
  .seq (.assign vreg (.vld (.var cUb)))
       (.vst cUb (.vadd (.var vreg) (.var bias)))

/-- `C = A @ B`, then a vector add of a splat into the UB cell, then UB → GM. -/
def gemmBias : Cmd :=
  .seq (.scope .cube cubeBody) <|
  .seq (.scope .vec vecBody)
       (.copy cUb cGm)

/-- A name bound by `splat` inside cube is a cube register. Vector code cannot read it. -/
def crossScope : Cmd :=
  .seq (.scope .cube (.assign bias (.splat (.val (.scalar 0)))))
       (.scope .vec (.vst cUb (.var bias)))

/-- Binding the same name again inside vector drops the cube register type. -/
def rebound : Cmd :=
  .seq (.scope .cube (.assign bias (.splat (.val (.scalar 0)))))
       (.scope .vec (.assign bias (.splat (.val (.scalar 1)))))

/-- A scalar bound outside both cores is readable in each. -/
def scalarBoth : Cmd :=
  .seq (.assign bias (.val (.scalar 3))) <|
  .seq (.scope .cube (.assign aGm (.add (.var bias) (.val (.scalar 1)))))
       (.scope .vec (.assign vreg (.add (.var bias) (.val (.scalar 2)))))

/-- A register born in the outer vector core is not readable in the inner cube core. -/
def nestedCross : Cmd :=
  .scope .vec <|
    .seq (.assign vreg (.splat (.val (.scalar 1))))
         (.scope .cube (.assign bias (.var vreg)))

theorem gemm_bias_typed : (check none gemmCtx gemmBias).isSome = true := by
  native_decide

theorem cross_scope_rejected : check none gemmCtx crossScope = none := by
  native_decide

theorem rebound_typed : (check none gemmCtx rebound).isSome = true := by
  native_decide

theorem scalar_both_typed : (check none [] scalarBoth).isSome = true := by
  native_decide

theorem nested_cross_rejected : check none [] nestedCross = none := by
  native_decide

def gemmEnv : Env := [
  (aGm, .buf .gm 0),
  (aL1, .buf .l1 0),
  (bGm, .buf .gm 0),
  (bL1, .buf .l1 0),
  (cL0c, .buf .l0c 0),
  (cUb, .buf .ub 0),
  (cGm, .buf .gm 0)
]

theorem gemm_bias_steps_into_cube :
    step none gemmEnv gemmBias =
      some (gemmEnv, .seq (.block .cube cubeBody) (.seq (.scope .vec vecBody) (.copy cUb cGm))) := by
  rfl

end TAS
