/-
Small-step semantics. A value redex packs a result of the type `unaryTy` /
`binaryTy` / `ternaryTy` already computed. Child expressions step first.
-/
import Triton.Typing

set_option autoImplicit false

namespace Triton

def evalUnary (op : Unary) (v : Val) : Option Val :=
  match unaryTy op (valTy v) with
  | some t => some (pack t (payload v))
  | none => none

def evalBinary (op : Binary) (v1 v2 : Val) : Option Val :=
  match binaryTy op (valTy v1) (valTy v2) with
  | some t => some (pack t (payload v1 + payload v2))
  | none => none

def evalTernary (op : Ternary) (v1 v2 v3 : Val) : Option Val :=
  match ternaryTy op (valTy v1) (valTy v2) (valTy v3) with
  | some t => some (pack t (payload v1 + payload v2 + payload v3))
  | none => none

def stepE (cfg : Cfg) (env : Env) : Expr → Option Expr
  | .val _ => none
  | .var x =>
      match lookup env x with
      | some v => some (.val v)
      | none => none
  | .programId axis =>
      if axis < 3 then some (.val (.scalar .i32 (Int.ofNat (pid cfg axis)))) else none
  | .numPrograms axis =>
      if axis < 3 then some (.val (.scalar .i32 (Int.ofNat (nprog cfg axis)))) else none
  | .arange start finish =>
      if start ≤ finish ∧ numel [finish - start] ≤ maxNumel then
        some (.val (.tensor .i32 [finish - start] 0))
      else none
  | .full s d n =>
      if numel s ≤ maxNumel then some (.val (.tensor d s n)) else none
  | .zeros s d =>
      if numel s ≤ maxNumel then some (.val (.tensor d s 0)) else none
  | .unary op e =>
      match e with
      | .val v =>
          match evalUnary op v with
          | some w => some (.val w)
          | none => none
      | _ =>
          match stepE cfg env e with
          | some e' => some (.unary op e')
          | none => none
  | .binary op e1 e2 =>
      match e1, e2 with
      | .val v1, .val v2 =>
          match evalBinary op v1 v2 with
          | some w => some (.val w)
          | none => none
      | .val _, _ =>
          match stepE cfg env e2 with
          | some e2' => some (.binary op e1 e2')
          | none => none
      | _, _ =>
          match stepE cfg env e1 with
          | some e1' => some (.binary op e1' e2)
          | none => none
  | .ternary op e1 e2 e3 =>
      match e1, e2, e3 with
      | .val v1, .val v2, .val v3 =>
          match evalTernary op v1 v2 v3 with
          | some w => some (.val w)
          | none => none
      | .val _, .val _, _ =>
          match stepE cfg env e3 with
          | some e3' => some (.ternary op e1 e2 e3')
          | none => none
      | .val _, _, _ =>
          match stepE cfg env e2 with
          | some e2' => some (.ternary op e1 e2' e3)
          | none => none
      | _, _, _ =>
          match stepE cfg env e1 with
          | some e1' => some (.ternary op e1' e2 e3)
          | none => none

def stepBool (v : Val) : Option Bool :=
  match v with
  | .scalar .bool n => some (n ≠ 0)
  | _ => none

def step (cfg : Cfg) (env : Env) : Cmd → Option (Env × Cmd)
  | .skip => none
  | .assign x e =>
      match e with
      | .val v => some ((x, v) :: env, .skip)
      | _ =>
          match stepE cfg env e with
          | some e' => some (env, .assign x e')
          | none => none
  | .seq c1 c2 =>
      match c1 with
      | .skip => some (env, c2)
      | _ =>
          match step cfg env c1 with
          | some (env', c1') => some (env', .seq c1' c2)
          | none => none
  | .block body =>
      match body with
      | .skip => some (env, .skip)
      | _ =>
          match step cfg env body with
          | some (env', body') => some (env', .block body')
          | none => none
  | .branch cond c1 c2 =>
      match cond with
      | .val v =>
          match stepBool v with
          | some true => some (env, c1)
          | some false => some (env, c2)
          | none => none
      | _ =>
          match stepE cfg env cond with
          | some cond' => some (env, .branch cond' c1 c2)
          | none => none
  | .loop n body =>
      match n with
      | 0 => some (env, .skip)
      | Nat.succ n' => some (env, .seq body (.loop n' body))
  | .store p v =>
      match p, v with
      | .val vp, .val vv =>
          match storeOk (valTy vp) (valTy vv) with
          | some _ => some (env, .skip)
          | none => none
      | .val _, _ =>
          match stepE cfg env v with
          | some v' => some (env, .store p v')
          | none => none
      | _, _ =>
          match stepE cfg env p with
          | some p' => some (env, .store p' v)
          | none => none
  | .storeMask p v m =>
      match p, v, m with
      | .val vp, .val vv, .val vm =>
          match storeOk (valTy vp) (valTy vv), loadResult (valTy vp) with
          | some _, some r =>
              match maskOk r (valTy vm) with
              | some _ => some (env, .skip)
              | none => none
          | _, _ => none
      | .val _, .val _, _ =>
          match stepE cfg env m with
          | some m' => some (env, .storeMask p v m')
          | none => none
      | .val _, _, _ =>
          match stepE cfg env v with
          | some v' => some (env, .storeMask p v' m)
          | none => none
      | _, _, _ =>
          match stepE cfg env p with
          | some p' => some (env, .storeMask p' v m)
          | none => none
  | .storeTDesc d offs val =>
      match d, offs, val with
      | .val vd, .val vo, .val vv =>
          match valTy vd, valTy vo, storeOk (valTy vd) (valTy vv) with
          | .tdesc _ b, .tensor .i32 s, some _ =>
              if s = [b.length] then some (env, .skip) else none
          | _, _, _ => none
      | .val _, .val _, _ =>
          match stepE cfg env val with
          | some val' => some (env, .storeTDesc d offs val')
          | none => none
      | .val _, _, _ =>
          match stepE cfg env offs with
          | some offs' => some (env, .storeTDesc d offs' val)
          | none => none
      | _, _, _ =>
          match stepE cfg env d with
          | some d' => some (env, .storeTDesc d' offs val)
          | none => none
  | .atomic x op p v =>
      match p, v with
      | .val vp, .val vv =>
          match storeOk (valTy vp) (valTy vv), atomicResult (valTy vp) with
          | some _, some tr => some ((x, pack tr (payload vp)) :: env, .skip)
          | _, _ => none
      | .val _, _ =>
          match stepE cfg env v with
          | some v' => some (env, .atomic x op p v')
          | none => none
      | _, _ =>
          match stepE cfg env p with
          | some p' => some (env, .atomic x op p' v)
          | none => none
  | .cas x p cmp v =>
      match p, cmp, v with
      | .val vp, .val vc, .val vv =>
          match atomicResult (valTy vp) with
          | some tr =>
              if valTy vc = tr ∧ valTy vv = tr then
                some ((x, pack tr (payload vc)) :: env, .skip)
              else none
          | none => none
      | .val _, .val _, _ =>
          match stepE cfg env v with
          | some v' => some (env, .cas x p cmp v')
          | none => none
      | .val _, _, _ =>
          match stepE cfg env cmp with
          | some cmp' => some (env, .cas x p cmp' v)
          | none => none
      | _, _, _ =>
          match stepE cfg env p with
          | some p' => some (env, .cas x p' cmp v)
          | none => none
  | .barrier => some (env, .skip)
  | .deviceAssert c => stepAssert cfg env .deviceAssert c
  | .staticAssert c => stepAssert cfg env .staticAssert c
  | .assume c => stepAssert cfg env .assume c
  | .devicePrint e => stepPrint cfg env .devicePrint e
  | .staticPrint e => stepPrint cfg env .staticPrint e

where
  stepAssert (cfg : Cfg) (env : Env) (wrap : Expr → Cmd) (c : Expr) : Option (Env × Cmd) :=
    match c with
    | .val v =>
        match v with
        | .scalar .bool _ => some (env, .skip)
        | _ => none
    | _ =>
        match stepE cfg env c with
        | some c' => some (env, wrap c')
        | none => none
  stepPrint (cfg : Cfg) (env : Env) (wrap : Expr → Cmd) (e : Expr) : Option (Env × Cmd) :=
    match e with
    | .val _ => some (env, .skip)
    | _ =>
        match stepE cfg env e with
        | some e' => some (env, wrap e')
        | none => none

/-- Reachable in zero or more steps of one program. `cfg` stays fixed. -/
inductive Steps (cfg : Cfg) : Env → Cmd → Env → Cmd → Prop where
  | refl (env : Env) (c : Cmd) : Steps cfg env c env c
  | tail (env : Env) (c : Cmd) (env1 : Env) (c1 : Cmd) (env2 : Env) (c2 : Cmd) :
      step cfg env c = some (env1, c1) →
      Steps cfg env1 c1 env2 c2 →
      Steps cfg env c env2 c2

end Triton
