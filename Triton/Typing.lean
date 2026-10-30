/-
Typing for the Triton language. Each `tl.*` name is one constructor.
The rule is the check in `python/triton/language/semantic.py`: dtype, rank,
broadcast, mask, and scalar control. The integer payload is not interpreted.
-/
import Triton.Basic

set_option autoImplicit false

namespace Triton

inductive Float1 where
  | exp | exp2 | log | log2 | cos | sin | sqrt | sqrtRn | rsqrt | erf | floor | ceil | sigmoid
  deriving DecidableEq, Repr

inductive Num1 where
  | abs | neg
  deriving DecidableEq, Repr

inductive Arith2 where
  | add | sub | mul | fdiv | divRn | umulhi | maximum | minimum | cdiv
  deriving DecidableEq, Repr

inductive Bit2 where
  | and | or | xor | shl | shr
  deriving DecidableEq, Repr

inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

inductive ReduceOp where
  | sum | max | min | xorSum | reduceOr | argmax | argmin
  deriving DecidableEq, Repr

inductive ScanOp where
  | cumsum | cumprod | associative
  deriving DecidableEq, Repr

inductive AtomicOp where
  | add | and | or | xor | max | min | xchg
  deriving DecidableEq, Repr

inductive RandOp where
  | rand | rand4x | randn | randn4x | randint | randint4x | philox | uniform | normal
  deriving DecidableEq, Repr

inductive Unary where
  | float1 (op : Float1)
  | num1 (op : Num1)
  | cast (d : DType)
  | trans
  | permute (dims : List Nat)
  | reshape (s : Shape)
  | view (s : Shape)
  | expandDims (axis : Nat)
  | sliceAxis (axis start finish : Nat)
  | ravel
  | zerosLike
  | hint
  | sort (axis : Nat)
  | topk (axis k : Nat)
  | bitonic (axis : Nat)
  | flip (axis : Nat)
  | softmax (axis : Nat)
  | split
  | reduce (op : ReduceOp) (axis : Nat) (keep : Bool)
  | scan (op : ScanOp) (axis : Nat)
  | makeBlockPtr (block : Shape)
  | makeTDesc (block : Shape)
  | load
  | histogram (bins : Nat)
  | rand (op : RandOp)
  | asm (d : DType)
  | map
  deriving DecidableEq, Repr

inductive Binary where
  | arith (op : Arith2)
  | bit (op : Bit2)
  | cmp (op : CmpOp)
  | ptrOffset
  | cat (axis : Nat)
  | join
  | interleave
  | gather
  | broadcast
  | dot
  | pair
  | advance
  | loadTDesc
  | swizzle (si sj sg : Nat)
  deriving DecidableEq, Repr

inductive Ternary where
  | fma
  | clamp
  | where_
  | loadMask
  | dotScaled
  deriving DecidableEq, Repr

inductive Expr where
  | val (v : Val)
  | var (x : Nat)
  | programId (axis : Nat)
  | numPrograms (axis : Nat)
  | arange (start finish : Nat)
  | full (s : Shape) (d : DType) (n : Int)
  | zeros (s : Shape) (d : DType)
  | unary (op : Unary) (e : Expr)
  | binary (op : Binary) (e1 e2 : Expr)
  | ternary (op : Ternary) (e1 e2 e3 : Expr)
  deriving DecidableEq, Repr

inductive Cmd where
  | skip
  | assign (x : Nat) (e : Expr)
  | seq (c1 c2 : Cmd)
  | block (body : Cmd)
  | branch (cond : Expr) (c1 c2 : Cmd)
  | loop (n : Nat) (body : Cmd)
  | store (ptr val : Expr)
  | storeMask (ptr val mask : Expr)
  | storeTDesc (desc offs val : Expr)
  | atomic (x : Nat) (op : AtomicOp) (ptr val : Expr)
  | cas (x : Nat) (ptr cmp val : Expr)
  | barrier
  | deviceAssert (cond : Expr)
  | staticAssert (cond : Expr)
  | assume (cond : Expr)
  | devicePrint (e : Expr)
  | staticPrint (e : Expr)
  deriving DecidableEq, Repr

def arithOk (op : Arith2) (d : DType) : Bool :=
  match op with
  | .add | .sub | .mul | .maximum | .minimum => isNumeric d
  | .fdiv | .divRn => isFloat d
  | .cdiv | .umulhi => isInt d

def bitOk (op : Bit2) (d : DType) : Bool :=
  match op with
  | .and | .or | .xor => isInt d || d == .bool
  | .shl | .shr => isInt d

def reduceOk (op : ReduceOp) (d : DType) : Bool :=
  match op with
  | .sum | .max | .min | .argmax | .argmin => isNumeric d
  | .xorSum | .reduceOr => true

def scanOk (op : ScanOp) (d : DType) : Bool :=
  match op with
  | .cumsum | .cumprod => isNumeric d
  | .associative => true

def randDType : RandOp → DType
  | .randint | .randint4x | .philox => .i32
  | _ => .f32

def reshapeTy (s' : Shape) : Ty → Option Ty
  | .tensor d s =>
      if numel s = numel s' ∧ numel s' ≤ maxNumel then some (.tensor d s') else none
  | _ => none

def numeric3 (a b c : Ty) : Option Ty :=
  match broadcast3 a b c with
  | some t =>
      match sameDtype t with
      | some d => if isNumeric d then some t else none
      | none => none
  | none => none

def unaryTy : Unary → Ty → Option Ty
  | .float1 _, .scalar d => if isFloat d then some (.scalar d) else none
  | .float1 _, .tensor d s => if isFloat d then some (.tensor d s) else none
  | .num1 _, .scalar d => if isNumeric d then some (.scalar d) else none
  | .num1 _, .tensor d s => if isNumeric d then some (.tensor d s) else none
  | .cast d', .scalar _ => some (.scalar d')
  | .cast d', .tensor _ s => some (.tensor d' s)
  | .trans, .tensor d s =>
      if s.length ≥ 1 then some (.tensor d s.reverse) else none
  | .permute dims, .tensor d s =>
      if isPerm s.length dims then some (.tensor d (applyPerm s dims)) else none
  | .reshape s', t => reshapeTy s' t
  | .view s', t => reshapeTy s' t
  | .expandDims axis, .tensor d s =>
      match expandShape axis s with
      | some s' => if numel s' ≤ maxNumel then some (.tensor d s') else none
      | none => none
  | .expandDims axis, .scalar d =>
      if axis = 0 then some (.tensor d [1]) else none
  | .sliceAxis axis start finish, .tensor d s =>
      match sliceDim axis start finish s with
      | some s' => some (asTensor d s')
      | none => none
  | .ravel, .tensor d s =>
      if numel s ≤ maxNumel then some (.tensor d [numel s]) else none
  | .ravel, .scalar d => some (.tensor d [1])
  | .zerosLike, .scalar d => some (.scalar d)
  | .zerosLike, .tensor d s => some (.tensor d s)
  | .hint, t =>
      match t with
      | .scalar _ | .tensor _ _ | .ptr _ | .ptrs _ _ => some t
      | _ => none
  | .sort axis, .tensor d s => if axis < s.length then some (.tensor d s) else none
  | .bitonic axis, .tensor d s => if axis < s.length then some (.tensor d s) else none
  | .flip axis, .tensor d s => if axis < s.length then some (.tensor d s) else none
  | .softmax axis, .tensor d s =>
      if axis < s.length && isFloat d then some (.tensor d s) else none
  | .topk axis k, .tensor d s =>
      match replaceAxis axis k s with
      | some s' => some (.tensor d s')
      | none => none
  | .split, .tensor d s =>
      match splitShape s with
      | some s' => some (.pair (asTensor d s') (asTensor d s'))
      | none => none
  | .reduce op axis keep, .tensor d s =>
      if reduceOk op d then
        match reduceShape keep axis s with
        | some s' =>
            match op with
            | .argmax | .argmin => some (.pair (asTensor d s') (asTensor .i32 s'))
            | _ => some (asTensor d s')
        | none => none
      else none
  | .scan op axis, .tensor d s =>
      if scanOk op d && axis < s.length then some (.tensor d s) else none
  | .makeBlockPtr b, .ptr d =>
      if numel b ≤ maxNumel then some (.blockPtr d b) else none
  | .makeTDesc b, .ptr d =>
      if numel b ≤ maxNumel then some (.tdesc d b) else none
  | .load, .ptr d => some (.scalar d)
  | .load, .ptrs d s => if numel s ≤ maxNumel then some (.tensor d s) else none
  | .load, .blockPtr d b => if numel b ≤ maxNumel then some (.tensor d b) else none
  | .histogram bins, .tensor d _ =>
      if isInt d && bins > 0 && bins ≤ maxNumel then some (.tensor .i32 [bins]) else none
  | .rand op, .scalar _ =>
      match op with
      | .philox => some (.tensor .i32 [4])
      | _ => some (.scalar (randDType op))
  | .rand op, .tensor _ s =>
      match op with
      | .philox =>
          if numel (s ++ [4]) ≤ maxNumel then some (.tensor .i32 (s ++ [4])) else none
      | _ => some (.tensor (randDType op) s)
  | .asm d, .scalar _ => some (.scalar d)
  | .asm d, .tensor _ s => some (.tensor d s)
  | .map, .scalar d => some (.scalar d)
  | .map, .tensor d s => some (.tensor d s)
  | _, _ => none

def binaryTy : Binary → Ty → Ty → Option Ty
  | .arith op, a, b =>
      match broadcastVal a b with
      | some t =>
          match sameDtype t with
          | some d => if arithOk op d then some t else none
          | none => none
      | none => none
  | .bit op, a, b =>
      match broadcastVal a b with
      | some t =>
          match sameDtype t with
          | some d => if bitOk op d then some t else none
          | none => none
      | none => none
  | .cmp _, a, b =>
      match broadcastVal a b with
      | some (.scalar _) => some (.scalar .bool)
      | some (.tensor _ s) => some (.tensor .bool s)
      | _ => none
  | .ptrOffset, .ptr d, .tensor .i32 s =>
      if numel s ≤ maxNumel then some (.ptrs d s) else none
  | .ptrOffset, .ptr d, .scalar .i32 => some (.ptr d)
  | .ptrOffset, .ptrs d s1, .tensor .i32 s2 =>
      match broadcastShape s1 s2 with
      | some s => if s = s1 && numel s ≤ maxNumel then some (.ptrs d s) else none
      | none => none
  | .cat axis, .tensor d1 s1, .tensor d2 s2 =>
      if d1 = d2 then
        match catShape axis s1 s2 with
        | some s => if numel s ≤ maxNumel then some (.tensor d1 s) else none
        | none => none
      else none
  | .join, .tensor d1 s1, .tensor d2 s2 =>
      if d1 = d2 && s1 = s2 && numel (s1 ++ [2]) ≤ maxNumel then
        some (.tensor d1 (s1 ++ [2]))
      else none
  | .join, .scalar d1, .scalar d2 =>
      if d1 = d2 then some (.tensor d1 [2]) else none
  | .interleave, .tensor d1 s1, .tensor d2 s2 =>
      if d1 = d2 && s1 = s2 then
        match doubleLast s1 with
        | some s => if numel s ≤ maxNumel then some (.tensor d1 s) else none
        | none => none
      else none
  | .gather, .tensor d _, .tensor .i32 si =>
      if numel si ≤ maxNumel then some (.tensor d si) else none
  | .broadcast, a, b =>
      match sameDtype a, sameDtype b with
      | some d1, some d2 =>
          if d1 = d2 then
            match broadcastShape (shapeOf a) (shapeOf b) with
            | some s =>
                if s = shapeOf b then some (asTensor d1 s) else none
            | none => none
          else none
      | _, _ => none
  | .dot, .tensor d1 [m, k], .tensor d2 [k2, n] =>
      if d1 = d2 && k = k2 && isNumeric d1 && numel [m, n] ≤ maxNumel then
        some (.tensor d1 [m, n])
      else none
  | .pair, a, b => some (.pair a b)
  | .advance, .blockPtr d b, .tensor .i32 s =>
      if s = [b.length] then some (.blockPtr d b) else none
  | .advance, .tdesc d b, .tensor .i32 s =>
      if s = [b.length] then some (.tdesc d b) else none
  | .loadTDesc, .tdesc d b, .tensor .i32 s =>
      if s = [b.length] && numel b ≤ maxNumel then some (.tensor d b) else none
  | .swizzle _ _ _, .scalar .i32, .scalar .i32 => some (.scalar .i32)
  | _, _, _ => none

def maskOk (result mask : Ty) : Option Unit :=
  match result, mask with
  | .scalar _, .scalar .bool => some ()
  | .tensor _ _, .scalar .bool => some ()
  | .tensor _ s, .tensor .bool sm =>
      match broadcastShape sm s with
      | some s' => if s' = s then some () else none
      | none => none
  | _, _ => none

def otherOk (result other : Ty) : Option Unit :=
  match broadcastVal result other with
  | some t => if t = result then some () else none
  | none => none

def loadResult : Ty → Option Ty
  | .ptr d => some (.scalar d)
  | .ptrs d s => if numel s ≤ maxNumel then some (.tensor d s) else none
  | .blockPtr d b => if numel b ≤ maxNumel then some (.tensor d b) else none
  | _ => none

def ternaryTy : Ternary → Ty → Ty → Ty → Option Ty
  | .fma, a, b, c => numeric3 a b c
  | .clamp, a, b, c => numeric3 a b c
  | .where_, c, x, y =>
      match broadcastVal x y with
      | none => none
      | some tv =>
          match c with
          | .scalar .bool => some tv
          | .tensor .bool sc =>
              match broadcastShape sc (shapeOf tv) with
              | some s => some (asTensor (match sameDtype tv with | some d => d | none => .bool) s)
              | none => none
          | _ => none
  | .loadMask, p, m, o =>
      match loadResult p with
      | some r =>
          match maskOk r m, otherOk r o with
          | some _, some _ => some r
          | _, _ => none
      | none => none
  | .dotScaled, .tensor d1 [m, k], .tensor d2 [k2, n], .pair s1 s2 =>
      if d1 = d2 && k = k2 && isNumeric d1 && numel [m, n] ≤ maxNumel then
        match s1, s2 with
        | .tensor _ _, .tensor _ _ => some (.tensor d1 [m, n])
        | _, _ => none
      else none
  | _, _, _, _ => none

def storeOk : Ty → Ty → Option Unit
  | .ptr d, .scalar d2 => if d = d2 then some () else none
  | .ptrs d s, .tensor d2 s2 =>
      if d = d2 then
        match broadcastShape s2 s with
        | some s' => if s' = s then some () else none
        | none => none
      else none
  | .ptrs d _, .scalar d2 => if d = d2 then some () else none
  | .blockPtr d b, .tensor d2 s => if d = d2 && s = b then some () else none
  | .tdesc d b, .tensor d2 s => if d = d2 && s = b then some () else none
  | _, _ => none

def atomicResult : Ty → Option Ty
  | .ptr d => some (.scalar d)
  | .ptrs d s => some (.tensor d s)
  | _ => none

def infer (Γ : Ctx) : Expr → Option Ty
  | .val v => some (valTy v)
  | .var x => lookup Γ x
  | .programId axis => if axis < 3 then some (.scalar .i32) else none
  | .numPrograms axis => if axis < 3 then some (.scalar .i32) else none
  | .arange start finish =>
      if start ≤ finish ∧ numel [finish - start] ≤ maxNumel then
        some (.tensor .i32 [finish - start])
      else none
  | .full s d _ => if numel s ≤ maxNumel then some (.tensor d s) else none
  | .zeros s d => if numel s ≤ maxNumel then some (.tensor d s) else none
  | .unary op e =>
      match infer Γ e with
      | some t => unaryTy op t
      | none => none
  | .binary op e1 e2 =>
      match infer Γ e1, infer Γ e2 with
      | some t1, some t2 => binaryTy op t1 t2
      | _, _ => none
  | .ternary op e1 e2 e3 =>
      match infer Γ e1, infer Γ e2, infer Γ e3 with
      | some t1, some t2, some t3 => ternaryTy op t1 t2 t3
      | _, _, _ => none

def check (Γ : Ctx) : Cmd → Option Ctx
  | .skip => some Γ
  | .assign x e =>
      match infer Γ e with
      | some τ => some (update Γ x τ)
      | none => none
  | .seq c1 c2 =>
      match check Γ c1 with
      | some Γ1 => check Γ1 c2
      | none => none
  | .block body => check Γ body
  | .branch cond c1 c2 =>
      match infer Γ cond, check Γ c1, check Γ c2 with
      | some (.scalar .bool), some Γ1, some Γ2 => if Γ1 = Γ2 then some Γ1 else none
      | _, _, _ => none
  | .loop _ body =>
      match check Γ body with
      | some Γ' => if Γ' = Γ then some Γ else none
      | none => none
  | .store p v =>
      match infer Γ p, infer Γ v with
      | some tp, some tv =>
          match storeOk tp tv with
          | some _ => some Γ
          | none => none
      | _, _ => none
  | .storeMask p v m =>
      match infer Γ p, infer Γ v, infer Γ m with
      | some tp, some tv, some tm =>
          match storeOk tp tv, loadResult tp with
          | some _, some r =>
              match maskOk r tm with
              | some _ => some Γ
              | none => none
          | _, _ => none
      | _, _, _ => none
  | .storeTDesc desc offs val =>
      match infer Γ desc, infer Γ offs, infer Γ val with
      | some (.tdesc d b), some (.tensor .i32 s), some tv =>
          if s = [b.length] then
            match storeOk (.tdesc d b) tv with
            | some _ => some Γ
            | none => none
          else none
      | _, _, _ => none
  | .atomic x _ p v =>
      match infer Γ p, infer Γ v with
      | some tp, some tv =>
          match storeOk tp tv, atomicResult tp with
          | some _, some tr => some (update Γ x tr)
          | _, _ => none
      | _, _ => none
  | .cas x p cmp v =>
      match infer Γ p, infer Γ cmp, infer Γ v with
      | some tp, some tc, some tv =>
          match atomicResult tp with
          | some tr => if tc = tr ∧ tv = tr then some (update Γ x tr) else none
          | none => none
      | _, _, _ => none
  | .barrier => some Γ
  | .deviceAssert c =>
      match infer Γ c with
      | some (.scalar .bool) => some Γ
      | _ => none
  | .staticAssert c =>
      match infer Γ c with
      | some (.scalar .bool) => some Γ
      | _ => none
  | .assume c =>
      match infer Γ c with
      | some (.scalar .bool) => some Γ
      | _ => none
  | .devicePrint e =>
      match infer Γ e with
      | some _ => some Γ
      | none => none
  | .staticPrint e =>
      match infer Γ e with
      | some _ => some Γ
      | none => none

end Triton
