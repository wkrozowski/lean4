inductive myNat where
| myZero : myNat
| mySucc : myNat → myNat

inductive myVec : myNat → Type where
| myVNil : myVec myNat.myZero
| myVCons : ∀ {n : myNat}, myNat → myVec n → myVec (myNat.mySucc n)

def myVec.size {n : myNat} (_ : myVec n) : myNat := n

def myFun (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ n => (myFun n).succ.succ
termination_by n

def myFun2 (n m : Nat) :=
  match n with
  | .zero => m
  | .succ n => myFun2 n m.succ

def myFun3 (n : myNat) : myNat :=
  match n with
  | myNat.myZero => myNat.myZero
  | myNat.mySucc n => myNat.mySucc (myNat.mySucc (myFun3 n))

def myInc (n : myNat) : myNat := myNat.mySucc n

#check myFun2.eq_2

def isSuc (n : Nat) : Bool :=
  match n with
  | .zero => false
  | .succ _ => true

def vecFun (n : Nat) (v : Vector Nat n) : Nat := match n with
| 0 => v.size + n
| Nat.succ m => vecFun m (v.tail) + n

#check ite.eq_1

def t : Nat → Nat := fun x => .zero

set_option trace.Meta.Tactic true

def broken (n : Nat) : Nat → Nat := match n with
| 0 => fun x => match x with
                | 0 => 0
                | n + 1 => n
| n + 1 => fun x => x + n

#check broken.eq_unfold


theorem myTest : (fun x => x) 1 = 1  := by
  conv =>
    lhs
    cbv



-- theorem test : "h" ++ "" = "h" := by
--   conv =>
--     lhs
--     cbv
--     dsimp
--     cbv
--     cbv
--     dsimp
--     cbv
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp
--     cbv
--     dsimp

def ident := String deriving BEq, Repr, Hashable

inductive aexp : Type where
  | CONST (n : Int)               -- a constant, or
  | VAR (x : ident)               -- a variable, or
  | PLUS (a1 : aexp) (a2 : aexp)  -- a sum of two expressions, or
  | MINUS (a1 : aexp) (s2 : aexp) -- a difference of two expressions


def store : Type := ident → Int

def mymeasure (a : aexp) : Nat :=
   match a with
  | .CONST n => 1
  | .VAR x => 1
  | .PLUS a1 a2 => mymeasure a1 + mymeasure a2 + 1
  | .MINUS a1 a2 => mymeasure a1 + mymeasure a2 + 1

def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2
    termination_by (mymeasure a)
    decreasing_by
    all_goals grind [mymeasure]

theorem leroy1 : aeval (λ _ => 2) (.PLUS (.VAR "x") (.MINUS (.VAR "x") (.CONST 1))) = 3 := by simp [aeval]

#print leroy1
