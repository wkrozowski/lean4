set_option trace.Meta.Tactic true

def myId (n : myNat) : myNat := n

def natFun (n : Nat) : Nat := match n with
  | 0 => 0
  | n + 1 => (natFun n).succ


def test (b : Bool) : Bool := match b,(!b) with
| true, true => false
| false, true => false
| true, false => false
| false, false => true

#check test.match_1.congr_eq_4

theorem myTest0 : 2 * 2 = 4 := by
  conv =>
    lhs
    cbv

def ident := String deriving BEq, Repr, Hashable

/-
  The abstract syntax: an arithmetic expression is either...
-/
inductive aexp : Type where
  | CONST (n : Int)               -- a constant, or
  | VAR (x : ident)               -- a variable, or
  | PLUS (a1 : aexp) (a2 : aexp)  -- a sum of two expressions, or
  | MINUS (a1 : aexp) (s2 : aexp) -- a difference of two expressions

/-
  The denotational semantics: an evaluation function that computes the integer value denoted by an expression.  It is parameterized by a store [s] that associates values to variables.
-/

def store : Type := ident → Int

@[grind] def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2

inductive bexp : Type where
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1 : aexp) (a2 : aexp)     -- whether [a1=a]
  | LESSEQUAL (a1 : aexp) (a2 : aexp) -- whether [a1≤a]
  | NOT (b1 : bexp)                   -- Boolean negation
  | AND (b1 : bexp) (b2 : bexp)       -- Boolean conjunction

@[grind] def beval (s : store) (b : bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

inductive com : Type where
  | SKIP                                        -- do nothing
  | ASSIGN (x : ident) (a : aexp)               -- assignment: [v := a]
  | SEQ (c1 : com) (c2 : com)                   -- sequence: [c1; c2]
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com) -- conditional: [if b then c1 else c2]
  | WHILE (b : bexp) (c1 : com)                 -- loop: [while b do c1 done]

@[grind] def update (x : ident) (v : Int) (s : store) : store :=
  fun y => if x == y then v else s y

@[grind] def cexec_bounded (fuel : Nat) (s : store) (c : com) : Option store :=
  match fuel with
  | .zero => .none
  | .succ fuel' =>
    match c with
    | .SKIP => .some s
    | .ASSIGN x a => .some (update x (aeval s a) s)
    | .SEQ c1 c2 =>
      match cexec_bounded fuel' s c1 with
      | .none => .none
      | .some s' => cexec_bounded fuel' s' c2
    | .IFTHENELSE b c1 c2 =>
      if beval s b then cexec_bounded fuel' s c1 else cexec_bounded fuel' s c2
    | .WHILE b c1 =>
      if beval s b then
        match cexec_bounded fuel' s c1 with
        | .none => .none
        | .some s' => cexec_bounded fuel' s' (.WHILE b c1)
      else
        .some s

/- Violates an assertion -/
theorem cexec1 : cexec_bounded 1 (fun _ => 0) (.SKIP) = sorry := by
  conv =>
    lhs
    cbv
  sorry
