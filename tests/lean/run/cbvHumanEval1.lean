def IsSubseq (s₁ : String) (s₂ : String) : Prop :=
  List.Sublist s₁.toList s₂.toList

def vowels : List Char := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

def NoVowels (s : String) : Prop :=
  List.all s.toList (· ∉ vowels)

def MaximalFor [LE α] (P : ι → Prop) (f : ι → α) (x : ι) : Prop :=
  -- Same as MaximalFor in Mathlib
  P x ∧ ∀ y : ι, P y → f x ≤ f y → f y ≤ f x

def RemoveVowelsIff (solution : String → String) : Prop :=
    (s x : String) → (solution s = x) → MaximalFor (fun i => NoVowels i ∧ IsSubseq i s) (String.length) x

def removeVowels (s : String) : String :=
    String.ofList (s.toList.filter (· ∉ vowels))

example : removeVowels "abcdef" = "bcdf" := by
  conv =>
    lhs
    cbv
  rfl

example : removeVowels "abcdef\nghijklm" = "bcdf\nghjklm" := by
  conv =>
    lhs
    cbv
  rfl

example : removeVowels "aaaaa" = "" := by
  conv =>
    lhs
    cbv
  rfl

example : removeVowels "aaBAA" = "B" := by
  conv =>
    lhs
    cbv
  rfl

example : removeVowels "zbcd" = "zbcd" := by
  conv =>
    lhs
    cbv
  rfl
