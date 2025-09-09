set_option trace.Meta.SumOfProducts true

def test (a b : Prop) := (fun x : a => b)

#check test True True

theorem myExists (a b : Prop) : ∃ (_ : a), b ↔ a ∧ b := by sorry

inductive my_prop (r : α → α → Prop) : α → Prop where
  | mk2 : my_prop r a → my_prop r a

#check my_prop.casesOn
#print my_prop.sop
#check Exists
