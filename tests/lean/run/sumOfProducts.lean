

inductive my_prop (r : α → α → Prop) : α → Prop where
  | mk2 : my_prop r a → r a b → my_prop r b

#check my_prop.casesOn

#check my_prop.sop

#check Exists
