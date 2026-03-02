module

-- Case 1: p is literally True/False
example : decide True = true := by cbv
example : decide False = false := by cbv

-- Case 2: p simplifies to True/False
example : decide (1 < 2) = true := by cbv
example : decide (3 < 2) = false := by cbv

-- Case 3: instance reduces to isTrue/isFalse
example : decide (1 = 1) = true := by cbv
example : decide (1 = 2) = false := by cbv

-- Case 4: compound propositions
example : decide (10 + 5 = 15) = true := by cbv

-- Case 5: decide used in a larger expression
example : (decide (1 < 2), decide (3 < 2)) = (true, false) := by cbv
