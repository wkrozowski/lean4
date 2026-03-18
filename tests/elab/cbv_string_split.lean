example : ("hello world".split (· == ' ')).toList.map (·.toString) = ["hello", "world"] := by cbv

example : ("hello world".split (· = ' ')).toList.map (·.toString) = ["hello", "world"] := by cbv

example : ("hello world".split (' ')).toList.map (·.toString) = ["hello", "world"] := by cbv

example : (("hello world".split (· == ' ')).filter (fun x => true )).toList.map (·.toString) = ["hello", "world"] := by cbv

example : (("hello world".split (· = ' ')).filter (fun x => true )).toList.map (·.toString) = ["hello", "world"] := by cbv

example : (("hello world".split (' ')).filter (fun x => true )).toList.map (·.toString) = ["hello", "world"] := by cbv
