import PyAstLean.PyAPI.Builtins.Casting

open PyAstLean

/-- info: 42 -/
#guard_msgs in
#eval pyInt "42"

/-- info: -7 -/
#guard_msgs in
#eval pyInt "  -7  "

/-- info: 1 -/
#guard_msgs in
#eval pyInt true

/-- info: 0 -/
#guard_msgs in
#eval pyInt "oops"

/-- info: "[1, 2, 3]" -/
#guard_msgs in
#eval pyStr ([1, 2, 3] : List Int)

/-- info: "True" -/
#guard_msgs in
#eval pyStr true

/-- info: "None" -/
#guard_msgs in
#eval pyStr (none : Option Int)

/-- info: ['a', 'b', 'c'] -/
#guard_msgs in
#eval pyList "abc"

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval pyList ([1, 2, 3] : List Int)

/-- info: [1, 2] -/
#guard_msgs in
#eval pyList ((1, 2) : Int × Int)
