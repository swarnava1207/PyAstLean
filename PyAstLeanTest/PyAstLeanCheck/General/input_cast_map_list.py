# PYASTLEANCHECK START
# TARGET: command
# CHECK: def read_int_list : IO (List Int) := do
# CHECK: let mut xs :=
# CHECK: pyList
# CHECK: pyMap pyInt
# CHECK: PyAstLean.pyStringSplit
# CHECK: PyAstLean.pyInputIO ""
# CHECK: return xs
# PYASTLEANCHECK END

def read_int_list():
    xs = list(map(int, input().split()))
    return xs
