# PYASTLEANCHECK START
# TARGET: command
# CHECK: def read_line : IO String := do
# CHECK: let mut raw := (← PyAstLean.pyInputIO "")
# CHECK: return raw
# CHECK: def read_prompted : IO String := do
# CHECK: let __py_ret ← PyAstLean.pyInputIO "n = "
# CHECK: return __py_ret
# CHECK: def read_nested_int : IO _ := do
# CHECK: let mut a :=
# CHECK: let __py_arg0 ← PyAstLean.pyInputIO ""
# CHECK: return PyAstLean.pyInt __py_arg0
# CHECK: let mut b :=
# CHECK: let __py_arg0 ← PyAstLean.pyInputIO ""
# CHECK: return PyAstLean.pyInt __py_arg0
# CHECK: let mut c := (← PyAstLean.pyInputIO "")
# CHECK: return ((a, c))
# CHECK: def echo_input : IO Int := do
# CHECK: let __py_arg0 ← PyAstLean.pyInputIO ""
# CHECK: let __py_result ← PyAstLean.pyPrintIO [__py_arg0]
# CHECK: return (0 : Int)
# PYASTLEANCHECK END

def read_line():
    raw = input()
    return raw


def read_prompted():
    return input("n = ")


def read_nested_int():
    a = int(input())
    b = int(input())
    c = input()
    a += b
    return (a,c)


def echo_input():
    print(input())
    return 0

def input_inside_print():
    print(f"Enter a number: {int(input())}")
