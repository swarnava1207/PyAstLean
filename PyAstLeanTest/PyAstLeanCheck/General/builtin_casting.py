# PYASTLEANCHECK START
# TARGET: command
# CHECK: def builtin_casting :=
# CHECK: let a := PyAstLean.pyInt "42"
# CHECK: let b := PyAstLean.pyStr [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: let c := PyAstLean.pyList "abc"
# CHECK: let d := PyAstLean.pyStr Bool.true
# CHECK: let e := PyAstLean.pyList ((1 : Int), (2 : Int))
# PYASTLEANCHECK END

def builtin_casting():
    a = int("42")
    b = str([1, 2, 3])
    c = list("abc")
    d = str(True)
    e = list((1, 2))
    return a, b, c, d, e
