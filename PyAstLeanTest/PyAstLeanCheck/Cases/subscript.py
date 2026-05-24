# PYASTLEANCHECK START
# TARGET: command
# CHECK: def arr : List Int :=
# CHECK:   [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: def result : Int :=
# CHECK:   PyAstLean.pyListGetItem arr (0 : Int)
# PYASTLEANCHECK END

arr = [1, 2, 3]
result = arr[0]

# PYASTLEANCHECK START
# TARGET: command
# CHECK: def foo : IO String :=
# CHECK:   Id.run
# CHECK:     (do
# CHECK:       let mut x : String := "hi"
# CHECK:       let mut y : String := PyAstLean.pyListGetItem x (0 : Int)
# CHECK:       y := y *ₚ (10 : Int)
# CHECK:       let mut z : String := PyAstLean.pyStringSlice y (some (2 : Int)) (some (-3))
# CHECK:       return z)
# PYASTLEANCHECK END

def foo():
    x = "hi"
    y = x[0]
    y *= 10
    z = y[2:-3]
    return z

# PYASTLEANCHECK START
# TARGET: command
# CHECK: def bar : IO String :=
# CHECK:   let x : String := "hi"
# CHECK:   let y : String := PyAstLean.pyStringSlice x (some (100 : Int)) (some (-2000))
# CHECK:   y
# PYASTLEANCHECK END

def bar():
    x = "hi"
    y = x[100:-2000]
    return y
