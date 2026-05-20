# PYASTLEANCHECK START
# TARGET: command
# CHECK: def arr := [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: def result := GetElem.getElem arr (0 : Int)
# PYASTLEANCHECK END

arr = [1, 2, 3]
result = arr[0]

# PYASTLEANCHECK START
# TARGET: command
# CHECK: def foo : IO String := do
# CHECK:   let x := "hi"
# CHECK:   let y := String.replicate 10 (String.get x 0)
# CHECK:   let z := String.extract y 2 7
# CHECK:   return z
# PYASTLEANCHECK END

def foo():
    x = "hi"
    y = x[0]
    y *= 10
    z = y[2:-3]
    return z
