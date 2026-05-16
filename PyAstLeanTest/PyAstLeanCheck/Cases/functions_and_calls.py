# PYASTLEANCHECK START
# TARGET: command
# CHECK: def add := fun a ↦
# CHECK: fun b ↦
# CHECK: a +ₚ b
# CHECK: def call_add := fun n ↦
# CHECK: (add n) (1 : Int)
# CHECK: def keyword_call := fun n ↦
# CHECK: (add (a := n)) (b := (2 : Int))
# CHECK: def many_args := fun a ↦
# CHECK: fun b ↦
# CHECK: fun c ↦
# CHECK: fun d ↦
# CHECK: fun e ↦
# CHECK: (((a +ₚ b) +ₚ c) +ₚ d) +ₚ e
# CHECK: def complex_func := fun x ↦
# CHECK: fun y ↦
# CHECK: fun z ↦
# CHECK: Id.run
# CHECK: let mut res := x *ₚ y
# CHECK: res := res +ₚ z
# CHECK: return res
# PYASTLEANCHECK END

def add(a: Any, b: Any) -> Any:
    return a + b

def call_add(n: Any) -> Any:
    return add(n, 1)

def keyword_call(n: Any) -> Any:
    return add(a=n, b=2)

def many_args(a: Any, b: Any, c: Any, d: Any, e: Any) -> Any:
    return a + b + c + d + e

def complex_func(x: Any, y: Any, z: Any) -> Any:
    res = x * y
    res += z
    return res
