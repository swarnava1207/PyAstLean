# PYASTLEANCHECK START
# TARGET: command
# CHECK: def answer :=
# CHECK: (42 : Int)
# CHECK: def inc := fun n ↦
# CHECK: n +ₚ answer
# PYASTLEANCHECK END

answer = 42

def inc(n):
    return n + answer
