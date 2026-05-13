# PYASTLEANCHECK START
# TARGET: command
# CHECK: def basic_switch := fun num ↦
# CHECK: if num == (1 : Int) then "one"
# CHECK: else "other"
# CHECK: def switch_with_guard := fun num ↦
# CHECK: let x := num
# CHECK: if x < (0 : Int) then "negative"
# CHECK: def switch_with_pattern := fun num ↦
# CHECK: num == (1 : Int) || num == (2 : Int) || num == (3 : Int)
# CHECK: else "other number"
# CHECK: def switch_with_tuple := fun point ↦
# CHECK: let x := Prod.fst✝ point
# CHECK: let y := Prod.snd✝ point
# CHECK: def switch_with_default := fun num ↦
# CHECK: if num == (1 : Int) then if num == (1 : Int) then "one" else "not one"
# PYASTLEANCHECK END

def basic_switch(num):
    match num:
        case 1:
            return "one"
        case 2:
            return "two"
        case _:
            return "other"

def switch_with_guard(num):
    match num:
        case x if x < 0:
            return "negative"
        case 0:
            return "zero"
        case x if x > 0:
            return "positive"
        
def switch_with_pattern(num):
    match num:
        case 0:
            return "zero"
        case 1 | 2 | 3:
            return "small number"
        case _:
            return "other number"
        
def switch_with_tuple(point):
    match point:
        case (0, 0):
            return "origin"
        case (x, 0):
            return f"x-axis at {x}"
        case (0, y):
            return f"y-axis at {y}"
        case (x, y):
            return f"point at ({x}, {y})"
        
def switch_with_default(num):
    match num:
        case 1:
            if num == 1:
                return "one"
            else:
                return "not one"
        case 2:
            return "two"
        case _:
            return "other"
