# PYASTLEANCHECK START
# TARGET: command
# CHECK: def pyprint_basic :=
# CHECK: PyAstLean.pyPrintIO
# CHECK: ["sum", (3 : Int), (4 : Int)]
# CHECK: return (7 : Int)
# CHECK: def pyprint_keywords :=
# CHECK: let mut a := ["a", "b", "c"]
# CHECK: PyAstLean.pyPrintIO ["a", "b", "c"] "|" "!"
# CHECK: let _ ← PyAstLean.pyPrintIO [String.append "" (ToString.toString a)]
# CHECK: return "ok"
# PYASTLEANCHECK END

def pyprint_basic():
    print("sum", 3, 4)
    return 7


def pyprint_keywords():
    a = ["a", "b", "c"]
    print("a", "b", "c", sep="|", end="!")
    print(f"{a}")
    return "ok"
