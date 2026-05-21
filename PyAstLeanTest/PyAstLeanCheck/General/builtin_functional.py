# PYASTLEANCHECK START
# TARGET: command
# CHECK: def builtin_functional :=
# CHECK: let xs := [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]
# CHECK: let ys := [(10 : Int), (20 : Int), (30 : Int)]
# CHECK: let letters := "cab"
# CHECK: let mapped := PyAstLean.pyMap
# CHECK: x +ₚ (1 : Int)
# CHECK: let filtered := PyAstLean.pyFilter
# CHECK: x %ₚ (2 : Int)
# CHECK: let zipped := pyZip xs ys
# CHECK: let enumerated := pyEnumerate letters
# CHECK: let total := pySum xs
# CHECK: let smallest := pyMin xs
# CHECK: let largest := pyMax xs
# CHECK: let reduced := PyAstLean.pyReduce
# CHECK: acc +ₚ x
# CHECK: (0 : Int)
# CHECK: def functools_reduced :=
# CHECK: let xs := [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: PyAstLean.pyReduce xs
# CHECK: acc +ₚ x
# CHECK: (0 : Int)
# CHECK: def reduce_no_init_literal :=
# CHECK: PyAstLean.pyReduceNoInit [(1 : Int), (2 : Int), (3 : Int)]
# CHECK: acc +ₚ x
# PYASTLEANCHECK END

from functools import reduce

def builtin_functional():
    xs = [1, 2, 3, 4]
    ys = [10, 20, 30]
    letters = "cab"
    mapped = map(lambda x: x + 1, xs)
    filtered = filter(lambda x: x % 2 == 0, xs)
    zipped = zip(xs, ys)
    enumerated = enumerate(letters)
    total = sum(xs)
    smallest = min(xs)
    largest = max(xs)
    reduced = reduce(lambda acc, x: acc + x, xs, 0)
    return mapped, filtered, zipped, enumerated, total, smallest, largest, reduced


def functools_reduced():
    xs = [1, 2, 3]
    return reduce(lambda acc, x: acc + x, xs, 0)


def reduce_no_init_literal():
    return reduce(lambda acc, x: acc + x, [1, 2, 3])
