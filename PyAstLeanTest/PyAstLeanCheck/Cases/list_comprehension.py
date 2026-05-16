
def simple_lc():
    return [x for x in range(10)]

def lc_with_condition():
    return [x for x in range(10) if x % 2 == 0]

def lc_with_array():
    a = [1, 2, 3, 4, 5]
    return [x * x for x in a]

def lc_with_string():
    s = "hello"
    return [char for char in (s + " world")]

def nested_lc():
    a= [[x for x in range(5)] for _ in range(3)]
    return a

def lc_with_function_call():
    def add_one(x):
        return x + 1
    
    a = [add_one(x) for x in range(5)] 
    return a

def lc_with_multiple_conditions():
    return [x for x in range(20) if x % 2 == 0 and x % 3 == 0]

def lc_with_tuple_unpacking():
    pairs= [(1, 'a'), (2, 'b'), (3, 'c')]
    another_pairs= [(4, 'd'), (5, 'e')]
    another_pairs= [(num, char) for num, char in another_pairs if num % 2 == 0]
    _ = another_pairs 
    return [f"{num}:{char}" for num, char in pairs]

def lc_with_nested_conditions():
    return [x for x in range(20) if (x % 2 == 0 and x % 3 == 0) or x % 5 == 0]

def lc_with_side_effects():
    result= []
    for x in range(5):
        result.append(x * x)
    return [y for y in result]

def lc_with_generator_expression():
    return [x * x for x in (i for i in range(5))]

def lc_with_if_else():
    a = [x for x in range(10)]
    return [x if x % 2 == 0 else -x for x in range(10)]
 