# Roadmap

A suggested roadmap of Python language features to implement, ordered from easiest to most complex. It begins with pure functional subsets and gradually introduces imperative state, control flow, and advanced data structures. 

## Phases

### 🟢 Phase 1: Pure Core (Expressions & Math)

*Focus: Establishing the JSON IR pipeline and basic type mapping without state mutation.*

- [x] **Primitive Literals:** `ast.Constant` (Integers, Floats, Booleans, Strings)
- [x] **Variables:** `ast.Name` (Variable lookups/loads)
- [ ] **Binary Math:** `ast.BinOp` (`+`, `-`, `*`, `/`, `//`, `%`, `**`)
- [ ] **Unary Math:** `ast.UnaryOp` (`-`, `+`)
- [ ] **Boolean Logic:** `ast.BoolOp` (`and`, `or`) and `ast.UnaryOp` (`not`)
- [ ] **Comparisons:** `ast.Compare` (`==`, `!=`, `<`, `<=`, `>`, `>=`)
- [ ] **Typed Functions:** `ast.FunctionDef` (Strictly typed arguments and return types)
- [x] **Returns:** `ast.Return` (Single return at the end of a function)
- [ ] **Ternary Expressions:** `ast.IfExp` (`x if condition else y`)

### 🟡 Phase 2: Collections & Pure Iteration

*Focus: Introducing data structures and functional programming paradigms that avoid mutable state.*

- [ ] **Tuples:** `ast.Tuple` (Mapped to Lean `Prod` or tuples)
- [ ] **Lists (Static):** `ast.List` (Mapped to Lean `Array` or `List`)
- [ ] **Subscripting (Read):** `ast.Subscript` (Reading from lists/tuples, e.g., `arr[0]`)
- [ ] **Dictionaries (Static):** `ast.Dict` (Mapped to Lean `Std.HashMap` or association lists)
- [ ] **List Comprehensions:** `ast.ListComp` (Mapped to `List.map` / `List.filter`)
- [ ] **Set & Dict Comprehensions:** `ast.SetComp`, `ast.DictComp`
- [ ] **Lambdas:** `ast.Lambda` (Anonymous functions mapped to Lean `fun x => ...`)

### 🟠 Phase 3: Control Flow & Local State

*Focus: Introducing execution branching and variable shadowing. This requires mapping to `Id.run do` in Lean or relying heavily on `let` bindings.*

- [ ] **Local Variable Assignment:** `ast.Assign` (Single targets, mapped to `let x := ...`)
- [ ] **Annotated Assignment:** `ast.AnnAssign` (e.g., `x: int = 5`)
- [ ] **Multiple Assignment:** `ast.Assign` (Multiple targets, e.g., `x, y = 1, 2`)
- [ ] **If/Else Blocks:** `ast.If` (Including `orelse` for `elif`/`else` branches)
- [ ] **Pattern Matching:** `ast.Match` and `ast.match_case` (Python 3.10+ structural matching)
- [x] **Function Calls:** `ast.Call` (Standard positional arguments)
- [ ] **Keyword Arguments:** `ast.Call` (Handling the `keywords` list)

### 🔴 Phase 4: True Mutation & Imperative Loops

*Focus: Handling constructs that fundamentally break functional purity, requiring Lean's `StateM`, `Id.run do` with `let mut`, or advanced fold mappings.*

- [ ] **Augmented Assignment:** `ast.AugAssign` (`+=`, `-=`, etc.)
- [ ] **For Loops (Bounded):** `ast.For` (Over iterables like lists or `range()`)
- [ ] **While Loops:** `ast.While` (Requires dealing with Lean's termination checker; may need `partial def`)
- [ ] **Loop Control:** `ast.Break` and `ast.Continue`
- [ ] **In-Place Subscript Mutation:** `ast.Assign` targeting an `ast.Subscript` (e.g., `arr[0] = 5`)
- [ ] **Walrus Operator:** `ast.NamedExpr` (`:=` assignment inside expressions)

### 🟣 Phase 5: Advanced Python Semantics

*Focus: Complex language features, exceptions, and object-oriented mapping.*

- [ ] **Try/Except Blocks:** `ast.Try` (Mapped to Lean's `Except` monad or `Option`)
- [ ] **Raising Exceptions:** `ast.Raise`
- [ ] **Context Managers:** `ast.With` (Mapped to bracketed execution or specific monads)
- [ ] **Classes & Methods:** `ast.ClassDef` (Mapped to Lean `structure` and namespaced `def`s)
- [ ] **Attribute Access (Read/Write):** `ast.Attribute` (e.g., `obj.property`)
- [ ] **Generators:** `ast.Yield` and `ast.YieldFrom` (Complex mapping, likely requiring streams or co-routines)
