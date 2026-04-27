import ast
import json
from pathlib import Path
import subprocess
import sys

class ASTToJsonLeanVisitorBase:
    def visit(self, node):
        """
        The dynamic dispatcher. Routes an AST node to its specific visit_X method.
        """
        # Base case: raw primitives
        if not isinstance(node, ast.AST):
            return node
            
        # Determine the name of the method we need
        method_name = f"visit_{type(node).__name__}"
        
        # Fetch the specific method, falling back to generic_visit if it doesn't exist
        visitor = getattr(self, method_name, self.generic_visit)
        
        return visitor(node)

    def generic_visit(self, node):
        """Strict fallback to prevent unsupported syntax from leaking into the IR."""
        raise NotImplementedError(f"Translation for {type(node).__name__} is not supported in the current subset.")
    

    def visit_BinOp(self, node):
        """Translates ast.BinOp (e.g., a + b) to a JSON IR node."""
        left_json = self.visit(node.left)
        right_json = self.visit(node.right)
        
        # Map Python operators to Lean-compatible strings
        if isinstance(node.op, ast.Add):
            op = "add"
        elif isinstance(node.op, ast.Sub):
            op = "sub"
        elif isinstance(node.op, ast.Mult):
            op = "mul"
        else:
            raise NotImplementedError(f"Operator {type(node.op).__name__} not supported.")
            
        return {
            "node_type": "BinOp",
            "op": op,
            "left": left_json,
            "right": right_json
        }
    
    def visit_Constant(self, node):
        """Translates ast.Constant (e.g., 42, "hello") to a JSON IR node."""
        return {
            "node_type": "Constant",
            "value": node.value
        }
        
    def visit_Expr(self, node):
        """Translates ast.Expr (e.g., a standalone expression) to a JSON IR node."""
        return self.visit(node.value)
        
class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor that implements the translation logic for a specific subset of Python syntax."""
    pass  # For now, we only have BinOp, Constant, and Expr. We can add more visit methods as needed.
        
translator = ASTToJsonLeanVisitor()

def translate_to_json(source_code):
    """Parses Python source code and translates it to a JSON IR."""
    ast_tree = ast.parse(source_code)
    data= translator.visit(ast_tree.body[0])  # Assuming we want to translate the first statement only
    return json.dumps(data)

parent_dir = Path(__file__).parent.parent

def translate_to_lean(source_code):
    """Translates Python source code to Lean code by first converting it to JSON and then invoking the Lean code generator."""
    json_ir = translate_to_json(source_code)
    json_task = json.dumps({"task": "translate_expr", "ast": json.loads(json_ir)})
    print(f"Generated JSON IR: {json_ir}", file=sys.stderr)  # Debugging output
    proc = subprocess.Popen(
        ["lake", "exe", "py2lean", json_task],
        cwd=parent_dir,
        stdout=subprocess.PIPE,   # keep stdout if you want to read it
        stderr=None,              # inherit parent's stderr (i.e., sys.stderr)
        text=True,
    )

    stdout, _ = proc.communicate()    # Call the Lean code generator (assuming it's a standalone executable)
    # result = subprocess.run(["lake", "exe", "py2lean", json_ir], capture_output=True, text=True, cwd=parent_dir)
    
    # if result.returncode != 0:
    #     raise RuntimeError(f"Lean code generation failed: {result.stderr}")
    # # print(result.stderr) # Debugging output
    return json.loads(stdout)
