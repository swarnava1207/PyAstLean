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
    
    def visit_Name(self, node):
        """Translates ast.Name (e.g., variable names) to a JSON IR node."""
        return {
            "node_type": "Name",
            "id": node.id
        }
    def visit_Call(self, node):
        """Translates ast.Call (e.g., function calls) to a JSON IR node."""
        func_json = self.visit(node.func)
        args_json = [self.visit(arg) for arg in node.args]
        keywords_json = {kw.arg: self.visit(kw.value) for kw in node.keywords}
        return {
            "node_type": "Call",
            "func": func_json,
            "args": args_json,
            "keywords": keywords_json
        }
        