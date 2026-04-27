import sys
import os
sys.path.append(os.path.dirname(__file__))
from node_visitor import *

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
    return json.loads(stdout)
