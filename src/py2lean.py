import argparse
import sys
import os
import json
import ast
from pathlib import Path
import subprocess
import logging
sys.path.append(os.path.dirname(__file__))
from node_visitor import *

HOMEDIR = Path.absolute(Path(__name__).parent.parent)
SRC_DIR = HOMEDIR / "src"
PY_EXEC = HOMEDIR / ".venv" / "bin" / "python"
logger = logging.getLogger(__name__)

class ASTToJsonLeanVisitor(ASTToJsonLeanVisitorBase):
    """Concrete visitor that implements the translation logic for a specific subset of Python syntax."""
    pass  # For now, we only have BinOp, Constant, and Expr. We can add more visit methods as needed.
        
translator = ASTToJsonLeanVisitor()


def configure_logging(verbose: bool) -> None:
    """Configure CLI logging, keeping normal runs quiet unless verbose is enabled."""
    level = logging.DEBUG if verbose else logging.WARNING
    logging.basicConfig(level=level, format="%(levelname)s: %(message)s")

def translate_to_json(source_code, filepath=None):
    """
    Parses Python source code and translates it to a JSON IR.
    If `filepath` is provided, it first runs the annotator code to add type annotations,
    else the source_code argument will be used as-is for translation.
    """
    if filepath is not None:
        logger.debug("Annotating Python source from %s before AST translation.", filepath)
        logger.debug("Original source:\n%s", source_code)
        annotated_code = subprocess.run(
            [str(PY_EXEC), str(SRC_DIR / "annotate_python.py"), "--no-write", "--file", str(filepath)],
            text=True,
            capture_output=True,
        )
        if annotated_code.returncode != 0:
            logger.warning("Annotation failed: %s", annotated_code.stderr.strip())
            logger.warning("Falling back to unannotated source code for translation.")
        source_code = annotated_code.stdout if annotated_code.returncode == 0 else source_code

    logger.debug("Source passed to Python AST parser:\n%s", source_code)
    ast_tree = ast.parse(source_code)
    logger.debug("Parsed Python AST:\n%s", ast.dump(ast_tree, indent=4))
    data = translator.visit(ast_tree)
    logger.debug("Generated JSON IR: %s", json.dumps(data))
    return json.dumps(data)

parent_dir = Path(__file__).parent.parent

def invoke_lean_backend(ast_json, target, check=True):
    """Send one JSON AST node to the Lean backend and return the parsed JSON response."""
    json_task = json.dumps({"task": "translate", "ast": ast_json, "check": check})
    # Prefer the built executable when present; otherwise fall back to `lake exe`.
    py2lean_bin = parent_dir / ".lake" / "build" / "bin" / "py2lean"
    cmd = [str(py2lean_bin), json_task, target] if py2lean_bin.exists() else ["lake", "exe", "py2lean", json_task, target]
    logger.debug("Invoking Lean backend: %s", cmd)
    proc = subprocess.Popen(
        cmd,
        cwd=parent_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    stdout, stderr = proc.communicate()
    if stderr.strip():
        logger.debug("Lean backend stderr:\n%s", stderr.strip())
    if proc.returncode != 0:
        return {"result": False, "error": stderr.strip() or "py2lean backend failed"}
    return json.loads(stdout)

def translate_to_lean(source_code, target="term", filepath = None):
    """Translate Python source to Lean via JSON IR and the Lean backend executable."""
    json_ir = translate_to_json(source_code, filepath)
    ast_json = json.loads(json_ir)

    if ast_json.get("node_type") == "Module":
        body = ast_json.get("body", [])
        if target == "command":
            code_parts = []
            for stmt in body:
                result = invoke_lean_backend(stmt, target, check=False)
                if result.get("result") is False:
                    return result
                code_key = f"lean_{target}"
                if code_key not in result:
                    return {"result": False, "error": f"Missing '{code_key}' in backend response."}
                code_parts.append(result[code_key])
            return {"result": True, f"lean_{target}": "\n\n".join(code_parts)}

        if len(body) == 1:
            return invoke_lean_backend(body[0], target)
        return {
            "result": False,
            "error": f"Target '{target}' only supports a single top-level statement; use --target command for full modules.",
        }

    return invoke_lean_backend(ast_json, target)

def egProgram():
    return """def f(n):
    x = n + 1
    y = x * 2
    x = y - 1
    return x + y
"""


def main(argv=None):
    """CLI entry point that reads a file and forwards its contents to the translator."""
    parser = argparse.ArgumentParser(description="Translate a Python file to Lean.")
    parser.add_argument("file", nargs="?", help="Python source file to translate")
    parser.add_argument("--file", dest="file_option", help=argparse.SUPPRESS)
    parser.add_argument(
        "--target",
        nargs="?",
        default="term",
        help="Lean target string to pass to the translator (default: term)",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output for debugging")
    args = parser.parse_args(argv)
    configure_logging(args.verbose)

    file_path = args.file_option or args.file
    if not file_path:
        parser.error("the following arguments are required: file")

    source_code = Path(file_path).read_text(encoding="utf-8")
    result = translate_to_lean(source_code, args.target, file_path)

    if isinstance(result, dict):
        if result.get("result") is False:
            print(result.get("error", "Translation failed."), file=sys.stderr)
            return 1

        code_key = f"lean_{args.target}"
        if code_key in result:
            logger.info("Successfully translated to Lean target '%s'.", args.target)
            print(result[code_key])
            return 0
    print("Unexpected translation result format.", file=sys.stderr)
    print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
