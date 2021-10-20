import ast
from typing import *

class SymbolicExecutor(ast.NodeVisitor):
    def __init__(self, path) -> None:
        super().__init__()
        self.funcs = []
        with open(path) as f:
            self.program = ast.parse(f.read())

    def dump(self) -> None:
        print(ast,ast.dump(self.program, indent=4))

    def ismain(self, left: str, ops, right : List[str]) -> bool:
        if len(ops) == 1 and len(right) == 1:
            return left == '__name__' and right[0] == '__main__'

    def eval(self) -> None:
        print("start symbolic evaluation")
        self.visit(self.program)
        print("end symbolic evaluation")

    # save all function definitions into the context
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.funcs.append(node)

    def visit_Compare(self, node: ast.Compare) -> Any:
        left = self.visit(node.left)
        right = list(map(lambda n : self.visit(n), node.comparators))
        if self.ismain(left, node.ops, right):
            # we found the main entry
            self.constraints = []
            print("we found the entry!")

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_Constant(self, node: ast.Constant) -> Any:
        return node.value


if __name__ == "__main__":
    se = SymbolicExecutor("sort.py")
    se.dump()
    se.eval()