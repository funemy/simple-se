import ast
import re
from typing import *

class SymbolicExecutor(ast.NodeVisitor):
    def __init__(self, path) -> None:
        super().__init__()
        self.funcs = {}
        self.ctx = {}
        self.stack = ["global"]
        self.sort = ""
        # we are interested in sorting algorithm with name "xxx_sort"
        self.target = re.compile('.*_sort$')
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
        self.funcs[node.name] = node

    def visit_Compare(self, node: ast.Compare) -> Any:
        left = self.visit(node.left)
        right = list(map(lambda n : self.visit(n), node.comparators))
        if self.ismain(left, node.ops, right):
            # we found the main entry
            # start construct SMT constraints
            self.constraints = []
            self.stack.append("main")
            print("Found main entry, start constructing SMT constraints!")

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_Constant(self, node: ast.Constant) -> Any:
        return node.value

    def visit_Call(self, node: ast.Call) -> Any:
        func_name = self.visit(node.func)
        if re.match(self.target, func_name):
            print("Found sorting function!")
            self.sort = func_name
            self.stack.append(func_name)
            self.visit(self.funcs[func_name])
        else:
            if func_name in self.funcs:
                self.stack.append(func_name)
                self.visit(self.funcs[func_name])

    def visit_Assign(self, node: ast.Assign) -> Any:
        pass

    def visit_While(self, node: ast.While) -> Any:
        pass

    def visit_AugAssign(self, node: ast.AugAssign) -> Any:
        pass

    def visit_Return(self, node: ast.Return) -> None:
        if self.stack[-1] == self.sort:
            print("Return from the sorting algorithm, finish.")
            return
        else:
            self.stack.pop()


if __name__ == "__main__":
    se = SymbolicExecutor("sort.py")
    se.dump()
    se.eval()