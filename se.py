import ast
import re
from typing import *

class SymbolicExecutor(ast.NodeVisitor):
    def __init__(self, path) -> None:
        super().__init__()
        self.funcs = {}
        self.ctx = [{}]
        self.curctx = self.ctx[0]
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

    # resolve constant or variable value
    def resolve(self, val):
        if isinstance(val, int):
            return val
        elif isinstance(val, str):
            return self.curctx[val]
    
    def eval_builtin(self, node: ast.Call, name: str) -> Any:
        if name == 'len':
            arg_name = self.visit(node.args[0])
            return len(self.curctx[arg_name])
        elif name == 'range':
            args = list(map(self.visit, node.args))
            assert(len(args) == 2)
            return list(range(self.resolve(args[0]), self.resolve(args[1])))

    def eval(self) -> None:
        print("start symbolic evaluation")
        self.visit(self.program)
        print("end symbolic evaluation")

    # ###################################################### # 
    #                                                        #
    # Visitor functions below for generating SMT constraints #
    #                                                        #
    # ###################################################### #

    # save all function definitions into the context
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if node.name not in self.funcs:
            self.funcs[node.name] = node

    def visit_Compare(self, node: ast.Compare) -> Any:
        left = self.visit(node.left)
        right = list(map(lambda n : self.visit(n), node.comparators))
        if self.ismain(left, node.ops, right):
            # we found the main entry
            # start construct SMT constraints
            self.constraints = []
            self.constraints.append("A: TYPE = ARRAY INT OF INT;")
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
        if func_name in self.funcs:
            args = list(map(self.visit, node.args))
            func = self.funcs[func_name]
            params = list(map(self.visit, func.args.args))
            assert(len(args) == len(params))
            nextctx = {}
            for i in range(0, len(args)):
                nextctx[params[i]] = self.curctx[args[i]]
            self.curctx = nextctx
            self.ctx.append(nextctx)
            self.stack.append(func_name)
            # we need to call generic_visit here
            # because visit_FunctionDef only add function to self.funcs
            # instead of traversing the function body
            self.generic_visit(func)
        else:
            return self.eval_builtin(node, func_name)

    def visit_arg(self, node: ast.arg) -> str:
        return node.arg

    def visit_Assign(self, node: ast.Assign) -> Any:
        # FIXME: this only handles single variable assignments
        name = self.visit(node.targets[0])
        self.curctx[name] = self.visit(node.value)
        print(self.curctx)

    def visit_List(self, node: ast.List) -> Any:
        return node.elts
        
    def visit_For(self, node: ast.For) -> Any:
        var = self.visit(node.target)
        r = self.visit(node.iter)
        print("var ", var)
        print("r ", r)
        for i in r:
            self.constraints.append("i%d: INT = %d;" % (i, i))

    def visit_While(self, node: ast.While) -> Any:
        pass

    def visit_AugAssign(self, node: ast.AugAssign) -> Any:
        pass

    def visit_Return(self, node: ast.Return) -> None:
        if self.stack[-1] == self.sort:
            print("Return from the sorting algorithm, finish.")
        else:
            self.stack.pop()
        name = self.visit(node.value)
        return self.curctx[name]


if __name__ == "__main__":
    se = SymbolicExecutor("sort.py")
    se.dump()
    se.eval()
    print(se.constraints)