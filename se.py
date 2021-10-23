import ast
import re
from typing import *

def conv_ops(ops) -> str:
    op = ops[0]
    if (isinstance(op, ast.GtE)):
        return ">="
    elif (isinstance(op, ast.Gt)):
        return ">"
    elif (isinstance(op, ast.LtE)):
        return "<="
    elif (isinstance(op, ast.Lt)):
        return "<"
    elif (isinstance(op, ast.Eq)):
        return "=="

def conv_name(name) -> str:
    if isinstance(name, list):
        name = name[0]
    if isinstance(name, tuple):
        if len(name) == 2:
            return "%s[%s]" % (name[0], name[1])
    elif isinstance(name, str):
        return name

class SymbolicExecutor(ast.NodeVisitor):
    def __init__(self, path) -> None:
        super().__init__()
        self.funcs = {}
        self.ctx = [{}]
        self.curctx = self.ctx[0]
        self.stack = ["global"]
        self.sort = ""
        self.done = False
        self.count = 0
        self.loop = False
        # we are interested in sorting algorithm with name "xxx_sort"
        self.target = re.compile('.*_sort$')
        with open(path) as f:
            self.program = ast.parse(f.read())

    def dump(self) -> None:
        print(ast,ast.dump(self.program, indent=4))

    def ismain(self, left: str, ops, right : List[str]) -> bool:
        if len(ops) == 1 and len(right) == 1:
            return left == '__name__' and right[0] == '__main__'

    def uid(self) -> int:
        uid = self.count
        self.count += 1
        return uid

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
        right = list(map(self.visit, node.comparators))
        if self.ismain(left, node.ops, right):
            # we found the main entry
            # start construct SMT constraints
            self.constraints = []
            self.constraints.append("A: TYPE = ARRAY INT OF INT;")
            self.stack.append("main")
            print("Found main entry, start constructing SMT constraints!")
        else:
            return (left, node.ops, right)

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_Constant(self, node: ast.Constant) -> Any:
        return node.value

    def visit_Call(self, node: ast.Call) -> Any:
        func_name = self.visit(node.func)
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
            if re.match(self.target, func_name):
                print("Found sorting function!")
                self.sort = func_name
                # we assume the first arg of sort function is the array
                self.constraints.append("%s : A" % params[0])
                self.curctx[params[0]] = params[0]
            res = []
            for stmt in func.body:
                print(stmt)
                r = self.visit(stmt)
                if r:
                    res = res + r
            if self.done:
                print("\n".join(res))
        else:
            return self.eval_builtin(node, func_name)

    def visit_arg(self, node: ast.arg) -> str:
        return node.arg

    def visit_Assign(self, node: ast.Assign) -> Any:
        # FIXME: this only handles single variable assignments
        name = self.visit(node.targets[0])
        val = self.visit(node.value)
        self.curctx[name] = val
        # print(self.curctx)
        return (conv_name(name), conv_name(val))

    def visit_If(self, node: ast.If) -> Any:
        if not self.sort:
            self.generic_visit(node)
            return
        body = list(map(self.visit, node.body))
        test = self.visit(node.test)
        test = "(%s%s%s)" % (conv_name(test[0]), conv_ops(test[1]), conv_name(test[2]))
        cons = []
        for b in body:
            c = "%s : INT = IF %s THEN %s ELSE %s;" % (b[0], test, b[1], b[0])
            cons.append(c)
        return cons

    def visit_List(self, node: ast.List) -> Any:
        return node.elts

    def visit_Subscript(self, node: ast.Subscript) -> Tuple[str, str]:
        name = self.visit(node.value)
        idx = self.visit(node.slice)
        # print("name: ", name)
        # print("idx: ", idx)
        return (self.curctx[name], idx)
        
    def visit_For(self, node: ast.For) -> Any:
        var = self.visit(node.target)
        r = self.visit(node.iter)
        for i in r:
            var_cons = "%s%d" % (var, i)
            self.constraints.append("%s: INT = %d;" % (var_cons, i))
            self.curctx[var] = i
            for stmt in node.body:
                cons = self.visit(stmt)

    def visit_Return(self, node: ast.Return) -> None:
        if self.stack[-1] == self.sort:
            print("Return from the sorting algorithm, finish.")
            self.done = True
        else:
            self.stack.pop()
        # name = self.visit(node.value)
        # return self.curctx[name]


if __name__ == "__main__":
    # se = SymbolicExecutor("sort.py")
    se = SymbolicExecutor("simple.py")
    se.dump()
    se.eval()
    print(se.constraints)