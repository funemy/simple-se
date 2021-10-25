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
        return name[0]
    if isinstance(name, tuple):
        if len(name) == 2:
            return "%s[%s]" % (name[0], name[1])
    elif isinstance(name, str):
        return name

# ###################################################### # 
#                                                        #
#                  AST for SMT Constraints               #
#                                                        #
# ###################################################### #
class Constraint():
    def __init__(self):
        pass

    def accept(self, visitor):
        visitor.visit(self);
        return visitor.constraints

class Var(Constraint):
    def __init__(self, name: str):
        super().__init__()
        self.name = unwrap(name)

    def __repr__(self) -> str:
        return self.name

class Value(Constraint):
    def __init__(self, val: Any):
        super().__init__()
        self.val = unwrap(val)

    def __repr__(self) -> str:
        return str(self.val)

class Declare(Constraint):
    def __init__(self, var: Var, ty: str):
        super().__init__()
        self.var = var
        self.ty = ty
    
    def __repr__(self) -> str:
        return "%s: %s;" % (self.var, self.ty)

class Condition(Constraint):
    def __init__(self, left, ops, right):
        super().__init__()
        self.left = left
        self.ops = ops
        self.right = right
    
    def __repr__(self) -> str:
        return "(%s%s%s)" % (self.left, conv_ops(self.ops), conv_name(self.right))

class Assign(Constraint):
    def __init__(self, var, ty: str, exp):
        super().__init__()
        self.var = var
        self. ty = ty
        self.exp = exp

    def __repr__(self) -> str:
        return "%s: %s = %s;" % (self.var, self.ty, self.exp)

class If(Constraint):
    def __init__(self, cond: Condition, then, els):
        super().__init__()
        self.cond = cond
        self.then = then
        self.els = els

    def __repr__(self) -> str:
        return "IF %s THEN %s ELSE %s ENDIF" % (self.cond, self.then, self.els)

class IfGuard(Constraint):
    def __init__(self, cond: Condition, stmts: list[Assign]):
        super().__init__()
        self.cond = cond
        self.stmts = stmts

    def __repr__(self) -> str:
        res = ""
        res += "If %s\n" % self.cond
        for s in self.stmts:
            res += "  %s\n" % s
        return res


# ###################################################### # 
#                                                        #
#             Visitor for SMT Constraint AST             #
#                                                        #
# ###################################################### #
class ConstraintVisitor():
    def __init__(self) -> None:
        self.count = 0
        self.symbols: dict[str, str] = {}
        self.constraints: list[str] = []

    def uid(self, var: Var) -> str:
        uid = "%s_%d" % (var.name.split('_')[0], self.count)
        self.count += 1
        return uid

    def visit(self, node):
        if isinstance(node, Var):
            self.visit_Var(node)
        elif isinstance(node, Value):
            self.visit_Value(node)
        elif isinstance(node, Declare):
            self.visit_Declare(node)
        elif isinstance(node, Condition):
            self.visit_Condition(node)
        elif isinstance(node, If):
            self.visit_If(node)
        elif isinstance(node, IfGuard):
            self.visit_IfGuard(node)
        elif isinstance(node, Assign):
            self.visit_Assign(node)
    
    def visit_Var(self, node: Var):
        if node.name not in self.symbols:
            self.symbols[node.name] = node.name
            d = Declare(node.name, "INT")
            self.constraints.append(repr(d))
        else:
            node.name = self.symbols[node.name]
        print("Var: " + node.name)

    def visit_Value(self, node: Value):
        print("Value")

    def visit_Declare(self, node: Declare):
        print("Declare")
        self.visit(node.var)

    def visit_Condition(self, node: Condition):
        print("Condition")
        self.visit(node.left)
        self.visit(node.right)

    def visit_IfGuard(self, node: IfGuard):
        print("IfGuard")
        self.visit(node.cond)
        for s in node.stmts:
            s.exp = If(node.cond, s.exp, Var(s.var))
            self.visit(s)
    
    def visit_If(self, node: If):
        self.visit(node.then)
        self.visit(node.els)

    def visit_Assign(self, node: Assign):
        print("Assign")
        self.visit(node.exp)
        self.visit(node.var)
        new_var = self.uid(node.var)
        self.symbols[node.var.name] = new_var
        self.symbols[new_var] = new_var
        node.var.name = new_var
        self.constraints.append(repr(node))

def unwrap(n):
    if isinstance(n, Value):
        return n.val
    elif isinstance(n, Var):
        return n.name
    elif isinstance(n, list):
        return list(map(unwrap, n))
    else:
        return n

# ###################################################### # 
#                                                        #
#  Python AST Visitor for generating SMT Constraint AST  #
#                                                        #
# ###################################################### #
class SymbolicExecutor(ast.NodeVisitor):
    def __init__(self, path) -> None:
        super().__init__()
        self.funcs : dict[str, ast.FunctionDef]= {}
        # context is for concrete reasoning
        self.ctx = [{}]
        self.curctx = self.ctx[0]
        # symbol table is for symbolic reasoning
        self.stack = ["global"]
        self.sort = ""
        self.done = False
        self.loop = False
        # we are interested in sorting algorithm with name "xxx_sort"
        self.target = re.compile('.*_sort$')
        with open(path) as f:
            self.program = ast.parse(f.read())

    def dump(self) -> None:
        print(ast,ast.dump(self.program, indent=4))

    def ismain(self, left, ops, right) -> bool:
        if len(ops) == 1 and len(right) == 1:
            return left == '__name__' and right[0] == '__main__'
        return False

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
        cons = self.gen_constraints()
        print("Final:")
        for c in cons:
            print(c)
        print("end symbolic evaluation")

    # ###################################################### # 
    #                                                        #
    #    Visitor functions below for generating SMT AST      #
    #                                                        #
    # ###################################################### #

    def gen_constraints(self):
        v = ConstraintVisitor()
        for c in self.constraints:
            print("==============")
            print(c)
            c.accept(v)
        return v.constraints

    # save all function definitions into the context
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if node.name not in self.funcs:
            self.funcs[node.name] = node

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_Constant(self, node: ast.Constant) -> Any:
        return node.value

    def visit_List(self, node: ast.List) -> Any:
        return node.elts

    def visit_arg(self, node: ast.arg) -> str:
        return node.arg

    def visit_Subscript(self, node: ast.Subscript) -> Var:
        name = self.visit(node.value)
        idx = self.visit(node.slice)
        return Var(name+str(idx))

    def visit_Compare(self, node: ast.Compare) -> Any:
        left = self.visit(node.left)
        right = list(map(self.visit, node.comparators))
        if self.ismain(left, node.ops, right):
            # we found the main entry
            # start construct SMT constraints
            self.constraints : List[Constraint] = []
            # self.constraints.append("A: TYPE = ARRAY INT OF INT;")
            self.stack.append("main")
            print("Found main entry, start constructing SMT constraints!")
        else:
            return Condition(Var(left), node.ops, right)

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
                # self.constraints.append("%s : A" % params[0])
            res : List[Constraint] = []
            for stmt in func.body:
                r = self.visit(stmt)
                if r:
                    res = res + r
            if self.done:
                self.constraints += res
        else:
            return self.eval_builtin(node, func_name)

    def visit_Assign(self, node: ast.Assign) -> Any:
        # FIXME: this only handles single variable assignments
        name = self.visit(node.targets[0])
        val = self.visit(node.value)
        self.curctx[name] = val
        if isinstance(node.value, ast.Constant):
            v = Value(val)
        elif isinstance(node.value, ast.Name):
            v = Var(val)
        else:
            v = val
        # print(self.curctx)
        return Assign(Var(name), "INT", v)

    def visit_If(self, node: ast.If) -> Any:
        if not self.sort:
            self.generic_visit(node)
            return
        test = self.visit(node.test)
        body = list(map(self.visit, node.body))
        stmts = []
        for b in body:
            if isinstance(b, Assign):
                stmts.append(b)
            else:
                raise TypeError("Unhandled constraint in if statement: %s" % b)
        return [IfGuard(test, stmts)]

    def visit_For(self, node: ast.For) -> Any:
        var = self.visit(node.target)
        r = self.visit(node.iter)
        for i in r:
            var_cons = "%s%d" % (var, i)
            self.curctx[var] = i
            for stmt in node.body:
                cons = self.visit(stmt)

    def visit_Return(self, node: ast.Return) -> None:
        if self.stack[-1] == self.sort:
            print("Return from the sorting algorithm, finish.")
            self.done = True
        else:
            self.stack.pop()


if __name__ == "__main__":
    # se = SymbolicExecutor("sort.py")
    se = SymbolicExecutor("simple.py")
    se.dump()
    se.eval()