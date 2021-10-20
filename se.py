import ast

class SymbolicExecutor(ast.NodeVisitor):
    def __init__(self, path) -> None:
        super().__init__()
        with open(path) as f:
            self.program = ast.parse(f.read())

    def dump(self) -> None:
        print(ast,ast.dump(self.program, indent=4))

    def eval(self) -> None:
        self.visit(self.program)


if __name__ == "__main__":
    se = SymbolicExecutor("sort.py")
    se.dump()