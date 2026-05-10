import ast
import base64
import bz2
import gzip
import copy
import lzma
import marshal
import re
import zlib


def banner():
    print(f"""\033[31m
             %                                                    %
              %%                                                %%
               %%%                                            %%%
                 %%%%                                      %%%%
                   %%%%%                                %%%%%
                     %%%%%%%                        %%%%%%%
                       %%%%%%%%:                :%%%%%%%%
                         %%%%%%%%%%          %%%%%%%%%%
                           :%%%%%%%%        %%%%%%%%:
                              %%%%%%        %%%%%%
                               %%%%.         %%%%
                               %%%%          %%%%
                              :%%%%%        %%%%%:
                              %%%%%%%%%  %%%%%%%%%
                                %%%%%%%%%%%%%%%%
                                  %%%%%%%%%%%%
                                    #%%%%%%
                                       %%

                        Деобфускатор создавал ProcHacker.""")


def read(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def isstr(x):
    return isinstance(x, ast.Constant) and isinstance(x.value, str)


def asint(x):
    if isinstance(x, ast.Constant) and isinstance(x.value, int) and not isinstance(x.value, bool):
        return x.value
    return None


def val(x):
    try:
        return ast.literal_eval(x)
    except Exception:
        return None


def even_trick(x):
    if not isinstance(x, ast.Compare) or not x.ops or not isinstance(x.ops[0], ast.Eq):
        return False
    if not x.comparators or asint(x.comparators[0]) != 0:
        return False
    left = x.left
    if not isinstance(left, ast.BinOp) or not isinstance(left.op, ast.Mod) or asint(left.right) != 2:
        return False
    add = left.left
    if not isinstance(add, ast.BinOp) or not isinstance(add.op, ast.Add):
        return False
    mul = add.left
    if not isinstance(mul, ast.BinOp) or not isinstance(mul.op, ast.Mult):
        return False
    a = nameid(mul.left)
    return bool(a and nameid(mul.right) == a and nameid(add.right) == a)


def decode_blob(s):
    data = s[::-1].encode()
    funcs = [
        base64.b85decode,
        bz2.decompress,
        gzip.decompress,
        lzma.decompress,
        zlib.decompress,
        marshal.loads,
    ]
    for f in funcs:
        data = f(data)
    if isinstance(data, bytes):
        for enc in ("utf-8", "cp1251", "latin1"):
            try:
                return data.decode(enc)
            except Exception:
                pass
        return data.decode("utf-8", "ignore")
    if hasattr(data, "co_consts"):
        for c in data.co_consts:
            if isinstance(c, (str, bytes)) and len(c) > 10:
                return c.decode("utf-8", "ignore") if isinstance(c, bytes) else c
    return str(data)


def get_join(node):
    if not isinstance(node, ast.Call):
        return None
    if not isinstance(node.func, ast.Attribute) or node.func.attr != "join":
        return None
    if not node.args or not isinstance(node.args[0], ast.List):
        return None
    out = []
    for x in node.args[0].elts:
        if not isstr(x):
            return None
        out.append(x.value)
    return "".join(out)


def unpack1(text):
    old = None
    while old != text:
        old = text
        try:
            tree = ast.parse(text)
        except SyntaxError:
            break
        found = None
        for n in ast.walk(tree):
            if isinstance(n, ast.Call):
                s = get_join(n)
                if s and len(s) > 100 and all(32 <= ord(c) < 128 for c in s[:40]):
                    found = s
                    break
                if len(n.args) == 1 and isstr(n.args[0]) and len(n.args[0].value) > 100:
                    found = n.args[0].value
                    break
        if not found:
            break
        try:
            text = decode_blob(found)
        except Exception:
            break
    return text


class ConstFold(ast.NodeTransformer):
    def visit_BinOp(self, node):
        node = self.generic_visit(node)
        a = val(node)
        if isinstance(a, (str, bytes, int, float, tuple, list)):
            return ast.copy_location(ast.Constant(a) if not isinstance(a, (tuple, list)) else ast.Constant(a), node)
        return node

    def visit_UnaryOp(self, node):
        node = self.generic_visit(node)
        a = val(node)
        if isinstance(a, (int, float, str, bytes)):
            return ast.copy_location(ast.Constant(a), node)
        return node

    def visit_If(self, node):
        node = self.generic_visit(node)
        if even_trick(node.test):
            return node.body
        a = val(node.test)
        if a is True:
            return node.body
        if a is False:
            return node.orelse
        return node


def nameid(x):
    return x.id if isinstance(x, ast.Name) else None


def targetid(x):
    return x.id if isinstance(x, ast.Name) else None


def is_state_assign(st, name):
    return isinstance(st, ast.Assign) and len(st.targets) == 1 and targetid(st.targets[0]) == name and asint(st.value) is not None


def next_state(body, name):
    todo = list(reversed(body))
    while todo:
        st = todo.pop(0)
        if is_state_assign(st, name):
            return asint(st.value)
        if isinstance(st, ast.If):
            todo = list(reversed(st.body)) + list(reversed(st.orelse)) + todo
    return None


def good_stmt(st, name):
    if isinstance(st, ast.Pass):
        return False
    if is_state_assign(st, name):
        return False
    if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.value, ast.Constant):
        t = targetid(st.targets[0])
        if t and re.search(r"[^\x00-\x7f]", t):
            return False
    if isinstance(st, ast.If):
        if even_trick(st.test):
            st.body = [x for x in st.body if good_stmt(x, name)]
            return bool(st.body)
        a = val(st.test)
        if a is True:
            st.body = [x for x in st.body if good_stmt(x, name)]
            return bool(st.body)
        if a is False:
            st.body = [x for x in st.orelse if good_stmt(x, name)]
            st.orelse = []
            return bool(st.body)
    return True


def clean_body(body, name):
    out = []
    for st in body:
        if isinstance(st, ast.If):
            if even_trick(st.test):
                out += clean_body(st.body, name)
                continue
            a = val(st.test)
            if a is True:
                out += clean_body(st.body, name)
                continue
            if a is False:
                out += clean_body(st.orelse, name)
                continue
        if good_stmt(st, name):
            if isinstance(st, ast.If):
                if not st.body:
                    st.body = [ast.Pass()]
                if not st.orelse and st.orelse != []:
                    st.orelse = []
            out.append(st)
    return out


class Blocks(ast.NodeTransformer):
    def generic_visit(self, node):
        node = super().generic_visit(node)
        for k, v in list(ast.iter_fields(node)):
            if isinstance(v, list) and k in ("body", "orelse", "finalbody"):
                if not v and k == "body":
                    setattr(node, k, [ast.Pass()])
        return node


class Flow(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        node = self.generic_visit(node)
        node.body = self.fix(node.body)
        if not node.body:
            node.body = [ast.Pass()]
        return node

    def visit_AsyncFunctionDef(self, node):
        return self.visit_FunctionDef(node)

    def visit_Module(self, node):
        node = self.generic_visit(node)
        node.body = self.fix(node.body)
        return node

    def visit_ClassDef(self, node):
        node = self.generic_visit(node)
        node.body = self.fix(node.body)
        if not node.body:
            node.body = [ast.Pass()]
        return node

    def fix(self, body):
        out = []
        i = 0
        while i < len(body):
            if i + 1 < len(body) and isinstance(body[i], ast.Assign) and isinstance(body[i + 1], ast.While):
                a = body[i]
                w = body[i + 1]
                if len(a.targets) == 1 and (nm := targetid(a.targets[0])) and asint(a.value) is not None:
                    z = self.flatten(nm, asint(a.value), w)
                    if z is not None:
                        out += z
                        i += 2
                        continue
            out.append(body[i])
            i += 1
        return out

    def flatten(self, nm, start, w):
        if not isinstance(w.test, ast.Compare) or nameid(w.test.left) != nm:
            return None
        blocks = {}
        stack = list(w.body)
        while stack:
            st = stack.pop(0)
            if not isinstance(st, ast.If):
                continue
            c = st.test
            if isinstance(c, ast.Compare) and nameid(c.left) == nm and c.ops and isinstance(c.ops[0], ast.Eq):
                k = asint(c.comparators[0])
                if k is not None:
                    blocks[k] = st.body
            if len(st.orelse) == 1 and isinstance(st.orelse[0], ast.If):
                stack.append(st.orelse[0])
        if not blocks:
            return None
        res = []
        seen = set()
        cur = start
        for _ in range(len(blocks) + 5):
            if cur in seen or cur not in blocks:
                break
            seen.add(cur)
            b = clean_body(blocks[cur], nm)
            for st in b:
                res.append(st)
                if isinstance(st, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
                    return res
            nxt = next_state(blocks[cur], nm)
            if nxt is None:
                break
            cur = nxt
        return res if res else None


class Clean(ast.NodeTransformer):
    def visit_Expr(self, node):
        node = self.generic_visit(node)
        s = ast.unparse(node) if hasattr(ast, "unparse") else ""
        if "IsDebuggerPresent" in s or "gettrace" in s:
            return None
        if isinstance(node.value, ast.Constant):
            return None
        return node

    def visit_Import(self, node):
        names = [x.name for x in node.names]
        if "ctypes" in names and "sys" in names:
            return None
        return node

    def visit_Assign(self, node):
        node = self.generic_visit(node)
        return node


def is_wrap_func(node):
    if not isinstance(node, ast.FunctionDef):
        return False
    for st in ast.walk(node):
        if isinstance(st, ast.Return) and isinstance(st.value, ast.Call):
            f = st.value.func
            if isinstance(f, ast.Subscript) and isinstance(f.value, ast.Attribute):
                return True
    return False


def is_ident_class(node):
    if not isinstance(node, ast.ClassDef):
        return False
    for st in ast.walk(node):
        if isinstance(st, ast.FunctionDef) and st.name == "__new__":
            args = [a.arg for a in st.args.args[1:]]
            for r in [x for x in ast.walk(st) if isinstance(x, ast.Return)]:
                if isinstance(r.value, ast.Name) and r.value.id in args:
                    return True
    return False


class Simp(ast.NodeTransformer):
    def __init__(self):
        self.wraps = set()
        self.idents = set()
        self.decs = set()

    def visit_Module(self, node):
        for st in node.body:
            if is_wrap_func(st):
                self.wraps.add(st.name)
            if is_ident_class(st):
                self.idents.add(st.name)
            if is_dec_func(st):
                self.decs.add(st.name)
        node = self.generic_visit(node)
        node.body = [x for x in node.body if not (isinstance(x, ast.FunctionDef) and x.name in self.wraps)]
        node.body = [x for x in node.body if not (isinstance(x, ast.ClassDef) and x.name in self.idents)]
        return node

    def visit_Call(self, node):
        node = self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id in self.wraps and len(node.args) == 3:
            f, a, k = node.args
            if isinstance(a, ast.List) and isinstance(k, ast.Dict):
                return ast.copy_location(ast.Call(func=f, args=a.elts, keywords=[ast.keyword(arg=kk.value if isinstance(kk, ast.Constant) else None, value=vv) for kk, vv in zip(k.keys, k.values)]), node)
        if isinstance(node.func, ast.Name) and node.func.id in self.idents and len(node.args) == 1 and not node.keywords:
            return node.args[0]
        if isinstance(node.func, ast.Name) and node.func.id in self.decs and len(node.args) == 1:
            b = calc(node.args[0])
            if isinstance(b, bytes):
                return ast.copy_location(ast.Constant(int.from_bytes(b[9:], "big") if len(b) > 9 else 0), node)
        if isinstance(node.func, ast.Lambda) and not node.args and not node.keywords and not node.func.args.args:
            return ast.copy_location(node.func.body, node)
        v = calc(node)
        if v is BAD:
            return node
        if isinstance(v, (str, bytes, int, float, bool, type(None))):
            return ast.copy_location(ast.Constant(v), node)
        return node


def is_dec_func(node):
    if not isinstance(node, ast.FunctionDef) or len(node.args.args) != 1:
        return False
    txt = ast.unparse(node)
    return "bytearray" in txt and "* 256" in txt


BAD = object()


def calc(node):
    try:
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            if node.id == "bytes":
                return bytes
            if node.id == "str":
                return str
            if node.id == "int":
                return int
            if node.id == "len":
                return len
            if node.id == "type":
                return type
        if isinstance(node, ast.List):
            return [calc(x) for x in node.elts]
        if isinstance(node, ast.Tuple):
            return tuple(calc(x) for x in node.elts)
        if isinstance(node, ast.Dict):
            return {calc(k): calc(v) for k, v in zip(node.keys, node.values)}
        if isinstance(node, ast.UnaryOp):
            a = calc(node.operand)
            if isinstance(node.op, ast.Not):
                return not a
            if isinstance(node.op, ast.USub):
                return -a
        if isinstance(node, ast.BinOp):
            a = calc(node.left)
            b = calc(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.BitXor):
                return a ^ b
            if isinstance(node.op, ast.Mod):
                return a % b
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            a = calc(node.left)
            b = calc(node.comparators[0])
            if isinstance(node.ops[0], ast.Is):
                return a is b
            if isinstance(node.ops[0], ast.IsNot):
                return a is not b
            if isinstance(node.ops[0], ast.Eq):
                return a == b
            if isinstance(node.ops[0], ast.NotEq):
                return a != b
            if isinstance(node.ops[0], ast.Gt):
                return a > b
            if isinstance(node.ops[0], ast.Lt):
                return a < b
        if isinstance(node, ast.ListComp):
            gen = node.generators[0]
            if isinstance(gen.target, ast.Name):
                out = []
                for item in calc(gen.iter):
                    out.append(calc_sub(node.elt, gen.target.id, item))
                return out
        if isinstance(node, ast.Call):
            fobj = calc(node.func)
            if fobj is not BAD and callable(fobj):
                args = [calc(x) for x in node.args]
                if any(x is BAD for x in args):
                    return BAD
                if getattr(fobj, "__name__", "") == "gettrace":
                    return None
                if fobj in (int, bytes, str, len, type, getattr) or getattr(fobj, "__name__", "") in ("gettrace",):
                    return fobj(*args)
            if isinstance(node.func, ast.Name):
                nm = node.func.id
                args = [calc(x) for x in node.args]
                if nm == "getattr" and len(args) >= 2 and args[0] is not BAD and args[1] is not BAD:
                    return getattr(args[0], args[1], None)
                if any(x is BAD for x in args):
                    return BAD
                if nm == "int":
                    return int(*args)
                if nm == "bytes":
                    return bytes(*args)
                if nm == "str":
                    return str(*args)
                if nm == "len":
                    return len(*args)
                if nm == "type":
                    return type(*args)
                if nm == "__import__" and args and args[0] in ("sys", "os", "time", "builtins", "types"):
                    return __import__(args[0])
                if nm == "getattr":
                    return getattr(*args)
            if isinstance(node.func, ast.Attribute):
                obj = calc(node.func.value)
                args = [calc(x) for x in node.args]
                if obj is BAD or any(x is BAD for x in args):
                    return BAD
                if node.func.attr in ("decode", "fromhex", "join", "upper"):
                    return getattr(obj, node.func.attr)(*args)
    except Exception:
        return BAD
    return BAD


def calc_sub(node, name, value):
    node = copy.deepcopy(node)
    if isinstance(node, ast.Name) and node.id == name:
        return value
    class R(ast.NodeTransformer):
        def visit_Name(self, n):
            if n.id == name:
                return ast.copy_location(ast.Constant(value), n)
            return n
    return calc(R().visit(node))


class Renamer(ast.NodeTransformer):
    def __init__(self):
        self.map = {}
        self.n = 0

    def new(self, name):
        if name.startswith("__") and name.endswith("__"):
            return name
        if name not in self.map:
            self.n += 1
            self.map[name] = "v" + str(self.n)
        return self.map[name]

    def visit_Name(self, node):
        if re.search(r"[^\x00-\x7f]", node.id):
            node.id = self.new(node.id)
        return node

    def visit_arg(self, node):
        if re.search(r"[^\x00-\x7f]", node.arg):
            node.arg = self.new(node.arg)
        return node

    def visit_FunctionDef(self, node):
        if re.search(r"[^\x00-\x7f]", node.name):
            node.name = self.new(node.name)
        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node):
        if re.search(r"[^\x00-\x7f]", node.name):
            node.name = self.new(node.name)
        self.generic_visit(node)
        return node

    def visit_ExceptHandler(self, node):
        if node.name and re.search(r"[^\x00-\x7f]", node.name):
            node.name = self.new(node.name)
        self.generic_visit(node)
        return node


class Pretty(ast.NodeTransformer):
    def visit_Call(self, node):
        node = self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == "getattr" and len(node.args) >= 2:
            if isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str) and node.args[1].value.isidentifier():
                return ast.copy_location(ast.Attribute(value=node.args[0], attr=node.args[1].value, ctx=ast.Load()), node)
        return node

    def visit_Assign(self, node):
        node = self.generic_visit(node)
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if re.search(r"[^\x00-\x7f]", node.targets[0].id):
                return node
            if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "__import__":
                if len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Constant):
                    mod = node.value.args[0].value
                    if isinstance(mod, str) and mod.isidentifier() and not node.targets[0].id.startswith("__"):
                        return ast.copy_location(ast.Import(names=[ast.alias(name=mod, asname=node.targets[0].id if node.targets[0].id != mod else None)]), node)
        return node


def new_func(name, args, body):
    f = ast.FunctionDef(name=name, args=args, body=body or [ast.Pass()], decorator_list=[], returns=None, type_comment=None)
    return ast.fix_missing_locations(f)


def class_to_func(cls, forced=None):
    if not isinstance(cls, ast.ClassDef):
        return None
    if "__code__" in ast.unparse(cls) or "meta_path" in ast.unparse(cls):
        return None
    if len(cls.bases) != 1:
        return None
    if not (isinstance(cls.bases[0], ast.Name) and cls.bases[0].id == "object"):
        return None
    for st in cls.body:
        if isinstance(st, ast.FunctionDef) and st.name == "__new__":
            args = copy.deepcopy(st.args)
            if args.args:
                args.args = args.args[1:]
            body = []
            for x in st.body:
                if isinstance(x, ast.If) and "time" in ast.unparse(x):
                    continue
                if isinstance(x, ast.Assign) and "time" in ast.unparse(x):
                    continue
                body.append(x)
                if isinstance(x, ast.Return):
                    break
            f = new_func(forced or cls.name, args, body)
            f.decorator_list = copy.deepcopy(getattr(cls, "decorator_list", []))
            return ast.fix_missing_locations(f)
    return None


def self_attrs(node):
    got = set()
    setted = set()
    for n in ast.walk(node):
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == "self":
            if isinstance(n.ctx, ast.Store):
                setted.add(n.attr)
            else:
                got.add(n.attr)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "getattr":
            if len(n.args) >= 2 and isinstance(n.args[0], ast.Name) and n.args[0].id == "self" and isinstance(n.args[1], ast.Constant) and isinstance(n.args[1].value, str):
                got.add(n.args[1].value)
    return got, setted


def trim_runtime(tree):
    full = tree.body
    body = full
    cut = 0
    for i, st in enumerate(body):
        if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name) and st.targets[0].id == "__bi__":
            cut = i + 1
    if cut:
        body = full[cut:]
    work = []
    for st in body:
        txt = ast.unparse(st)
        if "os" in txt and "_exit" in txt:
            continue
        if isinstance(st, ast.ClassDef) and any(isinstance(b, ast.Name) and b.id == "type" for b in st.bases):
            continue
        if isinstance(st, ast.ClassDef) and ("__code__" in txt or "meta_path" in txt):
            continue
        work.append(st)
    refs = set()
    for st in work:
        for n in ast.walk(st):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                refs.add(n.id)
    out = []
    method_names = set()
    for st in work:
        if isinstance(st, (ast.ClassDef, ast.FunctionDef)):
            continue
        for n in ast.walk(st):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "getattr":
                if len(n.args) >= 2 and isinstance(n.args[1], ast.Constant) and isinstance(n.args[1].value, str):
                    method_names.add(n.args[1].value)
    if cut:
        for st in full[:cut]:
            if isinstance(st, (ast.FunctionDef, ast.ClassDef)) and st.name in refs:
                f = class_to_func(st)
                if f:
                    out.append(f)
                elif isinstance(st, ast.FunctionDef) and not ("bytearray" in ast.unparse(st) and "* 256" in ast.unparse(st)):
                    out.append(st)
    for st in work:
        f = class_to_func(st)
        if f:
            out.append(f)
            continue
        if isinstance(st, ast.ClassDef):
            nb = []
            got, setted = self_attrs(st)
            prop_names = [x for x in got - setted if x not in method_names]
            used = set()
            for x in st.body:
                if isinstance(x, ast.ClassDef):
                    fname = None
                    isprop = any(isinstance(d, ast.Name) and d.id == "property" for d in x.decorator_list)
                    if isprop and prop_names:
                        fname = prop_names[0]
                    else:
                        for m in method_names:
                            if m not in ("__file__", "__code__", "__locked__", "__setattr__") and m not in used:
                                fname = m
                                break
                    fx = class_to_func(x, fname)
                    if fx:
                        used.add(fx.name)
                        nb.append(fx)
                        continue
                nb.append(x)
            st.body = nb or [ast.Pass()]
            out.append(st)
            continue
        out.append(st)
    tree.body = out
    return tree


def nice(text, rename=True):
    text = unpack1(text)
    tree = ast.parse(text)
    for tr in (ConstFold(), Flow(), Simp(), ConstFold(), Simp(), ConstFold(), Clean(), ConstFold(), Flow(), Simp(), ConstFold(), Clean(), Blocks()):
        tree = tr.visit(tree)
        ast.fix_missing_locations(tree)
    tree = trim_runtime(tree)
    for tr in (Simp(), ConstFold(), Clean(), Pretty(), Blocks()):
        tree = tr.visit(tree)
        ast.fix_missing_locations(tree)
    if rename:
        tree = Renamer().visit(tree)
        ast.fix_missing_locations(tree)
    out = ast.unparse(tree)
    out = re.sub(r"\n{3,}", "\n\n", out).strip() + "\n"
    return out


def main():
    banner()
    src = ""
    while not src:
        src = input("Введите путь к файлу: ").strip().strip('"')
    dst = re.sub(r"\.py$", "", src) + "_deobf.py"
    text = read(src)
    out = nice(text)
    write(dst, out)
    print(f"Deobfuscated file written to: {dst}")


if __name__ == "__main__":
    main()
