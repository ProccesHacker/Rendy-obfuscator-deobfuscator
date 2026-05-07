import ast
import bz2
import os
import base64
import builtins
import gzip
import hashlib
import importlib
import lzma
import marshal
import pathlib
import re
import sys
import types
import zlib

def print_banner(mode):
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

def process_data(name):
    return getattr(importlib.import_module(name), name.split('.')[-1], importlib.import_module(name))

class Coreclass(ast.NodeTransformer):

    def __init__(self, metadata=None):
        metadata = metadata or {}
        self.missing = object()
        self.fake_sys = types.SimpleNamespace(gettrace=lambda: None, modules={})
        self.fake_os = types.SimpleNamespace(path=types.SimpleNamespace(exists=lambda *_: False, isfile=lambda *_: False))
        self.fake_time = types.SimpleNamespace(time=lambda: 0)
        self.fake_hashlib = hashlib
        self.safe_globals = {'__builtins__': {}, 'bytes': bytes, 'bytearray': bytearray, 'str': str, 'int': int, 'len': len, 'type': type, 'getattr': getattr, 'hasattr': hasattr, 'isinstance': isinstance, 'Exception': Exception, 'BaseException': BaseException, 'ValueError': ValueError, 'TypeError': TypeError, 'KeyError': KeyError, 'range': range, 'list': list, 'tuple': tuple, 'map': map, '__import__': self.f4, 'sys': self.fake_sys, 'os': self.fake_os, 'time': self.fake_time, 'hashlib': self.fake_hashlib}
        self.scope_stack = [{}]
        self.wrapper_names = set(metadata.get('wrappers', set()))
        self.helper_calls = dict(metadata.get('helpers', {}))
        self.identity_names = set(metadata.get('identity', set()))

    def f4(self, name, *args, **kwargs):
        if name == 'sys':
            return self.fake_sys
        if name == 'os':
            return self.fake_os
        if name == 'time':
            return self.fake_time
        if name == 'hashlib':
            return self.fake_hashlib
        raise ImportError(name)

    def f5(self, node):
        if not isinstance(node, ast.FunctionDef):
            return node
        cut = next((i for i, x in enumerate(node.body) if isinstance(x, ast.While)), -1)
        if cut < 0:
            return node
        prefix = node.body[:cut]
        loop = node.body[cut]
        tail = node.body[cut + 1:]
        if not prefix or not isinstance(prefix[-1], ast.Assign):
            return node
        slot = prefix[-1]
        if len(slot.targets) != 1 or not isinstance(slot.targets[0], ast.Name):
            return node
        try:
            state = ast.literal_eval(slot.value)
        except Exception:
            return node
        name = slot.targets[0].id
        body = prefix[:-1]
        seen = set()
        while state not in seen:
            seen.add(state)
            branch = self.f6(loop.body, name, state)
            if branch is None:
                break
            jump = None
            inner = branch.body
            take = inner
            for idx, stmt in enumerate(inner):
                if isinstance(stmt, ast.If):
                    take = inner[idx].body
                    break
            for stmt in take:
                if isinstance(stmt, ast.Assign) and any((isinstance(t, ast.Name) and t.id == name for t in stmt.targets)):
                    try:
                        jump = ast.literal_eval(stmt.value)
                    except Exception:
                        jump = None
                elif isinstance(stmt, ast.Pass):
                    continue
                else:
                    body.append(stmt)
                    if isinstance(stmt, (ast.Return, ast.Raise)):
                        out = ast.FunctionDef(name=node.name, args=node.args, body=body, decorator_list=node.decorator_list, returns=node.returns, type_comment=node.type_comment)
                        return ast.fix_missing_locations(out)
            if jump is None:
                break
            state = jump
        if tail:
            body.extend(tail)
        out = ast.FunctionDef(name=node.name, args=node.args, body=body or [ast.Pass()], decorator_list=node.decorator_list, returns=node.returns, type_comment=node.type_comment)
        return ast.fix_missing_locations(out)

    def f6(self, nodes, name, state):
        for stmt in ast.walk(ast.Module(body=list(nodes), type_ignores=[])):
            if not isinstance(stmt, ast.If):
                continue
            test = stmt.test
            if isinstance(test, ast.Compare) and isinstance(test.left, ast.Name) and (test.left.id == name) and (len(test.ops) == 1) and isinstance(test.ops[0], ast.Eq) and (len(test.comparators) == 1) and isinstance(test.comparators[0], ast.Constant) and (test.comparators[0].value == state):
                return stmt
        return None

    def f7(self, node):
        ok = (ast.Expression, ast.Constant, ast.Name, ast.Load, ast.Store, ast.Call, ast.Attribute, ast.List, ast.Tuple, ast.Dict, ast.Set, ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare, ast.Lambda, ast.arguments, ast.arg, ast.ListComp, ast.comprehension, ast.IfExp, ast.Subscript, ast.Slice, ast.keyword)
        ops = (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow, ast.BitXor, ast.BitOr, ast.BitAnd, ast.LShift, ast.RShift, ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Is, ast.IsNot, ast.In, ast.NotIn, ast.And, ast.Or, ast.Not, ast.USub, ast.UAdd)
        for item in ast.walk(node):
            if isinstance(item, ops):
                continue
            if not isinstance(item, ok):
                return False
        return True

    def f8(self, value):
        if isinstance(value, int) and value.bit_length() > 8192:
            raise TypeError('int_too_large')
        if isinstance(value, (str, bytes, int, float, complex, bool)) or value is None:
            return ast.Constant(value=value)
        if isinstance(value, list):
            return ast.List(elts=[self.f8(x) for x in value], ctx=ast.Load())
        if isinstance(value, tuple):
            return ast.Tuple(elts=[self.f8(x) for x in value], ctx=ast.Load())
        if isinstance(value, dict):
            return ast.Dict(keys=[self.f8(k) for k in value.keys()], values=[self.f8(v) for v in value.values()])
        raise TypeError(type(value).__name__)

    def f9(self, node):
        if not self.f7(node):
            raise ValueError
        env = dict(self.safe_globals)
        for scope in self.scope_stack:
            for name, value in scope.items():
                if value is not self.missing:
                    env[name] = value
        env.update(self.helper_calls)
        for name in self.identity_names:
            env[name] = lambda x: x
        code = compile(ast.Expression(node), '<xat>', 'eval')
        return eval(code, env, env)

    def f10(self, names=()):
        scope = {}
        for name in names:
            scope[name] = self.missing
        self.scope_stack.append(scope)

    def f11(self):
        self.scope_stack.pop()

    def f12(self, node):
        names = [arg.arg for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]]
        if node.args.vararg:
            names.append(node.args.vararg.arg)
        if node.args.kwarg:
            names.append(node.args.kwarg.arg)
        self.f10(names)
        self.generic_visit(node)
        self.f11()
        return node

    def f13(self, node):
        body = [item for item in node.body if not isinstance(item, ast.Pass)]
        if len(body) != 1:
            return None
        fn = body[0]
        if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)) or fn.name != '__new__':
            return None
        args = ast.arguments(posonlyargs=list(fn.args.posonlyargs), args=list(fn.args.args[1:]), vararg=fn.args.vararg, kwonlyargs=list(fn.args.kwonlyargs), kw_defaults=list(fn.args.kw_defaults), kwarg=fn.args.kwarg, defaults=list(fn.args.defaults))
        if isinstance(fn, ast.AsyncFunctionDef):
            out = ast.AsyncFunctionDef(name=node.name, args=args, body=fn.body, decorator_list=list(node.decorator_list), returns=None, type_comment=None)
        else:
            out = ast.FunctionDef(name=node.name, args=args, body=fn.body, decorator_list=list(node.decorator_list), returns=None, type_comment=None)
        return ast.fix_missing_locations(out)

    def f14(self, node):
        node.body = [self.visit(self.f5(x)) for x in node.body]
        fresh = []
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
                continue
            if isinstance(stmt, ast.Expr) and 'sys.exit' in ast.unparse(stmt.value):
                continue
            if isinstance(stmt, ast.Pass):
                continue
            if isinstance(stmt, ast.While) and len(stmt.body) == 1 and isinstance(stmt.body[0], ast.Pass):
                continue
            if isinstance(stmt, ast.Try) and (not stmt.finalbody) and (not stmt.orelse) and all((len(x.body) == 1 and isinstance(x.body[0], ast.Pass) for x in stmt.handlers)):
                fresh.extend(stmt.body)
                continue
            fresh.append(stmt)
        node.body = fresh
        return node

    def f15(self, node):
        node = self.f5(node)
        node.returns = None
        for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]:
            arg.annotation = None
        if node.args.vararg:
            node.args.vararg.annotation = None
        if node.args.kwarg:
            node.args.kwarg.annotation = None
        return self.f12(node)

    def f16(self, node):
        node.returns = None
        for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]:
            arg.annotation = None
        if node.args.vararg:
            node.args.vararg.annotation = None
        if node.args.kwarg:
            node.args.kwarg.annotation = None
        return self.f12(node)

    def f17(self, node):
        self.f10()
        node = self.generic_visit(node)
        self.f11()
        return self.f13(node) or node

    def f18(self, node):
        node = self.generic_visit(node)
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            try:
                value = self.f9(node.value)
            except Exception:
                return node
            try:
                packed = self.f8(value)
            except Exception:
                self.scope_stack[-1][node.targets[0].id] = value
                return node
            self.scope_stack[-1][node.targets[0].id] = value
            node.value = packed
        return node

    def f19(self, node):
        node = self.generic_visit(node)
        try:
            value = self.f9(node.test)
        except Exception:
            if not node.body:
                node.body = [ast.Pass()]
            return node
        return node.body if value else node.orelse

    def f20(self, node):
        node = self.generic_visit(node)
        if not node.body:
            node.body = [ast.Pass()]
        return node

    def f21(self, node):
        node = self.generic_visit(node)
        if not node.body:
            node.body = [ast.Pass()]
        for handler in node.handlers:
            if not handler.body:
                handler.body = [ast.Pass()]
        return node

    def f22(self, node):
        if not isinstance(node, ast.Call) or not hasattr(node, 'func'):
            return node
        node = self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id in self.identity_names and (len(node.args) == 1) and (not node.keywords):
            return node.args[0]
        if isinstance(node.func, ast.Name) and node.func.id in self.wrapper_names and (len(node.args) == 3) and (not node.keywords):
            bag, argv, kw = node.args
            if isinstance(argv, ast.List) and isinstance(kw, ast.Dict) and all((k is None or isinstance(k, ast.Constant) for k in kw.keys)):
                return ast.copy_location(ast.Call(func=bag, args=argv.elts, keywords=[ast.keyword(arg=k.value if isinstance(k, ast.Constant) else None, value=v) for k, v in zip(kw.keys, kw.values)]), node)
        if isinstance(node.func, ast.Name) and node.func.id in self.helper_calls and (len(node.args) == 1):
            try:
                return ast.copy_location(self.f8(self.helper_calls[node.func.id](self.f9(node.args[0]))), node)
            except Exception:
                return node
        try:
            value = self.f9(node)
        except Exception:
            return node
        try:
            return ast.copy_location(self.f8(value), node)
        except Exception:
            return node

    def visit_Module(self, node):
        return self.f14(node)

    def visit_FunctionDef(self, node):
        return self.f15(node)

    def visit_AsyncFunctionDef(self, node):
        return self.f16(node)

    def visit_ClassDef(self, node):
        return self.f17(node)

    def visit_Assign(self, node):
        return self.f18(node)

    def visit_If(self, node):
        return self.f19(node)

    def visit_While(self, node):
        return self.f20(node)

    def visit_Try(self, node):
        return self.f21(node)

    def visit_Call(self, node):
        return self.f22(node)

class Coreclass2:

    def __init__(self):
        setter = getattr(sys, 'set_int_max_str_digits', None)
        if callable(setter):
            try:
                setter(0)
            except Exception:
                pass

    def f23(self, tree):
        metadata = {'wrappers': set(), 'helpers': {}, 'identity': set(), 'helper_names': set()}
        cleaner = Coreclass()
        for node in list(tree.body):
            if not isinstance(node, ast.FunctionDef):
                continue
            flat = cleaner.f5(node)
            body = [item for item in flat.body if not isinstance(item, ast.Pass)]
            core = [item for item in body if not isinstance(item, ast.Assign)]
            if len(core) == 1 and isinstance(core[0], ast.Return) and isinstance(core[0].value, ast.Name):
                arg_names = [arg.arg for arg in flat.args.args]
                if len(arg_names) == 1 and core[0].value.id == arg_names[0]:
                    metadata['identity'].add(flat.name)
                    continue
            if any((self.f24(item) for item in body)):
                metadata['wrappers'].add(flat.name)
                continue
            if len(flat.args.args) == 1:
                helper = self.f25(flat)
                if helper is not None:
                    metadata['helpers'][flat.name] = helper
                    metadata['helper_names'].add(flat.name)
        return metadata

    def f24(self, node):
        if not isinstance(node, ast.Try) or not node.handlers:
            return False
        handler = node.handlers[0]
        if len(handler.body) != 1 or not isinstance(handler.body[0], ast.Return):
            return False
        ret = handler.body[0].value
        if not isinstance(ret, ast.Call) or not isinstance(ret.func, ast.Subscript):
            return False
        if len(ret.args) != 1 or not isinstance(ret.args[0], ast.Starred) or len(ret.keywords) != 1:
            return False
        pieces = [ret.func, ret.args[0].value, ret.keywords[0].value]
        for item, index in zip(pieces, (0, 1, 2)):
            if not isinstance(item, ast.Subscript):
                return False
            if not isinstance(item.value, ast.Attribute) or item.value.attr != 'args':
                return False
            if not isinstance(item.value.value, ast.Name) or item.value.value.id != handler.name:
                return False
            if not isinstance(item.slice, ast.Constant) or item.slice.value != index:
                return False
        return True

    def f25(self, fn):
        bad = (ast.Import, ast.ImportFrom, ast.With, ast.AsyncWith, ast.Try, ast.Raise, ast.Lambda, ast.Global, ast.Nonlocal, ast.Delete, ast.Yield, ast.YieldFrom, ast.Await)
        for node in ast.walk(fn):
            if isinstance(node, bad):
                return None
        env = {'__builtins__': {}, 'int': int, 'len': len, 'bytearray': bytearray, 'bytes': bytes, 'range': range}
        try:
            code = compile(ast.Module(body=[ast.fix_missing_locations(fn)], type_ignores=[]), '<helper>', 'exec')
            exec(code, env, env)
        except Exception:
            return None
        func = env.get(fn.name)
        return func if callable(func) else None

    def f26(self, tree, metadata=None):
        metadata = metadata or {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                node.returns = None
                for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]:
                    arg.annotation = None
                if node.args.vararg:
                    node.args.vararg.annotation = None
                if node.args.kwarg:
                    node.args.kwarg.annotation = None
        keep = []
        names = set()
        for item in ast.walk(tree):
            if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load):
                names.add(item.id)
        defined = self.f35(tree)
        unresolved = {item.id for item in ast.walk(tree) if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load) and item.id not in defined}
        trash = {'__decoder__', '__identity_func__'} | set(metadata.get('wrappers', set())) | set(metadata.get('identity', set())) | set(metadata.get('helper_names', set()))
        guards = {'__IntegrityChecker__', '__UltraProtection__', '__check_lib__', '__tarpit__', '__runtime_protect__', '__validate_signature__'}
        for stmt in tree.body:
            if isinstance(stmt, ast.FunctionDef) and stmt.name in trash and (stmt.name not in names):
                continue
            if isinstance(stmt, ast.FunctionDef) and stmt.name == '__decoder__':
                continue
            if isinstance(stmt, (ast.FunctionDef, ast.ClassDef)) and stmt.name in guards:
                continue
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name) and isinstance(stmt.value, ast.List):
                if len(stmt.value.elts) > 32 and all((isinstance(x, ast.Constant) and x.value == '\x02\x02' for x in stmt.value.elts)):
                    continue
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
                if stmt.targets[0].id not in names and stmt.targets[0].id not in unresolved and isinstance(stmt.value, ast.Constant):
                    continue
            if isinstance(stmt, ast.Try):
                text = ast.unparse(stmt)
                if '__ANTI_DECOMPILER__' in text:
                    continue
                if '__var_' in text and '__check_' in text and ('lambda: None' in text):
                    continue
                if '__confusion__' in text and 'lambda: None' in text:
                    continue
                if text.strip() in {'try:\n    pass\nexcept:\n    pass', 'try:\n    pass\nexcept:\n    pass\nfinally:\n    pass'}:
                    continue
            if isinstance(stmt, ast.Expr):
                text = ast.unparse(stmt.value)
                if any((x in text for x in ['__check_imports__', '__protect__'])):
                    continue
            if isinstance(stmt, ast.For):
                text = ast.unparse(stmt)
                if '__check_lib__' in text:
                    continue
            if isinstance(stmt, ast.If):
                text = ast.unparse(stmt)
                if '__main__' in text and '__validate_signature__' in text:
                    continue
            keep.append(stmt)
        tree.body = keep
        tree = self.f27(tree)
        tree = self.f27_preserve_globals(tree)
        tree = self.f29(tree)
        tree = self.f28(tree)
        return ast.fix_missing_locations(tree)

    def f27_preserve_globals(self, tree):
        defined = self.f35(tree)
        loaded = {item.id for item in ast.walk(tree) if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load)}
        unresolved = loaded - defined
        if not unresolved:
            return tree
        fresh = []
        for stmt in tree.body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
                target = stmt.targets[0].id
                if target in unresolved:
                    fresh.append(stmt)
                    continue
            fresh.append(stmt)
        tree.body = fresh
        return tree

    def f27(self, tree):
        suspicious_tokens = ('__obf_safe__', 'debugpy', 'pydevd', 'currentframe', '.stack(', 'get_objects(', 'co_code', '__forbidden__', '_exit(', 'x ** x', 'sha256(__code_str__.encode())', "__import__('inspect')", "__import__('gc')", "__import__('sys').exit(1)", 'IsDebuggerPresent', 'gettrace', '__locked__', '__wrapper__', 'while True: pass', 'pystyle', 'requests')
        drop_names = set()
        for stmt in tree.body:
            if isinstance(stmt, (ast.FunctionDef, ast.ClassDef)):
                text = ast.unparse(stmt)
                if any((token in text for token in suspicious_tokens)):
                    drop_names.add(stmt.name)
                    continue
                if isinstance(stmt, ast.FunctionDef):
                    if 'lambda: 1 / 0' in text:
                        drop_names.add(stmt.name)
                        continue
                    if '__code_str__.sha256(__code_str__.encode()).hexdigest()' in text:
                        drop_names.add(stmt.name)
                        continue
                    if 'getattr(__import__(\'os\'), \'_exit\')(1)' in text or "getattr(__import__('os'), '_exit')(1)" in text:
                        drop_names.add(stmt.name)
                        continue
                    if 'while True' in text and 'pass' in text and '__wrapper__' in text:
                        drop_names.add(stmt.name)
                        continue
                    if '__import__(__lib_name__)' in text and "__size__ < 100" in text:
                        drop_names.add(stmt.name)
                        continue
                if isinstance(stmt, ast.ClassDef):
                    if '__setattr__' in text and '__locked__' in text:
                        drop_names.add(stmt.name)
                        continue
        fresh = []
        for stmt in tree.body:
            text = ast.unparse(stmt)
            if isinstance(stmt, ast.Import):
                names = {alias.asname or alias.name.split('.')[-1] for alias in stmt.names}
                if names <= {'sys', 'ctypes'} and ('IsDebuggerPresent' in text or 'gettrace' in text):
                    continue
            if isinstance(stmt, ast.Try):
                t = text
                if 'lambda: 1 / 0' in t:
                    continue
                if 'lambda: None' in t and all((len(h.body) == 1 and isinstance(h.body[0], ast.Pass) for h in stmt.handlers)):
                    continue
                if all((len(h.body) == 1 and isinstance(h.body[0], ast.Pass) for h in stmt.handlers)):
                    if all((isinstance(x, (ast.Expr, ast.Pass, ast.Assign, ast.AnnAssign, ast.If, ast.Try)) for x in stmt.body)):
                        continue
            if isinstance(stmt, (ast.FunctionDef, ast.ClassDef)) and stmt.name in drop_names:
                continue
            if isinstance(stmt, ast.Assign):
                if len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name) and (stmt.targets[0].id == '__main__') and isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Name) and (stmt.value.func.id == '__import__'):
                    continue
            if isinstance(stmt, ast.If):
                text = ast.unparse(stmt)
                if "hasattr(__main__, '__file__')" in text:
                    continue
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                if isinstance(call.func, ast.Name) and call.func.id in drop_names:
                    continue
                if isinstance(call.func, ast.Attribute) and isinstance(call.func.value, ast.Name) and (call.func.value.id in drop_names):
                    continue
                if isinstance(call.func, ast.Call) and isinstance(call.func.func, ast.Name) and call.func.func.id == 'getattr':
                    continue
            if isinstance(stmt, ast.Expr) and ('IsDebuggerPresent' in text or 'gettrace' in text):
                continue
            if isinstance(stmt, ast.For) and 'requests' in text and 'pystyle' in text:
                continue
            if isinstance(stmt, ast.ClassDef) and '__locked__' in text:
                continue
            if isinstance(stmt, ast.FunctionDef) and ('_exit' in text or ('while True' in text and 'pass' in text)):
                continue
            if isinstance(stmt, ast.FunctionDef) and '__import__(__lib_name__)' in text:
                continue
            fresh.append(stmt)
        defined = set()
        for stmt in fresh:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                defined.add(stmt.name)
            elif isinstance(stmt, (ast.Import, ast.ImportFrom)):
                for alias in stmt.names:
                    defined.add(alias.asname or alias.name.split('.')[-1])
            elif isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Name):
                        defined.add(target.id)
        cleaned = []
        for stmt in fresh:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                fn = stmt.value.func
                if isinstance(fn, ast.Name) and fn.id not in defined and (fn.id not in dir(builtins)):
                    continue
                if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name):
                    if fn.value.id not in defined and fn.value.id not in dir(builtins):
                        continue
            cleaned.append(stmt)
        tree.body = cleaned
        return tree

    def f28(self, tree):
        mapping = {}
        f_idx = 1
        c_idx = 1
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                if node.name.startswith('__') and node.name.endswith('__'):
                    continue
                if node.name not in mapping:
                    mapping[node.name] = f'C{c_idx}'
                    c_idx += 1
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name.startswith('__') and node.name.endswith('__'):
                    continue
                if node.name not in mapping:
                    mapping[node.name] = f'f{f_idx}'
                    f_idx += 1
        if not mapping:
            return tree
        tree = Coreclass5(mapping).visit(tree)
        return ast.fix_missing_locations(tree)

    def f29(self, tree):
        self.f31(tree)
        self.f32(tree)
        self.f33(tree)
        self.f34(tree)
        self.f30(tree)
        tree = Coreclass4().visit(tree)
        self.f36(tree)
        return ast.fix_missing_locations(tree)

    def f30(self, tree):
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            used = set()
            for item in self.f37(node):
                if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load):
                    used.add(item.id)
            fresh = []
            for stmt in node.body:
                if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name) and (stmt.targets[0].id not in used) and isinstance(stmt.value, ast.Constant):
                    continue
                fresh.append(stmt)
            node.body = fresh or [ast.Pass()]

    def f31(self, tree):
        defined = self.f35(tree)
        attrs = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and (node.func.id == 'getattr') and (len(node.args) >= 2) and isinstance(node.args[0], ast.Name) and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str):
                attrs.setdefault(node.args[0].id, set()).add(node.args[1].value)
            elif isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
                attrs.setdefault(node.value.id, set()).add(node.attr)
        mapping = {frozenset({'seed', 'randint'}): 'random', frozenset({'dumps'}): 'json', frozenset({'sleep', 'gather', 'run'}): 'asyncio', frozenset({'ArgumentParser'}): 'argparse'}
        new_imports = []
        for name, values in attrs.items():
            if name in defined:
                continue
            for keys, module in mapping.items():
                if keys.issubset(values):
                    new_imports.append(ast.Import(names=[ast.alias(name=module, asname=name)]))
                    defined.add(name)
                    break
        if not new_imports:
            return
        pos = 0
        while pos < len(tree.body) and isinstance(tree.body[pos], (ast.Import, ast.ImportFrom)):
            pos += 1
        tree.body[pos:pos] = new_imports

    def f32(self, tree):
        for node in ast.walk(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            if not any((isinstance(dec, ast.Name) and dec.id == 'dataclass' for dec in node.decorator_list)):
                continue
            fields = [item for item in node.body if isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name)]
            if not fields:
                continue
            keywords = []
            for item in ast.walk(tree):
                if isinstance(item, ast.Call) and isinstance(item.func, ast.Name) and (item.func.id == node.name) and item.keywords:
                    keys = [kw.arg for kw in item.keywords if kw.arg]
                    if len(keys) == len(fields):
                        keywords = keys
                        break
            if len(keywords) != len(fields):
                continue
            for field, name in zip(fields, keywords):
                field.target.id = name

    def f33(self, tree):
        class_methods = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                methods = [item for item in node.body if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)) and item.name != '__init__']
                if methods:
                    class_methods[node.name] = methods
        if not class_methods:
            return
        types = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                call = node.value
                if isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and (call.func.id in class_methods):
                    types[node.targets[0].id] = call.func.id
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            if not isinstance(node.func, ast.Call):
                continue
            inner = node.func
            if not (isinstance(inner.func, ast.Name) and inner.func.id == 'getattr' and (len(inner.args) >= 2) and isinstance(inner.args[0], ast.Name) and isinstance(inner.args[1], ast.Constant) and isinstance(inner.args[1].value, str)):
                continue
            owner = types.get(inner.args[0].id)
            if not owner:
                continue
            target = inner.args[1].value
            methods = class_methods.get(owner, [])
            if any((method.name == target for method in methods)):
                continue
            candidates = [method for method in methods if len(method.args.args) == len(node.args) + 1]
            chosen = None
            if len(candidates) == 1:
                chosen = candidates[0]
            else:
                for method in candidates:
                    text = ast.unparse(method)
                    if target == 'digest' and 'hexdigest' in text:
                        chosen = method
                        break
                    if target == 'masked' and "'*'" in text:
                        chosen = method
                        break
            if chosen is not None:
                chosen.name = target

    def f34(self, tree):
        module_defined = self.f35(tree)
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            params = [arg.arg for arg in node.args.args]
            if params and params[0] == 'self':
                params = params[1:]
            if not params or len(params) > 3:
                continue
            local_defined = set((arg.arg for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]))
            for item in self.f37(node):
                if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Store):
                    local_defined.add(item.id)
            seen = []
            seen_set = set()
            for item in self.f37(node):
                if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load):
                    if item.id in local_defined or item.id in module_defined or item.id in dir(builtins):
                        continue
                    if item.id not in seen_set:
                        seen.append(item.id)
                        seen_set.add(item.id)
            if len(seen) != len(params):
                continue
            mapping = dict(zip(seen, params))
            replacer = Coreclass3(mapping)
            node.body = [replacer.visit(item) for item in node.body]

    def f35(self, tree):
        names = set(dir(builtins))
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names.add(node.name)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    names.add(alias.asname or alias.name.split('.')[-1])
            elif isinstance(node, ast.ImportFrom):
                for alias in node.names:
                    names.add(alias.asname or alias.name)
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        names.add(target.id)
        return names

    def f36(self, tree):
        used = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                used.add(node.id)
        keep = []
        for node in tree.body:
            if isinstance(node, ast.Import):
                names = [alias for alias in node.names if (alias.asname or alias.name.split('.')[-1]) in used]
                if names:
                    node.names = names
                    keep.append(node)
                continue
            if isinstance(node, ast.ImportFrom):
                names = [alias for alias in node.names if (alias.asname or alias.name) in used]
                if names:
                    node.names = names
                    keep.append(node)
                continue
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                if node.targets[0].id not in used:
                    continue
            keep.append(node)
        tree.body = keep

    def f37(self, node):
        stack = list(getattr(node, 'body', ()))
        blocked = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
        while stack:
            current = stack.pop()
            yield current
            if isinstance(current, blocked):
                continue
            stack.extend(ast.iter_child_nodes(current))

    def f38(self, text):
        seen = set()
        blob = text.encode('utf-8') if isinstance(text, str) else bytes(text)
        while blob not in seen:
            seen.add(blob)
            nxt = self.f39(blob)
            if nxt is None:
                break
            blob = nxt.encode('utf-8') if isinstance(nxt, str) else bytes(nxt)
        return blob.decode('utf-8', 'replace')

    def f39(self, blob):
        text = blob.decode('utf-8', 'replace')
        try:
            tree = ast.parse(text)
        except Exception:
            return None
        safe_modules = {'base64': base64, 'zlib': zlib, 'lzma': lzma, 'gzip': gzip, 'bz2': bz2, 'marshal': marshal}
        safe_env = {'__builtins__': {}, '__import__': lambda name, *a, **k: safe_modules[name]}
        env = dict(safe_env)
        for stmt in tree.body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name) and isinstance(stmt.value, ast.Lambda):
                try:
                    value = eval(compile(ast.Expression(stmt.value), '<xat-lambda>', 'eval'), env, env)
                    env[stmt.targets[0].id] = value
                except Exception:
                    pass
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                if isinstance(call.func, ast.Name) and call.func.id in {'exec', 'eval'} and call.args:
                    try:
                        payload = eval(compile(ast.Expression(call.args[0]), '<xat-exec>', 'eval'), env, env)
                    except Exception:
                        payload = None
                    if isinstance(payload, str):
                        return payload
                    if isinstance(payload, bytes):
                        return payload
                    if isinstance(payload, type((lambda: 0).__code__)):
                        try:
                            out = ast.unparse(ast.parse(payload.co_consts[0])) if payload.co_consts and isinstance(payload.co_consts[0], str) else None
                            if out:
                                return out
                        except Exception:
                            pass
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and (len(node.args) == 1):
                try:
                    payload = ast.literal_eval(node.args[0])
                except Exception:
                    continue
                if not isinstance(payload, str):
                    continue
                try:
                    raw = base64.b64decode(payload[::-1])
                    raw = zlib.decompress(raw)
                    raw = lzma.decompress(raw)
                    raw = gzip.decompress(raw)
                    raw = marshal.loads(raw)
                except Exception:
                    continue
                if isinstance(raw, bytes):
                    return raw
                if isinstance(raw, str):
                    return raw
        return None

    def f40(self, text):
        source_tree = ast.parse(text)
        tree = ast.parse(text)
        last = None
        now = text
        metadata = {}
        for _ in range(8):
            if now == last:
                break
            last = now
            tree = self.f50(tree)
            metadata = self.f23(tree)
            tree = Coreclass(metadata).visit(tree)
            tree = ast.fix_missing_locations(tree)
            now = ast.unparse(tree)
            tree = ast.parse(now)
        metadata = self.f23(tree)
        tree = self.f26(tree, metadata)
        tree = self.f48(tree, source_tree)
        tree = self.f29(tree)
        tree = self.f28(tree)
        tree = self.f49(tree)
        tree = self.f51(tree)
        now = ast.unparse(tree)
        return now

    def f48(self, tree, source_tree):
        defined = self.f35(tree)
        unresolved = {item.id for item in ast.walk(tree) if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load) and item.id not in defined}
        if not unresolved:
            return tree
        restore = []
        for stmt in source_tree.body:
            if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.Import, ast.ImportFrom)):
                targets = []
                if isinstance(stmt, ast.Assign):
                    for target in stmt.targets:
                        if isinstance(target, ast.Name):
                            targets.append(target.id)
                elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                    targets.append(stmt.target.id)
                elif isinstance(stmt, (ast.Import, ast.ImportFrom)):
                    for alias in stmt.names:
                        targets.append(alias.asname or alias.name.split('.')[-1])
                if any((name in unresolved for name in targets)):
                    restore.append(stmt)
        if restore:
            existing = []
            seen = set()
            for stmt in tree.body:
                key = None
                if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.Import, ast.ImportFrom)):
                    key = ast.unparse(stmt)
                if key and key not in seen:
                    seen.add(key)
                    existing.append(stmt)
                else:
                    existing.append(stmt)
            insert_at = 0
            while insert_at < len(existing) and isinstance(existing[insert_at], (ast.Import, ast.ImportFrom, ast.Assign, ast.AnnAssign, ast.Expr)) and not (isinstance(existing[insert_at], ast.FunctionDef) or isinstance(existing[insert_at], ast.ClassDef)):
                insert_at += 1
            tree.body = existing[:insert_at] + restore + existing[insert_at:]
        return tree

    def f49(self, tree):
        mapping = {}
        module_idx = 1
        value_idx = 1
        reserved = set(dir(builtins)) | {'self', 'cls', 'Path'}

        def needs_short(name):
            if not name or name in reserved:
                return False
            if name.startswith('__') and name.endswith('__'):
                return False
            if re.fullmatch(r'[fCmv]\d+', name):
                return False
            return (not name.isascii()) or len(name) > 16

        for node in ast.walk(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names:
                    bound = alias.asname or alias.name.split('.')[-1]
                    if needs_short(bound) and bound not in mapping:
                        mapping[bound] = f'm{module_idx}'
                        module_idx += 1

        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]:
                    if arg.arg not in {'self', 'cls'} and arg.arg not in mapping:
                        mapping[arg.arg] = f'v{value_idx}'
                        value_idx += 1
                for arg in [node.args.vararg, node.args.kwarg]:
                    if arg and arg.arg not in mapping:
                        mapping[arg.arg] = f'v{value_idx}'
                        value_idx += 1
            elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store) and node.id not in reserved and not re.fullmatch(r'[fCmv]\d+', node.id) and node.id not in mapping:
                mapping[node.id] = f'v{value_idx}'
                value_idx += 1
            elif isinstance(node, ast.ExceptHandler) and node.name and needs_short(node.name) and node.name not in mapping:
                mapping[node.name] = f'v{value_idx}'
                value_idx += 1

        if not mapping:
            return tree
        return ast.fix_missing_locations(Coreclass6(mapping).visit(tree))

    def f50(self, tree):
        cleaner = Coreclass()
        fresh = []
        i = 0
        while i < len(tree.body):
            stmt = tree.body[i]
            if (
                i + 1 < len(tree.body)
                and isinstance(stmt, ast.Assign)
                and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and isinstance(tree.body[i + 1], ast.While)
            ):
                name = stmt.targets[0].id
                try:
                    state = ast.literal_eval(stmt.value)
                except Exception:
                    fresh.append(stmt)
                    i += 1
                    continue
                loop = tree.body[i + 1]
                expanded = []
                seen = set()
                while state not in seen:
                    seen.add(state)
                    branch = cleaner.f6(loop.body, name, state)
                    if branch is None:
                        break
                    inner = branch.body
                    take = inner
                    for idx, item in enumerate(inner):
                        if isinstance(item, ast.If):
                            take = item.body
                            break
                    jump = None
                    for item in take:
                        if isinstance(item, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in item.targets):
                            try:
                                jump = ast.literal_eval(item.value)
                            except Exception:
                                jump = None
                            continue
                        if isinstance(item, ast.Pass):
                            continue
                        expanded.append(item)
                    if jump is None:
                        break
                    state = jump
                if expanded:
                    fresh.extend(expanded)
                    i += 2
                    continue
            fresh.append(stmt)
            i += 1
        tree.body = fresh
        return ast.fix_missing_locations(tree)

    def f51(self, tree):
        funcs = {}
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                funcs[node.name] = [arg.arg for arg in node.args.args]
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
                continue
            params = funcs.get(node.func.id)
            if not params:
                continue
            used = {kw.arg for kw in node.keywords if kw.arg}
            for kw in node.keywords:
                if not kw.arg or kw.arg in params:
                    continue
                candidates = [name for name in params[len(node.args):] if name not in used]
                if len(candidates) == 1:
                    kw.arg = candidates[0]
                    used.add(kw.arg)
        return ast.fix_missing_locations(tree)

class Coreclass3(ast.NodeTransformer):

    def __init__(self, mapping):
        self.mapping = mapping

    def f41(self, node):
        if isinstance(node.ctx, ast.Load) and node.id in self.mapping:
            return ast.copy_location(ast.Name(id=self.mapping[node.id], ctx=node.ctx), node)
        return node

    def visit_Name(self, node):
        return self.f41(node)

    def f15(self, node):
        return node

    def f16(self, node):
        return node

    def f17(self, node):
        return node

    def f42(self, node):
        return node

    def f43(self, node):
        return node

    def f44(self, node):
        return node

    def f45(self, node):
        return node

    def f46(self, node):
        return node

class Coreclass4(ast.NodeTransformer):

    def f22(self, node):
        node = self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == 'getattr' and (len(node.args) == 2) and (not node.keywords) and isinstance(node.args[1], ast.Constant) and isinstance(node.args[1].value, str) and node.args[1].value.isidentifier():
            return ast.copy_location(ast.Attribute(value=node.args[0], attr=node.args[1].value, ctx=ast.Load()), node)
        return node

    def visit_Call(self, node):
        return self.f22(node)

class Coreclass5(ast.NodeTransformer):

    def __init__(self, mapping):
        self.mapping = mapping

    def f17(self, node):
        if node.name in self.mapping:
            node.name = self.mapping[node.name]
        self.generic_visit(node)
        return node

    def f15(self, node):
        if node.name in self.mapping:
            node.name = self.mapping[node.name]
        self.generic_visit(node)
        return node

    def f16(self, node):
        if node.name in self.mapping:
            node.name = self.mapping[node.name]
        self.generic_visit(node)
        return node

    def f41(self, node):
        if node.id in self.mapping:
            node.id = self.mapping[node.id]
        return node

    def f47(self, node):
        self.generic_visit(node)
        if node.attr in self.mapping:
            node.attr = self.mapping[node.attr]
        return node

    def visit_ClassDef(self, node):
        return self.f17(node)

    def visit_FunctionDef(self, node):
        return self.f15(node)

    def visit_AsyncFunctionDef(self, node):
        return self.f16(node)

    def visit_Name(self, node):
        return self.f41(node)

    def visit_Attribute(self, node):
        return self.f47(node)

class Coreclass6(ast.NodeTransformer):

    def __init__(self, mapping):
        self.mapping = mapping

    def visit_Name(self, node):
        if node.id in self.mapping:
            node.id = self.mapping[node.id]
        return node

    def visit_arg(self, node):
        if node.arg in self.mapping:
            node.arg = self.mapping[node.arg]
        return node

    def visit_alias(self, node):
        bound = node.asname or node.name.split('.')[-1]
        if bound in self.mapping:
            node.asname = self.mapping[bound]
        return node

    def visit_ExceptHandler(self, node):
        if node.name in self.mapping:
            node.name = self.mapping[node.name]
        self.generic_visit(node)
        return node

def process_data_2(path):
    src = pathlib.Path(path)
    tool = Coreclass2()
    raw = tool.f38(src.read_bytes())
    clean = tool.f40(raw)
    for _ in range(3):
        peeled = tool.f38(clean)
        refined = tool.f40(peeled)
        if refined == clean:
            break
        clean = refined
    out = src.with_name(f'XAT_{src.stem}.py')
    out.write_text(clean, encoding='utf-8')
    return out

def process_data_4(paths):
    targets = []
    for item in paths:
        path = pathlib.Path(item.strip().strip('"'))
        if path.is_dir():
            targets.extend(sorted(p for p in path.glob('*.py') if not p.name.startswith('XAT_') and p.name != pathlib.Path(__file__).name))
        else:
            targets.append(path)
    outputs = []
    seen = set()
    for target in targets:
        target = target.resolve()
        if target in seen:
            continue
        seen.add(target)
        outputs.append(process_data_2(target))
    return outputs

def process_data_3():
    print_banner('Rendy')
    target = ''
    while not target:
        target = input('Введите путь к файлу или папке: ').strip().strip('"')
    targets = [target]
    outputs = process_data_4(targets)
    for out in outputs:
        print(f'deobfuscated: {out}')
    
if __name__ == '__main__':
    process_data_3()
