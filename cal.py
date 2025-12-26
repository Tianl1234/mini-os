import ast
import operator
import math
import argparse
import sys
from decimal import Decimal, getcontext, Context, DivisionByZero
from fractions import Fraction

# Allowed operators mapping (we'll handle Pow specially)
OPS = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
    ast.FloorDiv: operator.floordiv,
    ast.Mod: operator.mod,
    # ast.Pow: operator.pow,  # handled explicitly
    ast.USub: operator.neg,
    ast.UAdd: lambda x: x,
}

# Whitelisted functions (names -> callable for float mode)
_MATH_FUNCS = {
    "sin": math.sin,
    "cos": math.cos,
    "tan": math.tan,
    "log": math.log,
    "ln": lambda x: math.log(x),
    "sqrt": math.sqrt,
    "abs": abs,
    "max": max,
    "min": min,
    "pow": math.pow,
}

# Named constants
_CONSTS = {
    "pi": math.pi,
    "e": math.e,
}


class EvalError(ValueError):
    pass


def _to_decimal(value, ctx: Context = None):
    if isinstance(value, Decimal):
        return value
    if isinstance(value, Fraction):
        return Decimal(value.numerator) / Decimal(value.denominator)
    # ints and floats
    # Use string conversion to avoid binary float artifacts
    return Decimal(str(value)) if not isinstance(value, float) else Decimal(repr(value))


def _to_fraction(value):
    if isinstance(value, Fraction):
        return value
    if isinstance(value, Decimal):
        # Fraction accepts Decimal in Python 3.11+, but to be safe use string
        try:
            return Fraction(str(value))
        except Exception:
            # fallback via as_tuple
            t = value.as_tuple()
            digits = 0
            for d in t.digits:
                digits = digits * 10 + d
            exp = t.exponent
            if exp >= 0:
                return Fraction(digits * (10 ** exp))
            else:
                return Fraction(digits, 10 ** (-exp))
    # ints and floats
    return Fraction(value)


def eval_expr(expr: str, mode: str = "float", precision: int | None = None):
    """
    Evaluate an arithmetic expression safely.
    mode: 'float' | 'decimal' | 'fraction'
    precision: number of decimal digits (only for decimal mode)
    """

    if mode not in ("float", "decimal", "fraction"):
        raise EvalError("Unbekannter Modus")

    ctx = None
    if mode == "decimal":
        if precision is None:
            precision = 28
        ctx = getcontext().copy()
        ctx.prec = int(precision)

    def convert_number(n):
        # n is an int or float
        if mode == "float":
            return float(n)
        if mode == "fraction":
            return Fraction(n)
        # decimal
        return _to_decimal(n, ctx)

    def convert_const(name):
        if name not in _CONSTS:
            raise EvalError(f"Unbekannter Name: {name}")
        val = _CONSTS[name]
        if mode == "float":
            return float(val)
        if mode == "fraction":
            return Fraction(val)
        return _to_decimal(val, ctx)

    # safe wrappers for whitelisted functions per mode
    def make_function(name):
        if name not in _MATH_FUNCS:
            raise EvalError(f"Unbekannte Funktion: {name}")
        func = _MATH_FUNCS[name]

        # Fraction mode: only allow a few functions with Fraction semantics
        if mode == "fraction":
            if name == "abs":
                return lambda *args: abs(_to_fraction(args[0]))
            if name in ("max", "min"):
                return lambda *args: getattr(__builtins__, name)(*[_to_fraction(a) for a in args])
            if name == "pow":
                def pow_frac(a, b):
                    a_f = _to_fraction(a)
                    b_f = _to_fraction(b)
                    if b_f.denominator != 1:
                        raise EvalError("pow mit nicht-ganzzahligem Exponenten in Fraction-Modus nicht erlaubt")
                    return a_f ** int(b_f)
                return pow_frac
            # others not supported
            raise EvalError(f"Funktion {name} nicht im Fraction-Modus unterstützt")

        # Decimal mode: convert args to Decimal where possible
        if mode == "decimal":
            if name == "sqrt":
                def sqrt_dec(a):
                    a_d = _to_decimal(a, ctx)
                    try:
                        return ctx.sqrt(a_d)
                    except Exception:
                        # fallback to float sqrt
                        return _to_decimal(math.sqrt(float(a_d)), ctx)
                return sqrt_dec

            if name in ("log", "ln"):
                return lambda a: _to_decimal(math.log(float(_to_decimal(a, ctx))), ctx)

            if name in ("sin", "cos", "tan"):
                return lambda a: _to_decimal(func(float(_to_decimal(a, ctx))), ctx)

            if name == "pow":
                def pow_dec(a, b):
                    a_d = _to_decimal(a, ctx)
                    b_d = _to_decimal(b, ctx)
                    # if exponent integral, use Decimal ** int
                    try:
                        if b_d == b_d.to_integral_value():
                            return a_d ** int(b_d)
                    except Exception:
                        pass
                    # fallback via float
                    return _to_decimal(math.pow(float(a_d), float(b_d)), ctx)
                return pow_dec

            if name in ("max", "min"):
                return lambda *args: getattr(__builtins__, name)(*[_to_decimal(a, ctx) for a in args])

            # default single-arg functions via float->Decimal
            return lambda *args: _to_decimal(func(*[float(_to_decimal(a, ctx)) for a in args]), ctx)

        # float mode
        return lambda *args: func(*[float(a) for a in args])

    def _eval(node):
        # Constants (py3.8+: ast.Constant, older: ast.Num)
        if isinstance(node, ast.Constant):
            if isinstance(node.value, (int, float)):
                return convert_number(node.value)
            raise EvalError("Nur Zahlen als Konstanten erlaubt")
        if sys.version_info < (3, 8) and isinstance(node, ast.Num):
            return convert_number(node.n)

        if isinstance(node, ast.BinOp):
            op_type = type(node.op)
            # Handle power separately for better control
            if op_type is ast.Pow:
                left = _eval(node.left)
                right = _eval(node.right)
                # Fraction mode: exponent must be integer
                if mode == "fraction":
                    l = _to_fraction(left)
                    r = _to_fraction(right)
                    if r.denominator != 1:
                        raise EvalError("pow mit nicht-ganzzahligem Exponenten in Fraction-Modus nicht erlaubt")
                    return l ** int(r)
                if mode == "decimal":
                    a_d = _to_decimal(left, ctx)
                    b_d = _to_decimal(right, ctx)
                    try:
                        if b_d == b_d.to_integral_value():
                            return a_d ** int(b_d)
                    except Exception:
                        pass
                    # fallback to math.pow
                    return _to_decimal(math.pow(float(a_d), float(b_d)), ctx)
                # float
                return math.pow(float(left), float(right))

            if op_type not in OPS:
                raise EvalError("Nicht unterstützter Operator")

            left = _eval(node.left)
            right = _eval(node.right)
            func = OPS[op_type]
            try:
                return func(left, right)
            except ZeroDivisionError:
                raise
            except Exception:
                # Try converting operands appropriately
                if mode == "decimal":
                    l = _to_decimal(left, ctx)
                    r = _to_decimal(right, ctx)
                    return func(l, r)
                if mode == "fraction":
                    l = _to_fraction(left)
                    r = _to_fraction(right)
                    return func(l, r)
                raise EvalError("Fehler bei Operation")

        if isinstance(node, ast.UnaryOp):
            op_type = type(node.op)
            if op_type not in OPS:
                raise EvalError("Nicht unterstützter Unary-Operator")
            val = _eval(node.operand)
            return OPS[op_type](val)

        if isinstance(node, ast.Call):
            # Only allow simple function calls like fname(arg, ...)
            if not isinstance(node.func, ast.Name):
                raise EvalError("Nur einfache Funktionsaufrufe erlaubt")
            fname = node.func.id
            func = make_function(fname)
            args = tuple(_eval(a) for a in node.args)
            return func(*args)

        if isinstance(node, ast.Name):
            return convert_const(node.id)

        raise EvalError("Ungültiger Ausdruck")

    try:
        tree = ast.parse(expr, mode="eval")
    except SyntaxError:
        raise EvalError("Syntaxfehler")

    if not isinstance(tree, ast.Expression):
        raise EvalError("Nur Ausdrücke erlaubt")

    return _eval(tree.body)


def main():
    parser = argparse.ArgumentParser(description="Sicherer Taschenrechner (AST-basiert)")
    parser.add_argument("--mode", choices=("float", "decimal", "fraction"), default="float", help="numeric mode")
    parser.add_argument("--precision", type=int, default=28, help="decimal precision (only for decimal mode)")
    args = parser.parse_args()

    mode = args.mode
    precision = args.precision if mode == "decimal" else None

    try:
        import readline  # optional: improves interactive input
    except Exception:
        pass

    while True:
        try:
            i = input(f"[{mode}] Rechnung (oder Enter zum Beenden): ")
        except (EOFError, KeyboardInterrupt):
            print()
            break
        if not i.strip():
            break
        try:
            res = eval_expr(i, mode=mode, precision=precision)
        except DivisionByZero:
            print("Fehler: Division durch Null")
        except ZeroDivisionError:
            print("Fehler: Division durch Null")
        except EvalError as e:
            print(f"ungültig: {e}")
        except Exception:
            print("ungültig")
        else:
            print(res)


if __name__ == "__main__":
    main()
