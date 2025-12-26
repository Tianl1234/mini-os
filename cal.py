import ast
import operator
import math
import sys
from decimal import Decimal, getcontext, Context, DivisionByZero
from fractions import Fraction

import tkinter as tk
from tkinter import ttk

# ============================================================
#  SICHERER AST-EVALUATOR
# ============================================================

OPS = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
    ast.FloorDiv: operator.floordiv,
    ast.Mod: operator.mod,
    ast.Pow: operator.pow,
    ast.USub: operator.neg,
    ast.UAdd: lambda x: x,
}

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
    return Decimal(str(value)) if not isinstance(value, float) else Decimal(repr(value))

def _to_fraction(value):
    if isinstance(value, Fraction):
        return value
    if isinstance(value, Decimal):
        tup = value.as_tuple()
        digits = 0
        for d in tup.digits:
            digits = digits * 10 + d
        exp = tup.exponent
        if exp >= 0:
            return Fraction(digits * (10 ** exp))
        else:
            return Fraction(digits, 10 ** (-exp))
    return Fraction(value)

def eval_expr(expr: str, mode: str = "float", precision: int | None = None):
    if mode not in ("float", "decimal", "fraction"):
        raise EvalError("Unbekannter Modus")

    ctx = None
    if mode == "decimal":
        if precision is None:
            precision = 28
        ctx = getcontext().copy()
        ctx.prec = int(precision)

    def convert_number(n):
        if mode == "float":
            return float(n)
        if mode == "fraction":
            return Fraction(n)
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

    def make_function(name):
        if name not in _MATH_FUNCS:
            raise EvalError(f"Unbekannte Funktion: {name}")
        func = _MATH_FUNCS[name]

        def wrapper(*args):
            if mode == "fraction":
                if name == "abs":
                    return abs(_to_fraction(args[0]))
                if name == "max":
                    return max(_to_fraction(a) for a in args)
                if name == "min":
                    return min(_to_fraction(a) for a in args)
                if name == "pow":
                    base, exp = (_to_fraction(a) for a in args)
                    if exp.denominator != 1:
                        raise EvalError("pow mit nicht-ganzzahligem Exponenten im Fraction-Modus nicht erlaubt")
                    return base ** int(exp)
                raise EvalError(f"Funktion {name} nicht im Fraction-Modus unterstützt")

            if mode == "decimal":
                if name == "sqrt":
                    try:
                        return ctx.sqrt(args[0])
                    except Exception:
                        return _to_decimal(math.sqrt(float(args[0])), ctx)
                if name in ("log", "ln"):
                    return _to_decimal(math.log(float(args[0])), ctx)
                if name in ("sin", "cos", "tan"):
                    return _to_decimal(func(float(args[0])), ctx)
                if name == "pow":
                    a, b = args
                    if isinstance(b, Decimal) and b == b.to_integral_value():
                        return a ** int(b)
                    return _to_decimal(math.pow(float(a), float(b)), ctx)
                if name in ("max", "min"):
                    return max(args)
                return _to_decimal(func(float(args[0])), ctx)

            return func(*[float(a) for a in args])

        return wrapper

    def _eval(node):
        if isinstance(node, ast.Constant):
            if isinstance(node.value, (int, float)):
                return convert_number(node.value)
            raise EvalError("Nur Zahlen als Konstanten erlaubt")

        if sys.version_info < (3, 8) and isinstance(node, ast.Num):
            return convert_number(node.n)

        if isinstance(node, ast.BinOp):
            op_type = type(node.op)
            if op_type not in OPS:
                raise EvalError("Nicht unterstützter Operator")
            left = _eval(node.left)
            right = _eval(node.right)
            func = OPS[op_type]
            try:
                return func(left, right)
            except ZeroDivisionError:
                raise
            except Exception as e:
                if mode == "decimal":
                    return func(_to_decimal(left, ctx), _to_decimal(right, ctx))
                if mode == "fraction":
                    return func(_to_fraction(left), _to_fraction(right))
                raise EvalError(str(e))

        if isinstance(node, ast.UnaryOp):
            op_type = type(node.op)
            if op_type not in OPS:
                raise EvalError("Nicht unterstützter Unary-Operator")
            return OPS[op_type](_eval(node.operand))

        if isinstance(node, ast.Call):
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

def auto_detect_mode(expr: str) -> str:
    expr = expr.replace(" ", "")

    if "." in expr:
        return "decimal"

    float_funcs = ("sin", "cos", "tan", "log", "ln", "sqrt")
    if any(f in expr for f in float_funcs):
        return "decimal"

    if "/" in expr and "//" not in expr:
        parts = expr.split("/")
        try:
            int(parts[0][-1])
            int(parts[1][0])
            return "fraction"
        except Exception:
            pass

    if all(ch.isdigit() or ch in "+-*/() " for ch in expr):
        return "fraction"

    return "float"


# ============================================================
#  MINI‑OS‑KOMPATIBLE VERSION DES TASCHENRECHNERS
# ============================================================

class CalculatorApp:
    def __init__(self, parent):
        self.root = parent  # kein Tk(), sondern Frame im Mini‑OS
        self.theme = "light"
        self.theme_data = LIGHT_THEME

        self.history = []
        self.history_window = None

        self.widgets_buttons = []
        self.widgets_misc = []

        self._build_layout()
        self.apply_theme()

    def _build_layout(self):
        t = self.theme_data

        top_frame = tk.Frame(self.root, bg=t["bg_main"])
        top_frame.grid(row=0, column=0, columnspan=4, sticky="nsew", padx=10, pady=(10, 0))

        self.display = tk.Entry(
            top_frame,
            font=("Helvetica", 30),
            bd=0,
            relief="flat",
            justify="right",
        )
        self.display.grid(row=0, column=0, columnspan=3, sticky="nsew", pady=(0, 5))

        self.theme_button = tk.Button(
            top_frame,
            text="☀",
            command=self.toggle_theme,
            bd=0,
            relief="flat",
            font=("Helvetica", 16),
            width=3,
        )
        self.theme_button.grid(row=0, column=3, sticky="ne", padx=(5, 0))

        self.mode_label = tk.Label(
            top_frame,
            text="Modus: auto",
            anchor="w",
            font=("Helvetica", 10),
        )
        self.mode_label.grid(row=1, column=0, columnspan=2, sticky="w", pady=(0, 10))

        self.history_button = tk.Button(
            top_frame,
            text="🕘 Verlauf",
            command=self.open_history_window,
            bd=0,
            relief="flat",
            font=("Helvetica", 10),
        )
        self.history_button.grid(row=1, column=2, columnspan=2, sticky="e")

        self.widgets_misc.extend([top_frame, self.display, self.theme_button,
                                  self.mode_label, self.history_button])

        btn_cfg = {
            "font": ("Helvetica", 20),
            "bd": 0,
            "relief": "flat",
            "width": 4,
            "height": 2,
            "borderwidth": 0,
        }

        buttons = [
            ("C", 1, 0, "clear"),
            ("←", 1, 1, "func"),
            ("(", 1, 2, "func"),
            (")", 1, 3, "func"),

            ("7", 2, 0, "num"),
            ("8", 2, 1, "num"),
            ("9", 2, 2, "num"),
            ("/", 2, 3, "op"),

            ("4", 3, 0, "num"),
            ("5", 3, 1, "num"),
            ("6", 3, 2, "num"),
            ("*", 3, 3, "op"),

            ("1", 4, 0, "num"),
            ("2", 4, 1, "num"),
            ("3", 4, 2, "num"),
            ("-", 4, 3, "op"),

            ("0", 5, 0, "num"),
            (".", 5, 1, "num"),
            ("+", 5, 2, "op"),
            ("=", 5, 3, "eq"),
        ]

        for (text, r, c, kind) in buttons:
            self._create_button(text, r, c, kind, btn_cfg)

        for r in range(1, 6):
            self.root.grid_rowconfigure(r, weight=1)
        for c in range(4):
            self.root.grid_columnconfigure(c, weight=1)

    def _create_button(self, text, row, col, kind, cfg):
        if text == "C":
            cmd = self.clear
        elif text == "←":
            cmd = self.backspace
        elif text == "=":
            cmd = self.calculate
        else:
            cmd = lambda t=text: self.insert_text(t)

        btn = tk.Button(self.root, text=text, command=cmd, **cfg)
        btn.grid(row=row, column=col, padx=6, pady=6, sticky="nsew")
        self.widgets_buttons.append((btn, kind))

    def apply_theme(self):
        t = self.theme_data

        for w in self.widgets_misc:
            if isinstance(w, tk.Frame):
                w.configure(bg=t["bg_main"])
            elif isinstance(w, tk.Entry):
                w.configure(bg=t["bg_display"], fg=t["fg_display"], insertbackground=t["fg_display"])
            elif isinstance(w, tk.Label):
                if w is self.mode_label:
                    w.configure(bg=t["bg_main"], fg=t["mode_label_fg"])
                else:
                    w.configure(bg=t["bg_main"], fg=t["fg_display_secondary"])
            elif isinstance(w, tk.Button):
                if w is self.theme_button:
                    w.configure(
                        bg=t["bg_main"],
                        fg=t["fg_display"],
                        activebackground=t["bg_main"],
                        activeforeground=t["fg_display"],
                    )
                elif w is self.history_button:
                    w.configure(
                        bg=t["bg_main"],
                        fg=t["fg_display_secondary"],
                        activebackground=t["bg_main"],
                        activeforeground=t["fg_display_secondary"],
                    )

        for btn, kind in self.widgets_buttons:
            if kind == "num":
                bg = t["btn_number_bg"]
                fg = t["btn_text"]
            elif kind == "op":
                bg = t["btn_op_bg"]
                fg = t["btn_text"]
            elif kind == "eq":
                bg = t["btn_eq_bg"]
                fg = t["btn_text_inverse"]
            elif kind == "clear":
                bg = t["btn_clear_bg"]
                fg = t["btn_text_inverse"]
            else:
                bg = t["btn_func_bg"]
                fg = t["btn_text"]

            btn.configure(
                bg=bg,
                fg=fg,
                activebackground=bg,
                activeforeground=fg,
            )

        if self.history_window is not None and tk.Toplevel.winfo_exists(self.history_window):
            self._apply_theme_to_history()

        self.theme_button.configure(text="☀" if self.theme == "light" else "🌙")

    def toggle_theme(self):
        self.theme = "dark" if self.theme == "light" else "light"
        self.theme_data = DARK_THEME if self.theme == "dark" else LIGHT_THEME
        self.apply_theme()

    def insert_text(self, text):
        if text == "^":
            text = "**"
        pos = self.display.index(tk.INSERT)
        self.display.insert(pos, text)

    def clear(self):
        self.display.delete(0, tk.END)
        self.mode_label.config(text="Modus: auto")

    def backspace(self):
        pos = self.display.index(tk.INSERT)
        if pos > 0:
            self.display.delete(pos - 1)

    def calculate(self):
        expr = self.display.get().strip()
        if not expr:
            return

        mode = auto_detect_mode(expr)
        self.mode_label.config(text=f"Modus: {mode}")

        try:
            res = eval_expr(expr, mode=mode, precision=28)
        except (DivisionByZero, ZeroDivisionError):
            self.display.delete(0, tk.END)
            self.display.insert(0, "Fehler: Division durch Null")
        except EvalError as e:
            self.display.delete(0, tk.END)
            self.display.insert(0, f"ungültig: {e}")
        except Exception:
            self.display.delete(0, tk.END)
            self.display.insert(0, "ungültig")
        else:
            result_str = str(res)
            self.history.append((expr, result_str, mode))
            self.update_history_listbox()

            self.display.delete(0, tk.END)
            self.display.insert(0, result_str)

        # ---------------- HISTORY ----------------

    def open_history_window(self):
        if self.history_window is not None and tk.Toplevel.winfo_exists(self.history_window):
            self.history_window.lift()
            return

        self.history_window = tk.Toplevel(self.root)
        self.history_window.title("Verlauf")
        self.history_window.resizable(False, False)

        self.history_listbox = tk.Listbox(self.history_window, font=("Helvetica", 11), height=15, width=40)
        self.history_listbox.pack(side="left", fill="both", expand=True)

        scrollbar = tk.Scrollbar(self.history_window, command=self.history_listbox.yview)
        scrollbar.pack(side="right", fill="y")
        self.history_listbox.config(yscrollcommand=scrollbar.set)

        self.history_listbox.bind("<Double-Button-1>", self.on_history_double_click)

        self._apply_theme_to_history()
        self.update_history_listbox()

    def _apply_theme_to_history(self):
        if self.history_window is None:
            return
        t = self.theme_data
        self.history_window.configure(bg=t["bg_main"])
        if hasattr(self, "history_listbox"):
            self.history_listbox.configure(
                bg=t["bg_display"],
                fg=t["fg_display"],
                selectbackground=t["btn_op_bg"],
                selectforeground=t["btn_text"],
                borderwidth=0,
                highlightthickness=0,
            )

    def update_history_listbox(self):
        if self.history_window is None or not tk.Toplevel.winfo_exists(self.history_window):
            return
        self.history_listbox.delete(0, tk.END)
        for expr, res, mode in self.history:
            self.history_listbox.insert(tk.END, f"[{mode}] {expr} = {res}")

    def on_history_double_click(self, event):
        selection = self.history_listbox.curselection()
        if not selection:
            return
        index = len(self.history) - 1 - selection[0]
        expr, res, mode = self.history[index]
        self.display.delete(0, tk.END)
        self.display.insert(0, expr)
        self.mode_label.config(text=f"Modus: {mode}")


# ============================================================
#  MINI‑OS START (anstelle von Tk() + mainloop())
# ============================================================

# Mini‑OS übergibt automatisch "parent"
app = CalculatorGUI(parent)
