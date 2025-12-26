import tkinter as tk
from tkinter import messagebox
from fractions import Fraction
from decimal import Decimal, getcontext, Context, DivisionByZero
import ast, operator, math, sys
from PIL import Image, ImageTk  # pip install pillow

# ============================================================
#  THEMES
# ============================================================

LIGHT_THEME = {
    "bg_main": "#F5F5F7",
    "fg_display": "#333333",
    "icon_bg": "#E2E8F0",
    "icon_fg": "#1A202C",
    "window_bg": "#FFFFFF",
    "title_bg": "#CBD5E0",
    "title_fg": "#1A202C",
}

DARK_THEME = {
    "bg_main": "#101820",
    "fg_display": "#E2E8F0",
    "icon_bg": "#2D3748",
    "icon_fg": "#E2E8F0",
    "window_bg": "#1F2933",
    "title_bg": "#2D3748",
    "title_fg": "#E2E8F0",
}

# ============================================================
#  SICHERER EVAL (vereinfacht, aber solide)
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
#  APPS
# ============================================================

class CalculatorApp:
    def __init__(self, parent):
        self.frame = tk.Frame(parent, bg="#FFFFFF")

        self.display = tk.Entry(
            self.frame,
            font=("Helvetica", 22),
            bd=0,
            bg="#FFFFFF",
            fg="#000000",
            justify="right",
        )
        self.display.grid(row=0, column=0, columnspan=4, pady=10, padx=10, sticky="nsew")

        buttons = [
            ("7", 1, 0), ("8", 1, 1), ("9", 1, 2), ("/", 1, 3),
            ("4", 2, 0), ("5", 2, 1), ("6", 2, 2), ("*", 2, 3),
            ("1", 3, 0), ("2", 3, 1), ("3", 3, 2), ("-", 3, 3),
            ("0", 4, 0), (".", 4, 1), ("+", 4, 2), ("=", 4, 3),
        ]

        for (text, r, c) in buttons:
            tk.Button(
                self.frame,
                text=text,
                font=("Helvetica", 18),
                command=lambda t=text: self.on_button(t)
            ).grid(row=r, column=c, padx=5, pady=5, sticky="nsew")

        for r in range(5):
            self.frame.grid_rowconfigure(r, weight=1)
        for c in range(4):
            self.frame.grid_columnconfigure(c, weight=1)

    def on_button(self, char):
        if char == "=":
            expr = self.display.get().strip()
            if not expr:
                return
            mode = auto_detect_mode(expr)
            try:
                res = eval_expr(expr, mode=mode, precision=28)
            except (DivisionByZero, ZeroDivisionError):
                self.display.delete(0, tk.END)
                self.display.insert(0, "Fehler: /0")
            except EvalError as e:
                self.display.delete(0, tk.END)
                self.display.insert(0, f"ungültig")
            except Exception:
                self.display.delete(0, tk.END)
                self.display.insert(0, "Fehler")
            else:
                self.display.delete(0, tk.END)
                self.display.insert(0, str(res))
        else:
            self.display.insert(tk.END, char)

    def get_widget(self):
        return self.frame


class SettingsApp:
    def __init__(self, parent, os_reference):
        self.os = os_reference
        t = self.os.theme_data
        self.frame = tk.Frame(parent, bg=t["window_bg"])

        tk.Label(
            self.frame,
            text="Einstellungen",
            font=("Helvetica", 18, "bold"),
            bg=t["window_bg"],
            fg=t["fg_display"],
        ).pack(pady=10)

        tk.Label(
            self.frame,
            text="Design / Theme:",
            font=("Helvetica", 14),
            bg=t["window_bg"],
            fg=t["fg_display"],
        ).pack(pady=10)

        tk.Button(
            self.frame,
            text="🌙 Dunkelmodus aktivieren",
            font=("Helvetica", 14),
            command=lambda: self.os.set_theme("dark"),
        ).pack(pady=5)

        tk.Button(
            self.frame,
            text="☀ Hellmodus aktivieren",
            font=("Helvetica", 14),
            command=lambda: self.os.set_theme("light"),
        ).pack(pady=5)

        tk.Label(
            self.frame,
            text="\n(Theme wirkt auf Desktop, Fenster und Icons)",
            font=("Helvetica", 10),
            bg=t["window_bg"],
            fg=t["fg_display"],
        ).pack(pady=10)

    def get_widget(self):
        return self.frame


class TimerApp:
    def __init__(self, parent):
        self.frame = tk.Frame(parent, bg="#FFFFFF")
        self.time_var = tk.StringVar(value="10")

        tk.Label(
            self.frame,
            text="Timer (Sekunden):",
            font=("Helvetica", 16),
            bg="#FFFFFF",
        ).pack(pady=10)

        tk.Entry(
            self.frame,
            textvariable=self.time_var,
            font=("Helvetica", 20),
            justify="center",
        ).pack(pady=10)

        tk.Button(
            self.frame,
            text="Start",
            font=("Helvetica", 16),
            command=self.start_timer,
        ).pack(pady=10)

        self.output = tk.Label(
            self.frame,
            text="",
            font=("Helvetica", 20),
            bg="#FFFFFF",
        )
        self.output.pack(pady=10)

    def start_timer(self):
        try:
            seconds = int(self.time_var.get())
        except Exception:
            self.output.config(text="Ungültig")
            return
        self.countdown(seconds)

    def countdown(self, remaining):
        if remaining <= 0:
            self.output.config(text="Fertig!")
            return
        self.output.config(text=str(remaining))
        self.frame.after(1000, lambda: self.countdown(remaining - 1))

    def get_widget(self):
        return self.frame

# ============================================================
#  MINI-OS
# ============================================================

class MiniOS:
    def __init__(self, root):
        self.root = root
        self.root.title("MiniOS")
        self.root.geometry("900x600")

        self.theme = "light"
        self.theme_data = LIGHT_THEME

        self.wallpaper_image = None
        self.wallpaper_label = None

        self.desktop = tk.Frame(self.root, bg=self.theme_data["bg_main"])
        self.desktop.pack(fill="both", expand=True)

        self.root.after(200, lambda: self.load_wallpaper_safe("wallpaper.png"))

        self.build_icons()

    # ---------------- Theme ----------------

    def set_theme(self, mode):
        self.theme = mode
        self.theme_data = DARK_THEME if mode == "dark" else LIGHT_THEME
        self.apply_theme()

    def apply_theme(self):
        self.desktop.configure(bg=self.theme_data["bg_main"])

        # Wallpaper neu legen (damit Background stimmt)
        if self.wallpaper_label is not None:
            self.wallpaper_label.lift()

        # Icons neu aufbauen
        for child in self.desktop.winfo_children():
            child.destroy()
        if self.wallpaper_label is not None:
            self.wallpaper_label = None
            self.root.after(50, lambda: self.load_wallpaper_safe("wallpaper.png"))
        self.build_icons()

    # ---------------- Wallpaper ----------------

    def load_wallpaper_safe(self, path):
        try:
            self.load_wallpaper(path)
        except Exception:
            pass

    def load_wallpaper(self, path):
        self.root.update_idletasks()
        w = self.root.winfo_width()
        h = self.root.winfo_height()
        if w <= 1 or h <= 1:
            w, h = 900, 600

        img = Image.open(path)
        img = img.resize((w, h), Image.LANCZOS)
        self.wallpaper_image = ImageTk.PhotoImage(img)

        if self.wallpaper_label is None:
            self.wallpaper_label = tk.Label(self.desktop, image=self.wallpaper_image, bd=0)
            self.wallpaper_label.place(x=0, y=0, relwidth=1, relheight=1)
        else:
            self.wallpaper_label.configure(image=self.wallpaper_image)

        for child in self.desktop.winfo_children():
            child.lift()

    # ---------------- Icons ----------------

    def build_icons(self):
        apps = [
            ("Taschenrechner", self.open_calculator),
            ("Einstellungen", self.open_settings),
            ("Timer", self.open_timer),
        ]

        for i, (name, callback) in enumerate(apps):
            self.create_icon(name, i, 0, callback)

    def create_icon(self, name, row, col, callback):
        t = self.theme_data
        frame = tk.Frame(self.desktop, bg=t["bg_main"])
        frame.grid(row=row, column=col, padx=40, pady=40)

        btn = tk.Button(
            frame,
            text="📱",
            font=("Helvetica", 40),
            bg=t["icon_bg"],
            fg=t["icon_fg"],
            bd=0,
            command=callback,
            activebackground=t["icon_bg"],
            activeforeground=t["icon_fg"],
        )
        btn.pack()

        tk.Label(
            frame,
            text=name,
            bg=t["bg_main"],
            fg=t["fg_display"],
            font=("Helvetica", 12),
        ).pack()

    # ---------------- Fensterverwaltung ----------------

    def open_window(self, title):
        t = self.theme_data
        win = tk.Toplevel(self.root)
        win.title(title)
        win.geometry("400x500")
        win.configure(bg=t["window_bg"])

        titlebar = tk.Frame(win, bg=t["title_bg"], height=40)
        titlebar.pack(fill="x")

        label = tk.Label(
            titlebar,
            text=title,
            bg=t["title_bg"],
            fg=t["title_fg"],
            font=("Helvetica", 12, "bold"),
        )
        label.pack(side="left", padx=10)

        btn_close = tk.Button(
            titlebar,
            text="✖",
            bg=t["title_bg"],
            fg=t["title_fg"],
            bd=0,
            command=win.destroy,
        )
        btn_close.pack(side="right", padx=10)

        def start_move(event):
            win._drag_start_x = event.x
            win._drag_start_y = event.y

        def do_move(event):
            dx = event.x - win._drag_start_x
            dy = event.y - win._drag_start_y
            x = win.winfo_x() + dx
            y = win.winfo_y() + dy
            win.geometry(f"+{x}+{y}")

        titlebar.bind("<Button-1>", start_move)
        titlebar.bind("<B1-Motion>", do_move)

        content = tk.Frame(win, bg=t["window_bg"])
        content.pack(fill="both", expand=True)

        return content

    # ---------------- Apps ----------------

    def open_calculator(self):
        content = self.open_window("Taschenrechner")
        app = CalculatorApp(content)
        app.get_widget().pack(fill="both", expand=True)

    def open_settings(self):
        content = self.open_window("Einstellungen")
        app = SettingsApp(content, self)
        app.get_widget().pack(fill="both", expand=True)

    def open_timer(self):
        content = self.open_window("Timer")
        app = TimerApp(content)
        app.get_widget().pack(fill="both", expand=True)

# ============================================================
#  START
# ============================================================

def main():
    root = tk.Tk()
    MiniOS(root)
    root.mainloop()

if __name__ == "__main__":
    main()
