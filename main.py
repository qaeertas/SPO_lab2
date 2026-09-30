#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
========================================================================================
Лабораторная работа: Расчет метрик Джилба и Маккейба (TypeScript / JavaScript Analyzer)
Полностью динамический анализатор сложности кода на Python (Tkinter)
========================================================================================
"""

import os
import re
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
from typing import List, Dict, Any, Tuple

SAMPLE_TS_CODE = """type OrderDetails = {
    UserStatus: string;
    OrderAmount: number;
    PromoCode: string;
};

function calculateDiscount(order: OrderDetails): number {
    let discount = 0.0;
    for (let attempt = 1; attempt <= 2; attempt++) {
        if (order.OrderAmount > 0) {
            switch (order.UserStatus) {
                case "VIP": {
                    let activityCounter = 0;
                    for (let i = 1; i <= 3; i++) {
                        activityCounter = activityCounter + i;
                    }

                    if (order.OrderAmount > 1000.0) {
                        if (order.PromoCode === "ULTRA") {
                            discount = 0.35;
                        } else {
                            discount = 0.25;
                        }
                    } else if (order.OrderAmount > 500.0) {
                        discount = 0.20;
                    } else {
                        discount = 0.15;
                    }
                    break;
                }

                case "Registered": {
                    let retries = 3;
                    while (retries > 0) {
                        retries = retries - 1;
                        if (order.OrderAmount > 750.0) {
                            if (order.PromoCode === "PROMO10") {
                                discount = 0.10;
                            } else {
                                discount = 0.05;
                            }
                        } else {
                            discount = 0.0;
                        }
                    }
                    break;
                }

                case "Guest":
                    if (order.PromoCode === "WELCOME5") {
                        discount = 0.05;
                    } else {
                        discount = 0.0;
                    }
                    break;

                default:
                    discount = 0.0;
            }
        }
    }
    return discount;
}

const vipOrder: OrderDetails = {
    UserStatus: "VIP",
    OrderAmount: 1200.0,
    PromoCode: "ULTRA"
};

const discount = calculateDiscount(vipOrder);
console.log("Детали заказа:", vipOrder);
console.log(`Рассчитанная скидка: ${discount}`);
"""


def strip_comments_keep_layout(code: str) -> str:
    """Удаляет однострочные // и многострочные /* */ комментарии."""

    def repl(m):
        return '\n' * m.group(0).count('\n')

    clean = re.sub(r'/\*.*?\*/', repl, code, flags=re.DOTALL)
    clean = re.sub(r'//[^\n]*', '', clean)
    return clean


class TsControlFlowAnalyzer:
    class Result:
        def __init__(self, mc_cabe: int, jilb_cl: int, jilb_cl_rel: float, jilb_cli: int, sa: int, so: float,
                     classic_ops: List[str], ast_text: str, source_lines: List[str],
                     cl_details: List[Tuple[str, int, int, str]]):
            self.mc_cabe = mc_cabe
            self.jilb_cl = jilb_cl
            self.jilb_cl_rel = jilb_cl_rel
            self.jilb_cli = jilb_cli
            self.sa = sa
            self.so = so
            self.classic_ops = classic_ops
            self.ast_text = ast_text
            self.source_lines = source_lines
            self.cl_details = cl_details

    @classmethod
    def analyze(cls, code: str) -> Result:
        if not code or not code.strip():
            return cls.Result(1, 0, 0.0, 0, 0, 0.0, [], "", [], [])

        clean_code = strip_comments_keep_layout(code)
        lines = clean_code.splitlines()
        raw_lines = code.splitlines()

        control_items = []
        classic_ops = []
        ast_nodes = []

        # Стек областей видимости для расчета уровня вложенности (CLI)
        scope_stack = [{'type': 'ROOT', 'depth': 0}]
        switch_stack = []

        pat_for = re.compile(r'\bfor\s*\((.*?)\)')
        pat_while = re.compile(r'\bwhile\s*\((.*?)\)')
        pat_do = re.compile(r'\bdo\b')
        pat_if = re.compile(r'(?<!else\s)\bif\s*\((.*?)\)')
        pat_elif = re.compile(r'\belse\s+if\s*\((.*?)\)')
        pat_switch = re.compile(r'\bswitch\s*\((.*?)\)')
        pat_case = re.compile(r'\bcase\s+([^:]+):')
        pat_default = re.compile(r'\bdefault\s*:')
        pat_var = re.compile(r'\b(?:let|const|var)\s+([A-Za-z0-9_]+)')
        pat_func = re.compile(r'\bfunction\s+([A-Za-z0-9_]+)')
        pat_return = re.compile(r'\breturn\b')

        for idx, (clean_line, raw_line) in enumerate(zip(lines, raw_lines)):
            line_no = idx + 1
            s = clean_line.strip()
            raw_s = raw_line.strip()
            if not s:
                continue

            # Пропуск объявлений типов/интерфейсов
            if re.match(r'^(type|interface|export\s+type|export\s+interface)\b', s):
                continue

            # Обработка закрывающих скобок
            while s.startswith('}'):
                if len(scope_stack) > 1:
                    popped = scope_stack.pop()
                    if popped['type'] == 'SWITCH' and switch_stack:
                        switch_stack.pop()
                s = s[1:].strip()

            if not s:
                continue

            cur_depth = scope_stack[-1]['depth']

            # 1. Функция
            m_func = pat_func.search(s)
            if m_func:
                classic_ops.append(f"function {m_func.group(1)}(...)")
                scope_stack.append({'type': 'FUNC', 'depth': 0})
                ast_nodes.append((0, f"Function: {m_func.group(1)}", line_no))
                continue

            # 2. Цикл for
            m_for = pat_for.search(s)
            if m_for:
                depth = cur_depth
                control_items.append((raw_s, 1, line_no, depth, "Цикл for"))
                classic_ops.append(raw_s)
                scope_stack.append({'type': 'FOR', 'depth': depth + 1})
                ast_nodes.append((depth, f"ForStatement [CLI={depth}]: ({m_for.group(1).strip()})", line_no))
                continue

            # 3. Цикл while
            m_while = pat_while.search(s)
            if m_while and not re.search(r'^\s*\}\s*while', clean_line):
                depth = cur_depth
                control_items.append((raw_s, 1, line_no, depth, "Цикл while"))
                classic_ops.append(raw_s)
                scope_stack.append({'type': 'WHILE', 'depth': depth + 1})
                ast_nodes.append((depth, f"WhileStatement [CLI={depth}]: ({m_while.group(1).strip()})", line_no))
                continue

            # 4. Цикл do..while
            if pat_do.search(s) and not pat_while.search(s):
                depth = cur_depth
                control_items.append((raw_s, 1, line_no, depth, "Цикл do..while"))
                classic_ops.append(raw_s)
                scope_stack.append({'type': 'DO', 'depth': depth + 1})
                ast_nodes.append((depth, f"DoWhileStatement [CLI={depth}]", line_no))
                continue

            # 5. Оператор switch
            m_sw = pat_switch.search(s)
            if m_sw:
                classic_ops.append(raw_s)
                switch_stack.append({'base_depth': cur_depth, 'cases_count': 0})
                scope_stack.append({'type': 'SWITCH', 'depth': cur_depth})
                ast_nodes.append((cur_depth, f"SwitchStatement: ({m_sw.group(1).strip()})", line_no))
                continue

            # 6. Ветка case (рассматривается как вложенный if)
            m_case = pat_case.search(s)
            if m_case:
                case_val = m_case.group(1).strip()
                if switch_stack:
                    switch_stack[-1]['cases_count'] += 1
                    case_depth = switch_stack[-1]['base_depth'] + (switch_stack[-1]['cases_count'] - 1) + 1
                else:
                    case_depth = cur_depth + 1
                control_items.append((raw_s, 1, line_no, case_depth, f"Ветка case {case_val}"))
                classic_ops.append(raw_s)
                scope_stack[-1]['depth'] = case_depth + 1
                ast_nodes.append((case_depth, f"CaseClause [CLI={case_depth}]: {case_val}", line_no))
                continue

            # 7. Ветка default
            if pat_default.search(s):
                if switch_stack:
                    def_depth = switch_stack[-1]['base_depth'] + switch_stack[-1]['cases_count']
                else:
                    def_depth = cur_depth
                classic_ops.append(raw_s)
                scope_stack[-1]['depth'] = def_depth
                ast_nodes.append((def_depth, f"DefaultClause [CLI={def_depth}]", line_no))
                continue

            # 8. Ветка else if
            m_elif = pat_elif.search(s)
            if m_elif:
                depth = cur_depth - 1 if cur_depth > 0 else 0
                control_items.append((raw_s, 1, line_no, depth, "Ветка else if"))
                classic_ops.append(raw_s)
                scope_stack.append({'type': 'IF', 'depth': depth + 1})
                ast_nodes.append((depth, f"ElseIfStatement [CLI={depth}]: ({m_elif.group(1).strip()})", line_no))
                continue

            # 9. Ветка else
            if re.match(r'^else\b', s):
                scope_stack.append({'type': 'ELSE', 'depth': cur_depth})
                continue

            # 10. Оператор if
            m_if = pat_if.search(s)
            if m_if:
                depth = cur_depth
                control_items.append((raw_s, 1, line_no, depth, "Оператор if"))
                classic_ops.append(raw_s)
                scope_stack.append({'type': 'IF', 'depth': depth + 1})
                ast_nodes.append((depth, f"IfStatement [CLI={depth}]: ({m_if.group(1).strip()})", line_no))
                continue

            # 11. Объявление переменных
            if pat_var.search(s):
                classic_ops.append(raw_s)
                ast_nodes.append((cur_depth, f"VariableDeclaration: {raw_s[:40]}", line_no))
                if '{' in s and not s.endswith('}'):
                    scope_stack.append({'type': 'BLOCK', 'depth': cur_depth})
                continue

            # 12. Оператор return
            if pat_return.search(s):
                classic_ops.append(raw_s)
                ast_nodes.append((cur_depth, f"ReturnStatement: {raw_s}", line_no))
                continue

            # 13. Выражения / присваивания / вызовы функций
            if re.search(r'(?:\+\+|--|\+=|-=|\*=|/=|%=|=|\bconsole\.log\b|\bMath\.)', s):
                parts = [p.strip() for p in raw_s.split(';') if p.strip()]
                for p in parts:
                    if p not in ('break', 'continue') and not p.startswith('//'):
                        classic_ops.append(p + (';' if not p.endswith(';') else ''))
                ast_nodes.append((cur_depth, f"Expression: {raw_s[:40]}", line_no))
                if '{' in s and not s.endswith('}'):
                    scope_stack.append({'type': 'BLOCK', 'depth': cur_depth})
                continue

            if '{' in s and not s.endswith('}'):
                scope_stack.append({'type': 'BLOCK', 'depth': cur_depth})

        # Динамический расчет метрик
        jilb_cl = len(control_items)
        mc_cabe = jilb_cl + 1
        n_ops = len(classic_ops)
        jilb_cl_rel = (jilb_cl / n_ops) if n_ops > 0 else 0.0
        jilb_cli = max((item[3] for item in control_items), default=0)

        # Граничные метрики Sa, So
        sa = jilb_cl * 2 + (n_ops - jilb_cl)
        so = (1.0 - (float(n_ops - 1) / sa)) if sa > 0 and n_ops > 1 else 0.0
        if so < 0:
            so = 0.0

        # Построение дерева AST
        ast_lines = ["Root: Module (TypeScript)"]
        for depth, text, l_no in ast_nodes:
            indent = "  " * (depth + 1)
            ast_lines.append(f"{indent}├── [Line {l_no:2d}] {text}")

        ast_text = "\n".join(ast_lines)
        source_lines = [f"{i + 1, 3}: {l.strip()}" for i, l in enumerate(raw_lines)]
        cl_details = [(item[0], item[1], item[2], item[4]) for item in control_items]

        return cls.Result(mc_cabe, jilb_cl, jilb_cl_rel, jilb_cli, sa, so, classic_ops, ast_text, source_lines,
                          cl_details)


class GilbParserApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Метрики Джилба и Маккейба — TypeScript Analyzer")
        self.root.geometry("1100x750")
        self.root.minsize(900, 600)

        self._build_ui()
        self.load_sample()

    def _build_ui(self):
        # 1. Панель кнопок (аналог C# Form1)
        top_panel = ttk.Frame(self.root, padding=(8, 6))
        top_panel.pack(fill=tk.X, side=tk.TOP)

        ttk.Button(top_panel, text="Открыть файл…", command=self.open_file).pack(side=tk.LEFT, padx=3)
        ttk.Button(top_panel, text="Загрузить пример", command=self.load_sample).pack(side=tk.LEFT, padx=3)

        btn_analyze = tk.Button(
            top_panel,
            text="Анализировать",
            bg="#2563eb",
            fg="white",
            font=("Arial", 9, "bold"),
            relief=tk.RAISED,
            padx=10,
            command=self.analyze
        )
        btn_analyze.pack(side=tk.LEFT, padx=6)

        ttk.Button(top_panel, text="Показать AST", command=self.show_ast_dialog).pack(side=tk.LEFT, padx=3)
        ttk.Button(top_panel, text="Экспорт метрик", command=self.export_metrics).pack(side=tk.LEFT, padx=3)
        ttk.Button(top_panel, text="Операторы (N)", command=self.show_ops_dialog).pack(side=tk.LEFT, padx=3)

        # 2. Основная рабочая область
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=8, pady=6)

        # Левая часть: Редактор кода
        left_frame = ttk.LabelFrame(main_paned, text=" Исходный код TypeScript (Редактируемый в реальном времени) ",
                                    padding=4)
        main_paned.add(left_frame, weight=3)

        self.rich_code = scrolledtext.ScrolledText(
            left_frame,
            wrap=tk.NONE,
            font=("Consolas", 10),
            undo=True,
            bg="#ffffff",
            fg="#0f172a",
            insertbackground="#2563eb",
            padx=6,
            pady=6
        )
        self.rich_code.pack(fill=tk.BOTH, expand=True)
        self.rich_code.bind("<KeyRelease>", lambda e: self._on_code_change())

        # Правая часть: Метрики потока управления
        right_frame = ttk.LabelFrame(main_paned, text=" Метрики потока управления ", padding=8)
        main_paned.add(right_frame, weight=2)

        self.lbl_mccabe = ttk.Label(right_frame, text="Метрика Маккейба Z(G): 0", font=("Arial", 11, "bold"),
                                    foreground="#1e3a8a")
        self.lbl_mccabe.pack(anchor=tk.W, pady=6)

        self.lbl_jilb_cl_big = ttk.Label(right_frame, text="Метрика Джилба CL: 0", font=("Arial", 11, "bold"),
                                         foreground="#0e7490")
        self.lbl_jilb_cl_big.pack(anchor=tk.W, pady=6)

        self.lbl_jilb_cl = ttk.Label(right_frame, text="Метрика Джилба cl: 0.000", font=("Arial", 11, "bold"),
                                     foreground="#047857")
        self.lbl_jilb_cl.pack(anchor=tk.W, pady=6)

        self.lbl_jilb_cli = ttk.Label(right_frame, text="Метрика Джилба CLI: 0", font=("Arial", 11, "bold"),
                                      foreground="#b91c1c")
        self.lbl_jilb_cli.pack(anchor=tk.W, pady=6)

        self.lbl_sa = ttk.Label(right_frame, text="Sa (абсолютное): 0", font=("Arial", 10), foreground="#334155")
        self.lbl_sa.pack(anchor=tk.W, pady=4)

        self.lbl_so = ttk.Label(right_frame, text="So (относительное): 0.000", font=("Arial", 10), foreground="#334155")
        self.lbl_so.pack(anchor=tk.W, pady=4)

        ttk.Separator(right_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=8)

        lbl_tbl_title = ttk.Label(right_frame, text="Операторы абсолютной сложности (CL):", font=("Arial", 9, "bold"))
        lbl_tbl_title.pack(anchor=tk.W, pady=2)

        tbl_scroll = ttk.Scrollbar(right_frame, orient=tk.VERTICAL)
        self.tree_cl = ttk.Treeview(right_frame, columns=("op", "val"), show="headings", height=8,
                                    yscrollcommand=tbl_scroll.set)
        tbl_scroll.config(command=self.tree_cl.yview)
        tbl_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.tree_cl.heading("op", text="Оператор")
        self.tree_cl.heading("val", text="Значение")
        self.tree_cl.column("op", width=240, anchor="w")
        self.tree_cl.column("val", width=70, anchor="center")
        self.tree_cl.pack(fill=tk.BOTH, expand=True)

        self.status_bar = ttk.Label(self.root, text="Готов к работе", relief=tk.SUNKEN, anchor=tk.W, padding=(6, 2))
        self.status_bar.pack(fill=tk.X, side=tk.BOTTOM)

        self.current_result = None

    def _on_code_change(self):
        code = self.rich_code.get("1.0", tk.END)
        lines = len(code.splitlines())
        self.status_bar.config(text=f"Код изменен (строк: {lines}). Нажмите 'Анализировать' для пересчета метрик.")

    def load_sample(self):
        self.rich_code.delete("1.0", tk.END)
        self.rich_code.insert("1.0", SAMPLE_TS_CODE.strip())
        self.status_bar.config(text=f"Загружен пример TypeScript ({len(SAMPLE_TS_CODE.splitlines())} строк)")
        self.analyze()

    def open_file(self):
        path = filedialog.askopenfilename(filetypes=[("TypeScript / JavaScript", "*.ts *.js"), ("All files", "*.*")])
        if path:
            try:
                with open(path, "r", encoding="utf-8") as f:
                    content = f.read()
            except:
                with open(path, "r", encoding="cp1251") as f:
                    content = f.read()
            self.rich_code.delete("1.0", tk.END)
            self.rich_code.insert("1.0", content)
            self.status_bar.config(text=f"Загружен файл: {path}")
            self.analyze()

    def analyze(self):
        # Чтение текущего текста из формы
        code = self.rich_code.get("1.0", tk.END)
        if not code.strip():
            messagebox.showwarning("Предупреждение", "Код для анализа пуст.")
            return

        # Запуск динамического анализа
        self.current_result = TsControlFlowAnalyzer.analyze(code)
        res = self.current_result

        # Обновление всех меток
        self.lbl_mccabe.config(text=f"Метрика Маккейба Z(G): {res.mc_cabe}")
        self.lbl_jilb_cl_big.config(text=f"Метрика Джилба CL: {res.jilb_cl}")
        self.lbl_jilb_cl.config(text=f"Метрика Джилба cl: {res.jilb_cl_rel:.3f}")
        self.lbl_jilb_cli.config(text=f"Метрика Джилба CLI: {res.jilb_cli}")
        self.lbl_sa.config(text=f"Sa (абсолютное): {res.sa}")
        self.lbl_so.config(text=f"So (относительное): {res.so:.3f}")

        # Обновление таблицы CL
        for it in self.tree_cl.get_children():
            self.tree_cl.delete(it)

        for op_name, val, line_no, desc in res.cl_details:
            self.tree_cl.insert("", tk.END, values=(op_name, val))

        self.status_bar.config(
            text=f"Анализ завершен: Z(G)={res.mc_cabe}, CL={res.jilb_cl}, cl={res.jilb_cl_rel:.3f}, CLI={res.jilb_cli}, N={len(res.classic_ops)}, Sa={res.sa}, So={res.so:.3f}")

    def show_ops_dialog(self):
        self.analyze()
        ops = self.current_result.classic_ops
        preview = "\n".join(f"{i + 1:2d}. {op}" for i, op in enumerate(ops))

        dialog = tk.Toplevel(self.root)
        dialog.title(f"Операторы (N={len(ops)})")
        dialog.geometry("600x500")

        txt = scrolledtext.ScrolledText(dialog, wrap=tk.NONE, font=("Consolas", 9), padx=6, pady=6)
        txt.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        txt.insert("1.0", f"Список операторов программы для расчета cl (N = {len(ops)}):\n\n" + preview)
        txt.config(state=tk.DISABLED)

        btn_close = ttk.Button(dialog, text="Закрыть", command=dialog.destroy)
        btn_close.pack(pady=4)

    def show_ast_dialog(self):
        self.analyze()
        res = self.current_result
        full_info = "ИСХОДНЫЙ КОД:\n" + "\n".join(
            res.source_lines) + "\n\nAST С НОМЕРАМИ СТРОК И УРОВНЯМИ ВЛОЖЕННОСТИ:\n" + res.ast_text

        dialog = tk.Toplevel(self.root)
        dialog.title("AST с номерами строк и блок-структурой")
        dialog.geometry("800x600")

        txt = scrolledtext.ScrolledText(dialog, wrap=tk.NONE, font=("Consolas", 9), padx=6, pady=6)
        txt.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        txt.insert("1.0", full_info)
        txt.config(state=tk.DISABLED)

        btn_close = ttk.Button(dialog, text="Закрыть", command=dialog.destroy)
        btn_close.pack(pady=4)

    def export_metrics(self):
        self.analyze()
        path = filedialog.asksaveasfilename(defaultextension=".txt",
                                            filetypes=[("Text file", "*.txt"), ("CSV file", "*.csv"),
                                                       ("All files", "*.*")])
        if path:
            res = self.current_result
            lines = [
                "Метрики потока управления:",
                f"Метрика Маккейба Z(G): {res.mc_cabe}",
                f"Метрика Джилба CL: {res.jilb_cl}",
                f"Метрика Джилба cl: {res.jilb_cl_rel:.3f}",
                f"Метрика Джилба CLI: {res.jilb_cli}",
                f"Sa (абсолютное): {res.sa}",
                f"So (относительное): {res.so:.3f}",
                "",
                f"Операторы cl (N={len(res.classic_ops)}):"
            ]
            for op in res.classic_ops:
                lines.append(" - " + op)
            lines.append("")

            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines))
            messagebox.showinfo("Экспорт", f"Метрики успешно сохранены в файл:\n{path}")


if __name__ == "__main__":
    root = tk.Tk()
    app = GilbParserApp(root)
    root.mainloop()