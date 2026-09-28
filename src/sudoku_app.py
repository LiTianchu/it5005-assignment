"""Streamlit interface for the assignment's Sudoku reasoners."""

from collections import defaultdict, deque
from html import escape
import json
from pathlib import Path
from time import perf_counter

import streamlit as st

from logic_ import parse_definite_clause
from sudoku_solver import (
    atom, build_definite_kb, build_general_kb, solve_full_grid_fc,
    solve_full_grid_bc, pl_bc_entails,
)


def show_board(n, box_h, box_w, givens, solution=None):
    """Render clues, blanks, and solved cells with distinct styles."""
    solution = solution or {}
    rows = []
    for r in range(1, n + 1):
        cells = []
        for c in range(1, n + 1):
            clue = (r, c) in givens
            value = givens.get((r, c), solution.get((r, c)))
            kind = "given" if clue else "inferred" if value is not None else "empty"
            edges = ""
            if (c - 1) % box_w == 0:
                edges += "border-left:3px solid #334155;"
            if c == n:
                edges += "border-right:3px solid #334155;"
            if (r - 1) % box_h == 0:
                edges += "border-top:3px solid #334155;"
            if r == n:
                edges += "border-bottom:3px solid #334155;"
            label = f"Row {r}, column {c}: {value if value is not None else 'empty'}"
            content = "&nbsp;" if value is None else escape(str(value))
            cells.append(
                f'<td class="{kind}" style="{edges}" aria-label="{escape(label)}">'
                f"{content}</td>"
            )
        rows.append("<tr>" + "".join(cells) + "</tr>")
    st.markdown(
        '<table class="sudoku-board" aria-label="Sudoku board"><tbody>'
        + "".join(rows) + "</tbody></table>",
        unsafe_allow_html=True,
    )


def describe_rule(premises, conclusion):
    """Explain the rule using cell positions and Sudoku constraints."""
    name = conclusion.op
    if name.startswith("Not"):
        r, c, v = map(int, name[3:].split("_"))
        if len(premises) == 1 and premises[0].op.startswith("Is"):
            pr, pc, pv = map(int, premises[0].op[2:].split("_"))
            if (pr, pc) == (r, c):
                return f"Eliminate {v} from row {r}, column {c}: that cell contains {pv}."
            if pr == r:
                reason = f"row {r} contains {v} at column {pc}"
            elif pc == c:
                reason = f"column {c} contains {v} at row {pr}"
            else:
                reason = f"its box contains {v} at row {pr}, column {pc}"
            return f"Eliminate {v} from row {r}, column {c}: {reason}."
    if name.startswith("Is"):
        r, c, v = map(int, name[2:].split("_"))
        if premises:
            return f"Place {v} in row {r}, column {c}: all other values were eliminated."
        return f"Given clue: row {r}, column {c} contains {v}."
    return f"Infer {name}."


def proof_steps(kb, query):
    """Record forward rule firings and retain the steps needed for this query."""
    facts, origins, agenda = set(), {}, deque()
    rules, waiting, remaining = [], defaultdict(list), []
    for clause in kb.clauses:
        premises, conclusion = parse_definite_clause(clause)
        premises = tuple(dict.fromkeys(premises))
        if not premises:
            if conclusion not in facts:
                facts.add(conclusion)
                origins[conclusion] = ((), conclusion)
                agenda.append(conclusion)
            continue
        index = len(rules)
        rules.append((premises, conclusion))
        remaining.append(len(premises))
        for premise in premises:
            waiting[premise].append(index)

    while agenda and query not in facts:
        fact = agenda.popleft()
        for index in waiting[fact]:
            remaining[index] -= 1
            if remaining[index] == 0:
                premises, conclusion = rules[index]
                if conclusion not in facts:
                    facts.add(conclusion)
                    origins[conclusion] = (premises, conclusion)
                    agenda.append(conclusion)
    if query not in facts:
        return []

    steps, seen = [], set()

    def collect(fact):
        if fact in seen:
            return
        seen.add(fact)
        premises, conclusion = origins[fact]
        for premise in premises:
            collect(premise)
        steps.append(describe_rule(premises, conclusion))

    collect(query)
    return steps


st.set_page_config(page_title="Sudoku Solver", layout="centered")
st.markdown(
    """<style>
    .sudoku-board { border-collapse: collapse; margin: 1rem auto; }
    .sudoku-board td { width: 2.6rem; height: 2.6rem; text-align: center;
        border: 1px solid #94a3b8; font-size: 1.2rem; }
    .sudoku-board .given { font-weight: 800; background: #e2e8f0; color: #0f172a; }
    .sudoku-board .inferred { font-weight: 600; color: #1d4ed8; background: #eff6ff; }
    .sudoku-board .empty { background: #f8fafc; }
    </style>""",
    unsafe_allow_html=True,
)
st.title("Sudoku Solver")

with (Path(__file__).resolve().parent / "puzzles.json").open(encoding="utf-8") as file:
    pool = json.load(file)
n, box_h, box_w = pool["n"], pool["box_h"], pool["box_w"]
puzzles = pool["puzzles"]
puzzle_index = st.selectbox(
    "Choose a puzzle", range(len(puzzles)),
    format_func=lambda i: f"Puzzle {i + 1} ({len(puzzles[i]['givens'])} givens)",
)
givens = {
    tuple(map(int, cell.split("_"))): value
    for cell, value in puzzles[puzzle_index]["givens"].items()
}

st.subheader("Puzzle")
st.caption("Bold gray cells are given clues; blue cells are inferred values.")
show_board(n, box_h, box_w, givens)

st.subheader("Solve the full grid")
algorithm = st.radio("Algorithm", ("Forward chaining", "Backward chaining"), horizontal=True)
if st.button("Solve puzzle", type="primary"):
    solver = solve_full_grid_fc if algorithm == "Forward chaining" else solve_full_grid_bc
    started = perf_counter()
    try:
        with st.spinner(f"Solving with {algorithm.lower()}..."):
            solution = solver(n, box_h, box_w, givens)
    except (ValueError, RecursionError) as exc:
        st.session_state.pop("solved_result", None)
        st.error(f"The solver could not finish this puzzle: {exc}")
    else:
        st.session_state["solved_result"] = (
            puzzle_index, algorithm, solution, perf_counter() - started
        )
solved = st.session_state.get("solved_result")
if solved and solved[:2] == (puzzle_index, algorithm):
    _, _, solution, elapsed = solved
    st.success(f"Solved with {algorithm} in {elapsed:.3f} seconds.")
    show_board(n, box_h, box_w, givens, solution)

st.subheader("Ask about a cell")
columns = st.columns(3)
with columns[0]:
    row = st.number_input("Row", min_value=1, max_value=n, value=1, step=1)
with columns[1]:
    column = st.number_input("Column", min_value=1, max_value=n, value=1, step=1)
with columns[2]:
    value = st.number_input("Value", min_value=1, max_value=n, value=1, step=1)
tutor_mode = st.checkbox("Show reasoning trace (tutor mode)", value=True)
if tutor_mode:
    st.caption("The tutor trace follows forward-chaining rules; the verdict uses backward chaining.")
if st.button("Check entailment"):
    try:
        with st.spinner("Checking the query..."):
            kb = build_definite_kb(n, box_h, box_w, givens)
            query = atom("Is", int(row), int(column), int(value))
            verdict = pl_bc_entails(kb, query)
            steps = proof_steps(kb, query) if tutor_mode and verdict else []
    except (ValueError, RecursionError) as exc:
        st.session_state.pop("query_result", None)
        st.error(f"Could not check the query: {exc}")
    else:
        st.session_state["query_result"] = (
            puzzle_index, int(row), int(column), int(value), verdict, steps, tutor_mode
        )
result = st.session_state.get("query_result")
if result and result[:4] == (puzzle_index, int(row), int(column), int(value)):
    _, qr, qc, qv, verdict, steps, traced = result
    st.write(f"Is row {qr}, column {qc} equal to {qv}? **{verdict}**")
    if traced:
        st.markdown("**Reasoning trace**")
        if steps:
            for index, step in enumerate(steps, start=1):
                with st.expander(f"Step {index}", expanded=index == len(steps)):
                    st.write(step)
        else:
            st.write("The given clues and elimination rules do not prove this value.")
