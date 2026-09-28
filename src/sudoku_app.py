"""Streamlit interface for the assignment's Sudoku reasoners."""

from html import escape
import json
from pathlib import Path
from time import perf_counter

import streamlit as st

from sudoku_solver import (
    atom, build_definite_kb, build_general_kb, solve_full_grid_fc,
    solve_full_grid_bc, pl_bc_entails, fc_infer, proof_steps,
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


def describe_fact(fact):
    """Render a Sudoku proposition as a sentence for a supporting step."""
    excluded = fact.op.startswith("Not")
    r, c, v = map(int, fact.op[3 if excluded else 2:].split("_"))
    verb = "cannot contain" if excluded else "contains"
    return f"Row {r}, column {c} {verb} {v}."


def show_proof_steps(steps):
    """Display recorded deductions as cards with links by step number."""
    st.markdown("**Forward-chaining reasoning trace**")
    if not steps:
        st.info("The given clues and elimination rules do not prove this value.")
        return
    st.caption(
        f"{len(steps)} steps supporting this answer, in deduction order. "
        "Expand a card to see why it follows and which earlier steps it uses."
    )
    for index, step in enumerate(steps, start=1):
        premises, conclusion = step['premises'], step['conclusion']
        excluded = conclusion.op.startswith("Not")
        r, c, v = map(int, conclusion.op[3 if excluded else 2:].split("_"))
        if excluded:
            action = f"Eliminate {v} from R{r}C{c}"
        elif premises:
            action = f"Place {v} at R{r}C{c}"
        else:
            action = f"Given: R{r}C{c} = {v}"
        with st.expander(f"Step {index} · {action}", expanded=index == len(steps)):
            st.write(describe_rule(premises, conclusion))
            if premises:
                st.markdown("**Based on earlier steps**")
                for number, premise in zip(step['depends_on'], premises):
                    st.markdown(f"- **Step {number}:** {describe_fact(premise)}")
            else:
                st.caption("Starting fact: supplied by the puzzle.")
            if index == len(steps):
                st.success("This establishes the queried value.")


st.set_page_config(page_title="Sudoku Solver", layout="centered")
st.markdown(
    """<style>
    .sudoku-board { border-collapse: collapse; table-layout: fixed;
        width: 100%; max-width: 26rem; margin: 1rem auto; }
    .sudoku-board td { height: clamp(1.7rem, 6vw, 2.6rem); padding: 0;
        text-align: center; vertical-align: middle;
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
    st.caption("Forward chaining starts from the clues and explains each elimination leading to the answer.")
if st.button("Check entailment"):
    try:
        with st.spinner("Checking the query..."):
            kb = build_definite_kb(n, box_h, box_w, givens)
            query = atom("Is", int(row), int(column), int(value))
            verdict = query in fc_infer(kb)
            steps = proof_steps(kb, query) if tutor_mode and verdict else []
    except (ValueError, RecursionError) as exc:
        st.session_state.pop("query_result", None)
        st.error(f"Could not check the query: {exc}")
    else:
        st.session_state["query_result"] = (
            puzzle_index, int(row), int(column), int(value), verdict, steps, tutor_mode
        )
result = st.session_state.get("query_result")
if (result and result[:4] == (puzzle_index, int(row), int(column), int(value))
        and result[6] == tutor_mode):
    _, qr, qc, qv, verdict, steps, traced = result
    st.write(f"Is row {qr}, column {qc} equal to {qv}? **{verdict}**")
    if traced:
        show_proof_steps(steps)
