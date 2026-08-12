#!/usr/bin/env python3
"""Structural audit checks for the v6.3 closure synthesis.

This script does not prove the theorem. It checks high-risk bookkeeping facts
that were sources of earlier red/orange gaps: complete control coverage,
no P1<->P2 circular citation, no short-lift<->terminal circular citation,
explicit marked-tail guards, one-shot seed ordering, and permanent negative
regressions.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = HERE / "3n_plus_minus_1_game_v6.3.tex"
V5_CERT = HERE / "routing_certificate_v5_0.json"


def block_between(text: str, start_marker: str, end_marker: str) -> str:
    a = text.index(start_marker)
    b = text.index(end_marker, a)
    return text[a:b]


def theorem_graph(text: str):
    # Coarse theorem/lemma graph sufficient to catch direct reference cycles.
    envpat = re.compile(
        r"\\begin\{(lemma|proposition|corollary|theorem)\}(.*?)(?=\\end\{\1\})\\end\{\1\}",
        re.S,
    )
    nodes: dict[str, tuple[int, str]] = {}
    for m in envpat.finditer(text):
        lm = re.search(r"\\label\{([^}]+)\}", m.group(0))
        if lm:
            nodes[lm.group(1)] = (m.start(), m.group(0))
    graph = {k: set() for k in nodes}
    for k, (_, block) in nodes.items():
        for r in re.findall(r"\\ref\{([^}]+)\}", block):
            if r in nodes and r != k:
                graph[k].add(r)
    return nodes, graph


def find_cycles(graph):
    index = 0
    stack: list[str] = []
    onstack: set[str] = set()
    idx: dict[str, int] = {}
    low: dict[str, int] = {}
    cycles: list[list[str]] = []

    def visit(v: str):
        nonlocal index
        idx[v] = low[v] = index
        index += 1
        stack.append(v)
        onstack.add(v)
        for w in graph[v]:
            if w not in idx:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = stack.pop()
                onstack.remove(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                cycles.append(comp)

    for v in graph:
        if v not in idx:
            visit(v)
    return cycles


def main() -> None:
    text = TEX.read_text(encoding="utf-8")
    cert = json.loads(V5_CERT.read_text(encoding="utf-8"))

    # 1. Every former v5 router control is explicitly assigned a v6 semantic row.
    controls = cert["controls"]
    expected = {
        "boundary_entry": "S1",
        "loss_sibling_entry": "S1",
        "a_obligation": "S2/S3",
        "a_test_4": "P1",
        "a_test_3": "P1",
        "a_test_2": "P1",
        "a_test_1": "P1",
        "b_select": "P1",
        "b2_first": "P1",
        "b2_ready": "P1",
        "factor_fork": "S4",
        "high_return": "S5/S6",
        "marked_tail": "S7",
        "short_lift": "S8/S9",
        "terminal_macro": "S10",
    }
    assert set(controls) == set(expected), (controls, expected)

    # Required sections/labels that implement the mapping.
    required_labels = [
        "prop:P1-closed",
        "prop:P2-closed",
        "lem:factor-fork-pay",
        "lem:high-return-pay",
        "lem:marked-tail-pay",
        "lem:short-tail",
        "lem:D2-pure",
        "lem:loss-anchored-lift",
        "lem:attached-lift",
        "lem:attached-b",
        "lem:terminal-pay",
        "cor:short-lift-closed",
        "prop:fixed-fibre",
        "prop:normalizer",
    ]
    for label in required_labels:
        assert f"\\label{{{label}}}" in text, label

    # 2. The two permanent negative regressions are visibly present.
    assert "20\\longmapsto30\\longmapsto45\\longmapsto68" in text
    assert "B(68)=25>20" in text
    assert "smaller canonical coefficient" in text
    assert "a smaller coefficient source" in text

    # 3. No stale open-P1/P2 status survives.
    lower = text.lower()
    stale = [
        "open mathematical obligations",
        "p1 remains open",
        "p2 remains open",
        "open proof obligation",
    ]
    for phrase in stale:
        assert phrase not in lower, phrase

    # 4. P1 must stop at attached factor/lift entry and not call the P2 factor lemma.
    p1 = block_between(
        text,
        "\\begin{proposition}[Seeded $A/B_2$ reset provenance]",
        "\\section{Semantic closure of factor, return and attached routing}",
    )
    assert "lem:factor-fork-pay" not in p1
    assert "prop:P2-closed" not in p1
    assert "P1 stops here" in p1

    # 5. Short-lift arithmetic may feed terminal-pay, never cite it to prove itself.
    a = text.index("\\label{lem:attached-lift}")
    b = text.index("\\end{proof}", a)
    attached = text[a:b]
    assert "lem:terminal-pay" not in attached

    # 6. Marked tail carries exactly the guard required by the old local lemma.
    mt_a = text.index("\\label{lem:marked-tail-pay}")
    mt_b = text.index("\\end{proof}", mt_a)
    marked = text[mt_a:mt_b]
    for fragment in [
        "b=Q_D^g(C)",
        "q=A(b)",
        "y=B(b)",
        "b,q\\text{ \\WIN}",
        "y\\text{ \\LOSS}",
        "D\\ge3",
    ]:
        assert fragment in marked, fragment

    short_a = text.index("\\label{lem:short-tail}")
    short_b = text.index("\\end{proof}", short_a)
    short = text[short_a:short_b]
    assert r"q=B(b)\text{ WIN}" in short
    assert r"y=A(b)\text{ LOSS}" in short
    assert r"j\ge2" in short
    assert "arithmetically empty" in short
    assert r"q=A(b)\text{ WIN}" in short
    assert r"y=B(b)\text{ LOSS}" in short
    assert "valuation is exactly one" in short
    assert r"m=\lambda+1\ge2" in short
    assert r"\delta=1-g" in short

    # D=2 is deliberately separate from the D=3 terminal module and is
    # explicitly LOSS-anchored.
    d2_a = text.index("\\label{lem:D2-pure}")
    d2_b = text.index("\\end{proof}", d2_a)
    d2 = text[d2_a:d2_b]
    assert "lem:terminal-pay" not in d2
    assert "loss-anchored-lift" in d2
    assert "never" in d2 and "free obligation" in d2

    la_a = text.index("\\label{lem:loss-anchored-lift}")
    la_b = text.index("\\end{proof}", la_a)
    la = text[la_a:la_b]
    for fragment in [
        "c_A=A(y)", "c_B=B(y)",
        r"Q_r^\epsilon(J(c_B))", "A(c_A)", "B(c_A)",
        "reverse-factor lemma is never invoked",
        "unrelated finite endpoint",
    ]:
        assert fragment in la, fragment

    # High-return canonical and factor alternatives are separated: only the
    # factor alternative may install a marked tail, and both first pay a token.
    hr_a = text.index("\\label{lem:high-return-pay}")
    hr_b = text.index("\\end{proof}", hr_a)
    hr = text[hr_a:hr_b]
    assert "including the exact obligation" in hr
    assert "canonical continuation" in hr
    assert "only the factor alternative enters" in hr.lower()
    assert "pair replacement $(u,c)\\mapsto(p,b)$ is strict" in hr

    # The terminal lemma is scoped only to the post-payment D=3 module.
    term_a = text.index("\\label{lem:terminal-pay}")
    term_b = text.index("\\end{proof}", term_a)
    term = text[term_a:term_b]
    assert "post-payment $D=3$" in term
    assert "D=2" not in term

    # 7. Seed order is explicit and prevents two independent initializations.
    seed_a = text.index("\\label{lem:seed-policy}")
    seed_b = text.index("\\end{proof}", seed_a)
    seed = text[seed_a:seed_b]
    assert "while $\\eta=1$" in seed
    assert "inner seed $\\zeta$ is\nunavailable" in seed
    assert "no unrelated finite state" in seed

    # 8. Token descent cannot be used while changing the older retained source.
    assert "outer token\ndecrease preserves the preceding outer source $s$" in text
    assert "inner token decrease preserves $(s,\\eta,M,\\zeta)$" in text

    # 9. Router partitions include every dangerous unbounded/terminal parameter range.
    p2_a = text.index("\\label{prop:P2-closed}")
    p2_b = text.index("\\section{Well-foundedness", p2_a)
    p2 = text[p2_a:p2_b]
    for fragment in [
        "$v=5$ or", "$v=6$", r"$v\ge7$",
        r"1&B(b)&A(b)", r"2&A(b)&B(b)", r"$D\ge3$",
        "D=2", "LOSS-anchored", "post-payment $D=3$", r"$m\ge4$",
        "terminal exponent is", "exactly one, two, or three",
        r"$\lambda=1,2,3,\ge4$",
    ]:
        assert fragment in p2, fragment

    # 10. No direct theorem/lemma reference cycle remains.
    nodes, graph = theorem_graph(text)
    cycles = find_cycles(graph)
    assert not cycles, cycles

    print("V6.3 STRUCTURAL RED/ORANGE AUDIT CHECKS PASSED")
    print(f"former v5 controls covered: {len(controls)}")
    print("mapping:")
    for c in controls:
        print(f"  {c}: {expected[c]}")
    print(f"labeled theorem/lemma nodes checked for direct cycles: {len(nodes)}")
    print("direct reference cycles: none")
    print("scope: structural bookkeeping checks only; not a proof by computation")


if __name__ == "__main__":
    main()
