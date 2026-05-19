#!/usr/bin/env python3
"""
Render the blueprint dependency graph from the hand-curated
`blueprint/dep_graph.dot` and (optionally) patch `leanblueprint`'s
generated web page so the graph stays visible off-line.

Why this exists
---------------
`plastexdepgraph` auto-generates a dependency graph from the
`\\uses{...}` annotations in `src/content.tex`, but the resulting layout
is dense and uninformative: every node is a wide ellipse with the
fully-qualified Lean name, with no proof-status colouring, no
difficulty rating, and no legend.

`blueprint/dep_graph.dot` is the hand-curated, human-readable version
of that same dependency graph: same edges as the auto-generated graph,
but with concise math labels, status fill colours
(grey = definition, green = proved, red = project-specific axiom),
a thick blue border for the paper's main results, 5-star
formalization-difficulty annotations, and a legend.  This script
turns it into SVG / PNG / PDF artifacts tracked in the repo.

Additionally, when run after `leanblueprint web`, this script patches
the generated `blueprint/web/dep_graph_document.html` so that:
  * the embedded `#graph` div ships the rendered SVG as a static
    fallback (so opening the HTML from `file://` shows something);
  * the inline DOT literal consumed by `d3-graphviz` is replaced with
    our hand-curated DOT (so the interactive render also matches);
  * the `useWorker: true` flag is flipped off (Web Workers can't fetch
    `graphvizlib.wasm` cross-origin from `file://`).

Run from the repo root (`leanblueprint web` is optional):

    python3 blueprint/render_graph.py
"""
from __future__ import annotations

import json
import pathlib
import re
import shutil
import subprocess
import sys


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    bp = root / "blueprint"
    dot_src = bp / "dep_graph.dot"
    if not dot_src.exists():
        print(f"error: {dot_src} not found (hand-curated DOT source missing)",
              file=sys.stderr)
        return 1

    if shutil.which("dot") is None:
        print("error: graphviz `dot` not on PATH (install graphviz)",
              file=sys.stderr)
        return 1

    # 1. Render SVG / PNG / PDF from the hand-curated DOT.
    svg_path = bp / "dep_graph.svg"
    png_path = bp / "dep_graph.png"
    pdf_path = bp / "dep_graph.pdf"
    subprocess.run(["dot", "-Tsvg", str(dot_src), "-o", str(svg_path)], check=True)
    subprocess.run(["dot", "-Tpng", "-Gdpi=200", str(dot_src), "-o", str(png_path)], check=True)
    subprocess.run(["dot", "-Tpdf", str(dot_src), "-o", str(pdf_path)], check=True)

    rendered = ["blueprint/dep_graph.svg",
                "blueprint/dep_graph.png",
                "blueprint/dep_graph.pdf"]

    # 2. If `leanblueprint web` has been run, also mirror the artifacts
    #    into web/ and patch the generated HTML to use our DOT.
    web = bp / "web"
    html_path = web / "dep_graph_document.html"
    if html_path.exists():
        for ext in ("svg", "png", "pdf"):
            shutil.copy(bp / f"dep_graph.{ext}", web / f"dep_graph.{ext}")

        html = html_path.read_text()

        # 2a. Replace the inline DOT literal consumed by d3-graphviz so the
        #     interactive render uses the hand-curated graph too.
        dot_text = dot_src.read_text()
        # The DOT goes inside a JS template literal: escape backticks and
        # `${` interpolation sequences just in case the curated source ever
        # contains them.
        dot_js = (dot_text
                  .replace("\\", "\\\\")
                  .replace("`", "\\`")
                  .replace("${", "\\${"))
        html, n_dot = re.subn(
            r"\.renderDot\(`.*?`\)",
            ".renderDot(`" + dot_js + "`)",
            html, count=1, flags=re.DOTALL)
        if n_dot != 1:
            print("warning: could not splice DOT into renderDot(...) call",
                  file=sys.stderr)

        # 2b. Inline-embed the rendered SVG into the #graph div so loading
        #     the page from file:// (no WASM) still shows the graph.
        svg = svg_path.read_text()
        svg = re.sub(r"^<\?xml[^>]*\?>\s*", "", svg)
        svg = re.sub(r"<!DOCTYPE[^>]*>\s*", "", svg)
        html, n_div = re.subn(
            r'<div id="graph"></div>',
            f'<div id="graph">{svg}</div>',
            html, count=1)
        if n_div != 1:
            print(f'warning: <div id="graph"></div> matched {n_div} times',
                  file=sys.stderr)

        # 2c. Disable the Web Worker code path so non-WASM browsers on
        #     file:// don't trip cross-origin restrictions.
        html = html.replace("useWorker: true", "useWorker: false")

        html_path.write_text(html)
        rendered.extend(["blueprint/web/dep_graph.svg",
                         "blueprint/web/dep_graph.png",
                         "blueprint/web/dep_graph.pdf"])
        rendered.append("blueprint/web/dep_graph_document.html (patched)")

    print("rendered:")
    for p in rendered:
        print(f"  {p}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
