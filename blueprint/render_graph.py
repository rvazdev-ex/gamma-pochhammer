#!/usr/bin/env python3
"""
Post-process the leanblueprint web output so the dependency graph
renders without a running HTTP server.

Why this exists
---------------
plastexdepgraph emits a `dep_graph_document.html` whose `#graph` div is
populated client-side by `d3-graphviz`, which fetches `graphvizlib.wasm`
inside a Web Worker.  Browsers refuse cross-origin requests from
`file://` (Workers especially), so loading the page off disk leaves the
graph area blank.  Using `leanblueprint serve` works, but anyone who
double-clicks the HTML or hosts it on a static-files server without
WASM MIME setup hits a silent failure.

What this does
--------------
1. Extracts the inline dot string from `dep_graph_document.html`.
2. Renders it to standalone SVG, PNG, and PDF via the system `dot`.
3. Embeds the rendered SVG directly into the `#graph` div as a static
   fallback (the JS still runs and overwrites it when WASM loads).
4. Flips `useWorker: true` to `useWorker: false` so the non-worker path
   also avoids the cross-origin Worker block.
5. Copies the three artifacts to `blueprint/dep_graph.{svg,png,pdf}`
   so they survive `git clean` of the gitignored `blueprint/web/`.

Run from the repo root after `leanblueprint web`:

    python3 blueprint/render_graph.py
"""
from __future__ import annotations

import pathlib
import re
import shutil
import subprocess
import sys


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    web = root / "blueprint" / "web"
    html_path = web / "dep_graph_document.html"
    if not html_path.exists():
        print(f"error: {html_path} not found; run `leanblueprint web` first",
              file=sys.stderr)
        return 1

    html = html_path.read_text()

    # 1. Extract inline dot literal.
    match = re.search(r"\.renderDot\(`(.*?)`\)", html, re.DOTALL)
    if not match:
        print("error: no .renderDot(`...`) call found in HTML", file=sys.stderr)
        return 1
    dot = match.group(1)

    dot_path = web / "dep_graph.dot"
    dot_path.write_text(dot)

    if shutil.which("dot") is None:
        print("error: graphviz `dot` not on PATH (install graphviz)",
              file=sys.stderr)
        return 1

    # 2. Render to SVG, PNG, PDF.
    svg_path = web / "dep_graph.svg"
    png_path = web / "dep_graph.png"
    pdf_path = web / "dep_graph.pdf"
    subprocess.run(["dot", "-Tsvg", str(dot_path), "-o", str(svg_path)], check=True)
    subprocess.run(["dot", "-Tpng", "-Gdpi=200", str(dot_path), "-o", str(png_path)], check=True)
    subprocess.run(["dot", "-Tpdf", str(dot_path), "-o", str(pdf_path)], check=True)

    # 3. Inline-embed SVG into the #graph div (static fallback).
    svg = svg_path.read_text()
    svg = re.sub(r"^<\?xml[^>]*\?>\s*", "", svg)
    svg = re.sub(r"<!DOCTYPE[^>]*>\s*", "", svg)
    html, n = re.subn(
        r'<div id="graph"></div>',
        f'<div id="graph">{svg}</div>',
        html, count=1)
    if n != 1:
        print(f"warning: <div id=\"graph\"></div> pattern matched {n} times",
              file=sys.stderr)

    # 4. Disable Worker (so non-WASM Chrome on file:// works).
    html = html.replace("useWorker: true", "useWorker: false")

    html_path.write_text(html)

    # 5. Mirror the standalone artifacts to the tracked blueprint/ dir.
    out_dir = root / "blueprint"
    for ext in ("svg", "png", "pdf"):
        shutil.copy(web / f"dep_graph.{ext}", out_dir / f"dep_graph.{ext}")

    print("rendered:")
    for ext in ("svg", "png", "pdf"):
        print(f"  blueprint/dep_graph.{ext}")
        print(f"  blueprint/web/dep_graph.{ext}")
    print("patched: blueprint/web/dep_graph_document.html "
          "(SVG embedded + useWorker disabled)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
