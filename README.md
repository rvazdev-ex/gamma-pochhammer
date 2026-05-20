# GammaPochhammer

[![Lean 4](https://img.shields.io/badge/Lean-4.29.1-blueviolet)](./lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.29.1-blue)](./lakefile.toml)
[![License](https://img.shields.io/badge/license-MIT-green)](./LICENSE)

A Lean 4 + [mathlib](https://leanprover-community.github.io/) formalization
of the paper

> **Pochhammer Gamma Kernels**
> ([PDF](./paper/paper.pdf) &middot;
>  [arXiv:2312.07754 (Karp's problem)](https://arxiv.org/abs/2312.07754))

The headline result (Theorem~1 of the paper) settles **Karp's conjecture**
on Toeplitz determinants of Pochhammer symbols from the 2023 Sofia
open-problem collection: the binomial Pochhammer convolution
\(P_n(z)\) inherits strict negative real-rootedness from its input
sequence \((f_k)\).

## Disclosure

The proof for Karp's original problem was done by the author. The kernel
extension was provided by GPT 5.5, and the formalization was done in
collaboration with Opus 4.7.

---

## Quick links

| Resource | Where |
|---|---|
| Paper (PDF) | [`paper/paper.pdf`](./paper/paper.pdf) |
| Paper (LaTeX source) | [`paper/paper.tex`](./paper/paper.tex) |
| Blueprint (LaTeX source, builds to web + PDF) | [`blueprint/src/`](./blueprint/src/) |
| Paper-to-Lean correspondence | [`BLUEPRINT.md`](./BLUEPRINT.md) |

## Formalization status

The Lean development depends on **two project-specific axioms** (and
nothing else outside of `Classical.choice`, `propext`, and `Quot.sound`).
Both axioms correspond to classical Pólya--Schur results that mathlib
does not yet provide.

| Paper result | Lean name | Axiom-free? |
|---|---|:---:|
| Theorem~1 (\(P_n\) preserves real-negative-rootedness) | `main_theorem` | depends on (1), (2) |
| Theorem~2 (Pochhammer kernel ladder) | `ladder_formula`, `pochhammer_kernel_ladder` | yes |
| Theorem~3 (centered-family classification) | `centered_balanced_classification` | depends on (2) |
| Lemma~3 (\(\gamma\)-representation) | `gamma_representation` | **yes** &mdash; proved from first principles |
| Lemma~1 (Hadamard closure, ASW) | `hadamard_closure_for_negative_rooted` | (1) axiom |
| Lemma~2 (Schur--Maló) | `schur_preserves_nonpos` | (2) axiom |

`lake build` succeeds with **no `sorry`s**. Run
`#print axioms GammaPochhammer.main_theorem` to confirm only the two
project axioms appear.

## Repository layout

```
.
├── GammaPochhammer.lean              -- root module
├── GammaPochhammer/
│   ├── Basic.lean                    -- definitions, paper §1-§2, the 2 axioms
│   ├── GammaRep.lean                 -- proof of Lemma 3 (gamma representation)
│   ├── Determinant.lean              -- proof of Theorem 1 from Lemmas 1, 2, 3
│   └── Classification.lean           -- proof of Theorem 3
├── paper/
│   └── paper.tex                     -- LaTeX source of the paper
├── blueprint/
│   ├── src/
│   │   ├── content.tex               -- paper-to-Lean dependency map
│   │   ├── web.tex                   -- plasTeX entry point
│   │   ├── print.tex                 -- LaTeX PDF entry point
│   │   ├── plastex.cfg               -- plasTeX (HTML) renderer config
│   │   ├── latexmkrc                 -- latexmk config for the PDF build
│   │   ├── blueprint.sty             -- LaTeX stub for \usepackage{blueprint}
│   │   ├── extra_styles.css          -- extra CSS for the HTML build
│   │   └── macros/                   -- common.tex, print.tex, web.tex
│   ├── print.bib                     -- bibliography
│   └── lean_decls                    -- declaration manifest
├── BLUEPRINT.md                      -- high-level paper-to-Lean map
├── lakefile.toml                     -- Lean build config
└── lean-toolchain                    -- pinned Lean version
```

## Building locally

### Lean library

Prerequisite: [elan](https://github.com/leanprover/elan) (`curl
https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
-sSf | sh`). It will fetch the Lean toolchain pinned in
`lean-toolchain` automatically.

```sh
lake exe cache get        # download prebuilt mathlib oleans
lake build                # build GammaPochhammer (no sorrys)
```

### Paper PDF

```sh
cd paper
latexmk -pdf paper.tex
```

### Blueprint

The blueprint has three independent targets: declaration check, PDF, and
HTML. They share a single source tree under `blueprint/src/`.

**Prerequisites**

* Python 3.10+ with `leanblueprint` (PyPI):
  ```sh
  pip install leanblueprint
  ```
  `leanblueprint` itself depends on plasTeX, `plastexdepgraph`, and
  `plastexshowmore`; pip pulls them in.
* A TeX distribution providing `latexmk` and `pdflatex` (TeX Live or
  MiKTeX). The `latexmkrc` in `blueprint/src/` pins the engine to
  `pdflatex`; switch it to `xelatex`/`lualatex` only if you add
  `unicode-math` or `fontspec` to `print.tex`.
* The Lean library must build first: `leanblueprint checkdecls` calls
  `lake exe checkdecls`, which needs the compiled oleans.

**One-time setup after cloning**

`leanblueprint checkdecls` is provided by a Lake dependency
(`PatrickMassot/checkdecls`). It is declared in `lakefile.toml`, but a
fresh clone must materialize it once:

```sh
lake update checkdecls    # fetch the checkdecls Lake package
lake exe cache get        # download prebuilt mathlib oleans
lake build                # build GammaPochhammer
```

**Build the blueprint**

```sh
leanblueprint checkdecls         # verify every \lean{...} in content.tex resolves
leanblueprint pdf                # → blueprint/print/print.pdf  (uses pdflatex)
leanblueprint web                # → blueprint/web/index.html   (uses plasTeX)
python3 blueprint/render_graph.py  # render dep graph + patch HTML (see below)
leanblueprint serve              # serve blueprint/web/ on localhost
```

The `render_graph.py` step renders the hand-curated
[`blueprint/dep_graph.dot`](./blueprint/dep_graph.dot) (concise math
labels, status-coloured nodes, blue border on main results, 5-star
difficulty annotations, legend) into `blueprint/dep_graph.{svg,png,pdf}`
which are tracked in the repo. If `leanblueprint web` has been run, it
also patches `blueprint/web/dep_graph_document.html` to (a) splice the
same DOT into the `d3-graphviz` `.renderDot(...)` call so the
interactive render matches, (b) inline the rendered SVG into the
`#graph` div as a static fallback, and (c) flip `useWorker: true` to
`false`. Without (b) and (c) the client-side WASM render silently fails
when the page is opened via `file://`, so the graph area stays blank
for anyone not running `leanblueprint serve`.

All three commands must be run from the repository root (they locate
the blueprint via the surrounding Git repo).

## Contributing

The two open axioms (Lemma 1 and Lemma 2 of the paper) require
independent mathlib infrastructure (Aissen--Schoenberg--Whitney /
Hermite--Kakeya--Obreschkoff). Contributions toward either are
welcome; see [`BLUEPRINT.md`](./BLUEPRINT.md) for the proof routes.

When editing the blueprint, every `\lean{GammaPochhammer.foo}` tag in
`blueprint/src/content.tex` must resolve to a real declaration; run
`leanblueprint checkdecls` locally before pushing.

## License & citation

Released under the [MIT license](./LICENSE).

If you reference the formalization or the paper, please cite:

```bibtex
@misc{rvazdev-ex-gamma-pochhammer,
  author       = {rvazdev-ex},
  title        = {Pochhammer Gamma Kernels},
  year         = {2026},
  howpublished = {\url{https://github.com/rvazdev-ex/gamma-pochhammer}},
}
```
