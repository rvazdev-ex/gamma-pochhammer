# GammaPochhammer

[![Build](https://github.com/rvazdev-ex/gamma-pochhammer/actions/workflows/blueprint.yml/badge.svg)](https://github.com/rvazdev-ex/gamma-pochhammer/actions/workflows/blueprint.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.29.1-blueviolet)](./lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.29.1-blue)](./lakefile.toml)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](./LICENSE)

A Lean 4 + [mathlib](https://leanprover-community.github.io/) formalization
of the paper

> **Pochhammer Gamma Kernels** &mdash; R. Valencia
> ([PDF](./paper/paper.tex) &middot;
>  [arXiv:2312.07754 (Karp's problem)](https://arxiv.org/abs/2312.07754))

The headline result (Theorem~1 of the paper) settles **Karp's conjecture**
on Toeplitz determinants of Pochhammer symbols from the 2023 Sofia
open-problem collection: the binomial Pochhammer convolution
\(P_n(z)\) inherits strict negative real-rootedness from its input
sequence \((f_k)\).

---

## Quick links

| Resource | Where |
|---|---|
| Paper (LaTeX source) | [`paper/paper.tex`](./paper/paper.tex) |
| Paper (PDF, built by CI) | <https://rvazdev-ex.github.io/gamma-pochhammer/paper.pdf> |
| Blueprint &mdash; web, with dependency graph | <https://rvazdev-ex.github.io/gamma-pochhammer/blueprint/> |
| Blueprint &mdash; PDF | <https://rvazdev-ex.github.io/gamma-pochhammer/blueprint/blueprint.pdf> |
| API docs &mdash; doc-gen4 | <https://rvazdev-ex.github.io/gamma-pochhammer/docs/> |
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

`lake build` succeeds with **no `sorry`s**. Run `#print axioms main_theorem`
to confirm only the two project axioms appear.

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
│   │   └── macros/common.tex
│   ├── plastex.cfg                   -- HTML renderer config
│   ├── print.bib                     -- bibliography
│   └── lean_decls                    -- declaration manifest
├── BLUEPRINT.md                      -- high-level paper-to-Lean map
├── lakefile.toml                     -- Lean build config
├── lean-toolchain                    -- pinned Lean version
└── .github/workflows/blueprint.yml   -- CI: Lean + doc-gen4 + blueprint + Pages
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

```sh
pip install leanblueprint
leanblueprint checkdecls   # verify every \lean{...} resolves
leanblueprint pdf          # builds blueprint/print/print.pdf
leanblueprint web          # builds blueprint/web/index.html
```

### API documentation

```sh
lake -Kenv=dev update doc-gen4
lake -Kenv=dev build GammaPochhammer:docs
# Output: .lake/build/doc/index.html
```

## One-time GitHub Pages setup

For the deployed site at
<https://rvazdev-ex.github.io/gamma-pochhammer/> to publish:

1. **Settings &rarr; Actions &rarr; General**:
   under *Workflow permissions*, allow GitHub Actions to write
   to the repository.
2. **Settings &rarr; Pages &rarr; Source**: choose *GitHub Actions*.

Pushes to `main` then trigger
[`.github/workflows/blueprint.yml`](./.github/workflows/blueprint.yml),
which builds the Lean project, doc-gen4 API docs, the blueprint
(web + PDF), and the paper PDF, then deploys everything to Pages.

## Contributing

The two open axioms (Lemma~1 and Lemma~2 of the paper) require
independent mathlib infrastructure (Aissen--Schoenberg--Whitney /
Hermite--Kakeya--Obreschkoff). Contributions toward either are
welcome; see [`BLUEPRINT.md`](./BLUEPRINT.md) for the proof routes.

When editing the blueprint, every `\lean{GammaPochhammer.foo}` tag in
`blueprint/src/content.tex` must resolve to a real declaration, or
`leanblueprint checkdecls` (run in CI) will fail.

## License & citation

Released under the [Apache 2.0 license](./LICENSE).

If you reference the formalization or the paper, please cite:

```bibtex
@misc{valencia-gamma-pochhammer,
  author       = {R. Valencia},
  title        = {Pochhammer Gamma Kernels},
  year         = {2026},
  howpublished = {\url{https://github.com/rvazdev-ex/gamma-pochhammer}},
}
```
