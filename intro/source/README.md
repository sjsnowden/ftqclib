# ftqclib overview — editable source

This is the source for **ftqclib: A Mathematical Foundation for Fault-Tolerant Quantum Computing**. The reading edition is a single offline HTML file with native MathML equations and inline SVG diagrams.

## Files

- `ftqclib.md`: essay, mathematics in LaTeX notation, captions, and references.
- `figures/bell-pair.svg`: Bell preparation circuit and amplitude support.
- `figures/semantics.svg`: the semantic correctness diagram.
- The other eight SVGs illustrate Pauli signs, carrier evaluation and gate actions, interference, chains, unread Bell information, the thirteen-qubit planar patch, and continuing work.
- `make_figures.py`: standard-library Python generator for those eight additional figures; the SVGs themselves remain editable.
- `lean-excerpts.json`: the eight literal Lean extracts, source-module paths, starting lines, and normalized source-file hashes.
- `STYLE-PUBLIC.html`: the repository's public document template, preserved verbatim.
- `build.mjs`: Markdown, SVG, and MathML compiler and structural checks.
- `package.json` and `package-lock.json`: pinned build dependencies.

## Rebuild

Use Node.js 20 or newer. This edition was built with Node.js 24.14.1, Marked 17.0.5, and Temml 0.13.5.

From this source directory:

```sh
npm ci --ignore-scripts
npm run build
```

The build writes `../index.html` and `../build-manifest.json`. Installing dependencies requires registry access; reading the resulting HTML requires no network access. External references are ordinary links and are followed only when selected.

Edit the Markdown and SVG sources, then rebuild. The generated HTML should not be edited separately. Display mathematics uses `$$` on separate lines; inline mathematics uses `$...$`.

Semantic blocks use the following forms:

```text
:::figure bell-pair.svg
**Figure 1.** Caption text.
:::

:::proposition Statement name
Statement text.
:::

:::proof
Proof text.
:::

:::theorem Statement name
Statement text.
:::

:::proof-sketch
Proof sketch text.
:::
```

The template head, including its semantic rules and unchanged stylesheet, is copied into the output; only the document title changes. Temml's display-math root decoration is replaced by the equivalent semantic `display="block"` attribute, whose layout is already defined in STYLE-PUBLIC. The redundant `mathcal` class is removed from the Unicode mathematical-script letters 𝒞 and 𝒢; their alphabet is already represented in the characters themselves. The compiler rejects any remaining inline styles or unsupported math classes. Table column headers carry semantic `scope` attributes.

## Provenance and checks

The essay concerns the source snapshot labelled **d66ec2b** by [the published ftqclib source browser](https://ftqclib.pages.dev/), which embeds 519 Lean modules. Selected definitions, theorem statements, and proofs were inspected from that embedded source. This does not claim an independent Lean rebuild or a complete proof audit. It does not identify the older local checkout with the published snapshot.

STYLE-PUBLIC was taken from `vendor/code-standard/documents/STYLE-PUBLIC.html` in the local `sjsnowden/ftqclib` checkout at commit **2b172c66bd2b2e27602accb47862e5d9a6a5f44f**. Its exact content and stylesheet hashes are recorded in the build manifest.

The initial text received separate mathematical, claims, and reader-accessibility reviews. The expanded surface-code discussion, carrier definitions and examples, and eight Lean excerpts received further mathematical review. The build checks mathematical compilation, internal reference targets, unique identifiers, SVG accessibility metadata, absence of scripts and external rendering dependencies, preservation of the stylesheet, and agreement of the Lean blocks with their source-excerpt registry. The SVGs were rendered locally and visually inspected. Full-document browser visual verification was unavailable in this session; the structural checks do not establish rendering in every browser.

The Bell and minimum-weight-correction propositions are explanatory proofs written for the essay. The carrier completeness theorem is an expository statement of the source result, with its scale and admissibility restrictions retained; its accompanying proof is explicitly a sketch. Literal Lean proof excerpts depend on their original file context and are not claimed to be independently compiled standalone examples.

The continuation uses the authenticated plan inspected on 5 October 2026, labelled as built from `docs/TARGETS.md` (`08f4171e1623`) and `docs/STEPS.json` (`78711b2a934e`). Only the requested discussion and source citation are included here; credentials and the full access-controlled page are not part of this bundle. Proved foundations and planned operational results are distinguished in the prose and the roadmap figure.
