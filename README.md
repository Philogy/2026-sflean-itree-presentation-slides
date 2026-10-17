# SF Lean — Interaction Trees in Lean 4 (2026)

Slides for an SF Lean talk on Interaction Trees (ITrees) in Lean 4, built with
[VersoSlides](https://github.com/leanprover/verso-slides): Lean documents
compiled to an offline [reveal.js](https://revealjs.com) deck, with real
semantic Lean highlighting on code blocks.

## Build

```sh
lake build          # compile the slides executable
lake exe slides     # render the deck into ./_slides
open _slides/index.html
```

`_slides/` and `.lake/` are gitignored.

## Layout

- `Talk.lean` — the deck itself (`#doc (Slides) ...`), one `#` heading per slide.
- `Main.lean` — entry point; `slidesMain` with theme/transition config.
- `lakefile.lean` — package config; depends on `verso-slides`.
- `lean-toolchain` — pinned to `leanprover/lean4:v4.36.0-rc1` (matches the
  `verso-slides` tag).

## Slides

1. Fuel vs. relational semantics
2. ITrees: `ret`, `tau`, `vis`
3. Monad instance and `#eval`
4. `eutt` and malloc-agnostic `Same`
5. CoFree and the quotient
6. Case study: SIR
7. Takeaway

Most slides past the first few are placeholders to be fleshed out.

## Upstream reputation

`verso-slides` is published by `@leanprover` (the Lean FRO) on Reservoir, part
of the Verso documentation toolchain — the same system behind the official Lean
manuals. First-party and low-risk.
