# Repository Guidelines

## Project Structure & Module Organization
- Goal: a small but useful classical propositional logic library for working logicians, following mathlib conventions (naming, layout, module hygiene).
- `Main.lean` is the executable entry point (run with `lake exe propositional_logic`); use it for demos or quick checks once defined.
- `PropositionalLogic/` holds the library: `Syntax.lean` (formulas and notations), `Semantics.lean` (valuations, consequence, lemmas), `Calculus.lean` (natural deduction/proof systems placeholder), `Examples.lean` (playground), `Basic.lean` (minimal utilities).
- `lakefile.toml` declares the `PropositionalLogic` lib and `propositional_logic` exe, depends on mathlib; `lean-toolchain` pins Lean `v4.26.0-rc1`. Add new modules by topic (syntax, semantics, calculus, algebraic semantics, automation).
- Future scope: extend to modal/conditional logics; keep directory names aligned with mathlib patterns (`Modal`, `Conditional`, etc.) if/when added.

## Build, Test, and Development Commands
- `lake build` — build the library and executable.
- `lake exe propositional_logic` — run the CLI (currently a greeting; consider a truth-table checker or proof search demo).
- `lake fmt` — format Lean sources with the built-in formatter.
- `lake clean` — drop build artifacts if you hit a stale cache.
- `lake test` — placeholder for future test targets once added.

## Coding Style & Naming Conventions
- Lean defaults: two-space indentation; `camelCase` for defs/lemmas (`consequence_or_elim`), `PascalCase` for structures/types (`Fml`, `Valuation`); descriptive names over abbreviations.
- Prefer the Unicode symbols already in use (`¬`, `∧`, `∨`, `→`, `⊨`) for clarity; declare notations near their definitions.
- Keep proofs readable: structure `by` blocks, avoid long tactic chains, and only tag lemmas `@[simp]` when universally safe.
- Mirror mathlib naming for connectives and metatheory (e.g., `_assoc`, `_comm`, `_iff`, `_elim`, `_intro` suffixes); follow mathlib folder/file organization when splitting topics.

## Testing Guidelines
- No dedicated tests yet; add `example`, `theorem`, or `#eval` blocks in `Examples.lean` or a future `Tests/` folder to exercise new lemmas and valuations.
- For truth-table style checks, build small valuations and assert truth values with `rfl`/`simp`; ensure `lake build` is clean before pushing.
- When formal tests exist, wire them as Lake test targets and document the command (e.g., `lake test`).

## Commit & Pull Request Guidelines
- Use imperative commit subjects (e.g., "Add valuation helper lemmas") with brief bodies explaining intent and approach.
- PRs should summarize scope, list touched modules, note new notations/attributes, and include verification steps (commands run, notable outputs).
- Link related issues/tasks and call out breaking changes or assumptions that reviewers should check.

## Open Questions & Contributor Notes
- Executable purpose: candidates include a truth-table generator, countermodel finder, or ND proof checker; pick one and document expected CLI flags.
- Automation: embrace tactics that help interactive proving (normalization, valuation search, ND automation); avoid full-blown SAT-solver engineering unless it directly shortens proofs.
- Extensibility: design definitions to generalize to Boolean algebra semantics first; later add modal/conditional semantics in separate namespaces with shared syntax where possible.
- Completeness/compactness/decidability/post completeness/Craig interpolation are targets; outline proof strategy per file before implementing to keep modules slim.
