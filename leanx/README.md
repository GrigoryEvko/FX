# leanx — Lean 4 Reference Interpreter for FX

`leanx` is the canonical reference implementation of FX's semantics,
written in Lean 4.  It is the authoritative answer to "what does this
FX program mean."

This directory lives at the root of the main FX repository alongside
the language specification (`../fx_design.md`) and the production
compiler (`../compiler/`, forthcoming).

## Quick orientation

* **`SPEC.md`** — the full design specification for leanx.  Read this.
* **`AXIOMS.md`** — the canonical 33-entry allowlist; status column
  distinguishes `pending` / `stated` / `proved`.
* **`BOOTSTRAP.md`** — how to use leanx to bootstrap `fxc` from source.
* **`SORRY.md`** — tracker for open `sorry` placeholders (must never
  appear in `FX/Kernel/**` or `FX/Metatheory/**`).
* **`docs/MetatheoryCorpus.md`** — known-unsoundness corpus
  (`fx_design.md` §27.2).  Each row is a permanent regression test.
* **`docs/rfcs/`** — proposals that touch the trust base.
* **`FX/`** — Lean 4 source tree.  `FX/Kernel/**` and
  `FX/Metatheory/**` are the zero-sorry trusted trees.
* **`tests/`** — test library and runtime runner.
* **`scripts/`** — CI enforcement (axiom audit, coverage metric).

## Build

```bash
cd leanx
lake build              # build everything
lake exe fxi run ...    # run an FX program
lake test               # run the test suite
```

## Trust base

Three layers:

1. **Lean 4 kernel** (~10k LOC C++, being verified by Lean4Lean).
2. **leanx kernel** (`FX/Kernel/**`, ~3000 LOC Lean; zero sorry,
   33 axioms from `AXIOMS.md`).
3. **Z3 SMT oracle** (external subprocess; queries logged to
   `audit.smtq`).

Everything else is untrusted — bugs produce rejections, not silently
wrong output.

## What leanx is not

* Not a production compiler.  Use `fxc` (the native compiler, written
  in FX itself) for real work.
* Not a replacement for `fx_design.md`.  The spec comes first; leanx
  realizes it executably.
* Not a general-purpose Lean library.

## Project status

**Phase 1 in progress** (per `SPEC.md` §7).  Delivered:

  * Grade semirings for 13 of the 21 dimensions (`FX/Kernel/Grade/`),
    with semiring laws proved by `decide` rather than postulated.
  * Universe levels (`FX/Kernel/Level.lean`).
  * Lexer (`FX/Syntax/Lexer.lean`), surface AST (`FX/Syntax/Ast.lean`),
    recursive-descent parser (`FX/Syntax/Parser.lean`).
  * CLI skeleton (`fxi tokenize`, `fxi parse`) in `FX/Cli/Main.lean`.
  * Runtime test suite: 146 runtime checks + hundreds of compile-time
    `example : P := by decide` proofs.
  * **Zero `sorry` and zero `axiom` in `FX/Kernel/**` and
    `FX/Metatheory/**`** — verified by `scripts/axiom-audit.sh`.

Phase 1 exit gate (not yet reached):  kernel `Term`, `HasType`,
`Reduces` relations land; Preservation and Progress get their
proofs.  Current Metatheory files are Phase-0 placeholders with the
theorem statements documented in `../fx_design.md` §27.4.

See `SPEC.md` §7 for phases 2–8 and `docs/MetatheoryCorpus.md` for
the unsoundness corpus (layer 1 of `fx_design.md` §27.3).

## Legacy

`../fstarx/` is from a prior F*/OCaml bootstrap attempt, retained for
history only.  Not referenced by leanx.

## License

Same as the main FX project.  See `../LICENSE`.
