# lean-fx-3 — PolyCell kernel

`lean-fx-3` is the standalone home of the PolyCell v2 kernel: a
Generator-table cell calculus where every term is a `PolyCell profile sort
dim` and reduction lives at the dim-1 morphism layer.  The project is
self-contained — a single `lakefile.lean` with three `lean_lib` targets and
no external dependency.

## The two sub-projects

| Lib            | Role                                                      |
| -------------- | -------------------------------------------------------- |
| `FX1Poly`      | The **rich** Lean-verified PolyCell kernel.  Proof-carrying, zero-axiom, the full Generator-table cell calculus.  This is what we *build*. |
| `FX0Poly`      | A **Metamath-Zero–flavored minimal external checker** (greenfield stub).  Tiny, independently-auditable; re-checks the certificates `FX1Poly` emits. |
| `FX1PolyAudit` | The zero-axiom audit engine (`#assert_no_axioms` macro + per-decl gates).  Split from `FX1Poly` so the inner loop skips the audit tax. |

The `FX1Poly` ↔ `FX0Poly` relationship is the **MM0 ↔ Lean trust split**:
the rich kernel elaborates and produces certificates; the minimal checker
re-verifies them so that trust reduces to a ~600-line core, not to the full
elaborator.

## Build targets

```bash
lake build FX1Poly                 # fast inner-loop kernel build
lake build FX1Poly FX1PolyAudit    # full strict zero-axiom sweep (CI gate)
lake build FX0Poly                 # the minimal checker (stub for now)
```

Toolchain: `leanprover/lean4:v4.29.1` (pinned in `lean-toolchain`).

## Zero-axiom commitment — ABSOLUTE

Every shipped declaration is a `theorem` / `lemma` / `def` / `inductive` /
`structure` / `instance` with a real body.  **No** `axiom`, `sorry`,
`admit`, `noncomputable`, `Classical.*`, `@[extern]`, or `@[implemented_by]`
in kernel code — and stdlib lemmas that leak `propext` / `Quot.sound` /
`Classical.choice` are reimplemented cleanly.  Verified per-decl by
`#assert_no_axioms` under the `FX1PolyAudit` target.  This discipline is
non-negotiable.

## Design reference

`polycell.md` is the canonical design spec for the PolyCell substrate.
