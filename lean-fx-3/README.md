# lean-fx-3 — PolyCell kernel (clean cut from lean-fx-2)

This directory is a **clean cut** of the PolyCell v2 kernel out of
`lean-fx-2`.  The motivation: `lean-fx-2` houses two genuinely different
kernels in one tree — a legacy intrinsic-MLTT kernel
(`Term : Ctx → Ty → RawTerm → Type`, with `Step` / `Conv`) and the newer
PolyCell v2 Generator-table cell calculus.  Keeping them in one project
conflates them.  `lean-fx-3` carries PolyCell out into a standalone home
with **no build dependency on `lean-fx-2`**.

## The two sub-projects

| Lib            | Role                                                      |
| -------------- | -------------------------------------------------------- |
| `FX1Poly`      | The **rich** Lean-verified PolyCell kernel.  Proof-carrying, zero-axiom, the full Generator-table cell calculus.  This is what we *build*. |
| `FX0Poly`      | A **Metamath-Zero–flavored minimal external checker** (greenfield).  Tiny, independently-auditable; re-checks the certificates `FX1Poly` emits.  We don't have it yet. |
| `FX1PolyAudit` | The zero-axiom audit engine (`#assert_no_axioms` macro + per-decl gates).  Mirrors lean-fx-2's `LeanFX2Audit`. |

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
inherited verbatim from `lean-fx-2/CLAUDE.md` and is non-negotiable.

## Migration status

Migration is **incremental and non-destructive**: each slice is copied here,
built green standalone, and only later removed from `lean-fx-2` (with
explicit per-slice confirmation).  PolyCell is a near-leaf in lean-fx-2's
dependency DAG — nothing in the legacy kernel imports it; only the audit
gates do — so the cut is mechanically clean.

| Slice              | Source (lean-fx-2)                                | Status |
| ------------------ | ------------------------------------------------- | ------ |
| Universe           | `Foundation/PolyCell/Universe/*`                  | ported (`FX1Poly.Universe.*`) |
| Core (cell calc)   | `Foundation/PolyCell/Core/*` (~140 files)         | pending |
| NbE                | `Foundation/PolyCell/NbE/*`                        | pending |
| Typed layer        | `Foundation/PolyCell/Typed/*`                     | pending — couples to legacy `Ty`; classifier to be made PolyCell-native |
| Tier0 / Modal / …  | remaining `Foundation/PolyCell/*` subtrees        | pending |

`polycell.md` (the design spec, ported here) is the canonical reference.

### Substrate the migration must resolve

PolyCell's outbound coupling to the legacy kernel is tiny — 4 modules:
`Foundation.Action` (generic Action typeclass, zero imports),
`Foundation.RawSubst.{RenameDefs,ActionInstances}` (generic renaming /
substitution machinery), and `Foundation.Ty` (the typed-layer classifier,
used only by `Typed/TypingContext`).  The clean cut copies the generic
renaming substrate into `FX1Poly`; the legacy-`Ty` typed bridge is the one
genuine design decision deferred to its own migration step (sever to a
PolyCell-native classifier vs. carry a minimal `Ty` copy).
