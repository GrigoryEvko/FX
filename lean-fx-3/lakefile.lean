import Lake
open Lake DSL

/-! # lean-fx-3 — PolyCell kernel

Two-tier verification architecture (MM0-flavored trust split):

* `FX1Poly`     — the RICH Lean-verified PolyCell kernel.  Proof-carrying,
                  zero-axiom, the full Generator-table cell calculus.  This
                  is the elaborator that PRODUCES certificates.
* `FX1PolyAudit`— the zero-axiom audit engine: the `#assert_no_axioms` macro
                  plus per-declaration gate files.  A two-target split keeps
                  the inner loop (`lake build FX1Poly`) from paying the audit
                  elaboration tax.
* `FX0Poly`     — the Metamath-Zero–flavored MINIMAL external checker
                  (greenfield).  A tiny, independently-auditable verifier
                  that re-checks FX1Poly's emitted certificates.  Trust
                  reduces to FX0Poly's small core, not to FX1Poly's full
                  elaborator.

Build targets:

* `lake build FX1Poly`            — fast inner-loop kernel build.
* `lake build FX1Poly FX1PolyAudit` — full strict zero-axiom sweep
                                      (pre-merge / CI gate).  The
                                      authoritative umbrella is
                                      `FX1PolyAudit.AuditAll`: a pure-import
                                      module naming every required gate, so a
                                      deleted gate file fails the build rather
                                      than silently shrinking the `.submodules`
                                      glob below.
* `lake build FX0Poly`            — the minimal checker (stub for now).
-/

package «lean-fx-3» where
  version := v!"0.1.0-clean-cut"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`maxHeartbeats, (20000000 : Nat)⟩,
    ⟨`synthInstance.maxHeartbeats, 20000000⟩
  ]

@[default_target]
lean_lib FX1Poly where
  globs := #[.submodules `FX1Poly]

lean_lib FX1PolyAudit where
  globs := #[.submodules `FX1PolyAudit]

lean_lib FX0Poly where
  globs := #[.submodules `FX0Poly]
