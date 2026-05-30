import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TypingContext
import FX1Poly.Typed.HasType

/-! # Tools/AuditAll/AuditTyped
   — persistent per-declaration zero-axiom gate for the typed layer

The typed layer (polycell.md §11.8.5) is the dim-0 soundness stratum: the
`.context` / `.type` / `.term` cells that classify each other.  Its first
brick is the native `TypingContext` de Bruijn telescope (TY-CTX, the
lean-fx-3 re-port of lean-fx-2's M31/M32) — the `.context`-sort spine the
`HasType` engine consumes via the variable rule.

Every declaration here must elaborate without `propext`, `Classical.choice`,
`Quot.sound`, or `sorryAx` — so any future edit that introduces an axiom
dependency fails `lake build FX1PolyAudit` immediately.  The `lookup`
de Bruijn destructuring and `length_eq_scope` induction are the two places
a careless rewrite could pull `propext` through the match compiler; these
gates pin them shut.
-/

/-! ### TY-CTX #467 — native TypingContext telescope + lookup + coherence -/

#assert_no_axioms FX1Poly.Typed.TypingContext
#assert_no_axioms FX1Poly.Typed.TypingContext.length
#assert_no_axioms FX1Poly.Typed.TypingContext.length_eq_scope
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_zero
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_succ

/-! ### TY-ENGINE #282 first slice — HasType var + conv core + IsType -/

#assert_no_axioms FX1Poly.Typed.universeCodeCell
#assert_no_axioms FX1Poly.Typed.variableCell
#assert_no_axioms FX1Poly.Typed.HasType
#assert_no_axioms FX1Poly.Typed.IsType
