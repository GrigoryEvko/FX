import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeUnion

/-! # FX1PolyAudit/AuditUnionRecursiveElim — NATIVE-32 audit shard (recursive-eliminator rows
    integrated into the real union + the listElim row)

Per-declaration zero-axiom gate for the NATIVE-32 wave: the recursive-eliminator rows landed IN the
`HasTypeUnion` judgment (the two new arms + the native row schema/table), the union-level
theorems (bespoke adequacy, the succ-ι internal-discharge GO theorem, the closed 2-step typed
computation chain, the spike→union transfer), the spike table-inversion ingredient, and the listElim
sibling row (the app-chain shape: schema, table, spike-sibling judgment, bespoke adequacy, nil-ι typed
smoke).  Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## HasTypeUnion.lean — the native recursive-eliminator row schema + the two new union arms -/

-- The native recursive-eliminator row schema (field-identical to the spike's `RecursiveElimRule`),
-- the two Nat rows, and the if-then-else table with its rfl-diagonal metadata.
#assert_no_axioms FX1Poly.Typed.NativeRecursiveElimRule
#assert_no_axioms FX1Poly.Typed.natElimNativeRecursiveRule
#assert_no_axioms FX1Poly.Typed.natRecNativeRecursiveRule
#assert_no_axioms FX1Poly.Typed.nativeRecursiveElimRuleOf
#assert_no_axioms FX1Poly.Typed.nativeRecursiveElimRuleOf_natElim
#assert_no_axioms FX1Poly.Typed.nativeRecursiveElimRuleOf_natRec

-- The two new union arms (constructors): the NatIntro embedding (numeral scrutinees) and the
-- table-driven recursive-eliminator arm with recursive scrutinee/base premises.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.recursiveElim

/-! ## RecursiveElimUnionSpike.lean — the table-inversion transfer ingredient -/

-- A recursive-elim table hit pins one of the two Nat rows (the spike→union transfer ingredient;
-- decidable case analysis over the if-then-else, no propext).

/-! ## RecursiveElimNativeUnion.lean — the union-level theorems -/

-- Bespoke adequacy: every bespoke recursive-eliminator derivation maps into the real union.

-- ★ The succ-ι reduct types INTERNALLY through the union's own recursive arm (no reductTyped premise)
-- on the IH-return family — the NATIVE-04 residual discharged inside the real judgment, both twins.

-- ★ The closed 2-step fully-typed computation chain through the recursion loop, union-typed.

-- ★ The spike→union transfer: every spike derivation maps into the real union (induction over the
-- spike's 3 arms; recursiveElimRow via the table inversion at definitionally-equal cells).

-- The integration evidence record + its inhabiting witness.

/-! ## ListElimRecursiveRow.lean — the app-chain listElim sibling row -/

-- The sibling rule schema (app-chain consContractum), the one row, the table + rfl-diagonal metadata,
-- and the cons-ι contractum match.

-- The spike-sibling judgment (union embedding + list-intro scrutinee + the listElim row arm).

-- Bespoke listElim adequacy + the nil-ι typed smoke.

-- The listElim row evidence record + its inhabiting witness.

end FX1PolyAudit
