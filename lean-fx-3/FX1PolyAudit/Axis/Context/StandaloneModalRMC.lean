import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.StandaloneModalRMC

/-! # FX1PolyAudit/AuditAxisContextStandaloneModalRMC — zero-axiom gate for context-21's capstone

Per-declaration zero-axiom gate for `context-21`'s context-side deliverable
(`FX1Poly/Axis/Context/StandaloneModalRMC.lean`, `⟦core=𝒞 standalone; assembly→Core/fib⟧`): the CAPSTONE of
the context axis — the standalone modal Representable Map Category on `𝒞 = fxBaseSubstCategory.opposite`,
bundling `context-10`'s comprehension + Uemura representability, `context-4`'s modal lock, `context-17`'s
Beck–Chevalley coherence (incl. the display pullback), `context-12`'s normalization, and the Uemura AXIOM-1
display-pullback closure.  Coherence: the carrier is the opposite base, the bundled lock is the trivial mode,
and the AXIOM-1 closure IS the Beck–Chevalley pullback.  The full Uemura Def-2.1 MorphismClass, the cross-axis
model assembly, and the lock-threaded NbE are the honest deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The capstone bundle + witness
#assert_no_axioms FX1Poly.Axis.StandaloneModalRMC
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC

-- Coherence: the bundled pieces share the one base 𝒞
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC_contextCategory_isOppositeBase
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC_modalLock_isTrivialMode
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC_axiom1_isBeckChevalleyPullback
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC_displayPullback_isStrict
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC_displayTowerPullback_isStrict

-- Honesty markers (the → Core/fib cross-axis assembly) + smoke
#assert_no_axioms FX1Poly.Axis.standaloneModalRMC_hasFullUemuraMorphismClass
#assert_no_axioms FX1Poly.Axis.standaloneModalRMC_hasCrossAxisModelAssembly
#assert_no_axioms FX1Poly.Axis.standaloneModalRMC_hasModalLockThreadedNbe
#assert_no_axioms FX1Poly.Axis.standaloneModalRMC_hasDisplayRepresentableClass
#assert_no_axioms FX1Poly.Axis.fxStandaloneModalRMC_representability_smoke

end FX1PolyAudit
