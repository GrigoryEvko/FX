import LeanFX2.Confluence.ParStarBridge

/-! Phase 6.D typed parallel-chain bridge + projection-confluence audit.

Five exports:
* `Step.parStar` (inductive) — typed RT closure of Step.par
* `Step.par.toStar` — single-step → multi-step lift
* `Step.parStar.snoc` / `append` — chain manipulation
* `Step.parStar.toRawBridge` — typed chain → raw chain
* `Step.parStar.toRawConfluence` — projection-confluence corollary
-/

#print axioms LeanFX2.Step.par.toStar
#print axioms LeanFX2.Step.parStar.snoc
#print axioms LeanFX2.Step.parStar.append
#print axioms LeanFX2.Step.parStar.toRawBridge
#print axioms LeanFX2.Step.parStar.toRawConfluence
