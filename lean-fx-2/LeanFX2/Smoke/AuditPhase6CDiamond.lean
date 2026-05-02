import LeanFX2.Confluence.RawDiamond

/-! Phase 6.C diamond + confluence zero-axiom audit.

Five theorems shipped:
* `RawStep.par.diamond` — single-step diamond
* `RawStep.par.toStar` — single-step → multi-step lift
* `RawStep.parStar.snoc` — append a step at the end
* `RawStep.parStar.append` — concatenate two chains
* `RawStep.par.strip` — strip lemma
* `RawStep.parStar.confluence` — Church-Rosser
-/

#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.par.toStar
#print axioms LeanFX2.RawStep.parStar.snoc
#print axioms LeanFX2.RawStep.parStar.append
#print axioms LeanFX2.RawStep.par.strip
#print axioms LeanFX2.RawStep.parStar.confluence
