import LeanFX2.Foundation.Mode
import LeanFX2.Term

/-! # Modal/Foundation — modal type theory foundation

Modal types decorate a base type with a modality.  `Term.modIntro`,
`Term.modElim`, `Term.subsume` are the load-bearing modal
constructors.

## Constructors (added to Term in Layer 1; specified here)

* `Term.modIntro (modality : Modality) (term : Term ctx ty raw) :
    Term ctx (Ty.modal modality ty) (RawTerm.modIntro modality raw)`
* `Term.modElim (modElimTerm : Term ctx (Ty.modal m ty) modElimRaw)
    (cont : Term (ctx.cons (Ty.modal m ty)) resultType resultRaw) :
    Term ctx resultType (RawTerm.modElim modElimRaw resultRaw)`
* `Term.subsume (subsumes : TwoCell modA modB) (term : Term ctx (Ty.modal modA ty) raw)
    : Term ctx (Ty.modal modB ty) (RawTerm.subsume raw)`

## Computation rules (Step / Step.par cases)

* `iotaModal : Step (Term.modElim (Term.modIntro term) cont) (cont.subst0_term ...)` —
  modElim of modIntro reduces to substituted continuation.  Detailed
  semantics depends on modality.
* `iotaSubsumeId : Step (Term.subsume (TwoCell.refl) t) t` — refl-subsume is identity
* Subsumption composition rules

## Dependencies

* `Foundation/Mode.lean` — Mode and Modality
* `Term.lean` — Term and Term.subst0

## Downstream consumers

* `Modal/Later.lean`, `Modal/Bridge.lean`, `Modal/Cap.lean`,
  `Modal/Ghost.lean`, `Modal/2LTT.lean` — concrete modalities

## Implementation plan (Phase 7)

1. Define modIntro/modElim/subsume in Term inductive (Layer 1
   already has scaffolding for them per `Term.lean`'s docstring)
2. Define iotaModal/iotaSubsumeId in Step/Step.par (Layer 2)
3. Verify reduction preserves typing
4. Smoke: trivial modIntro-modElim is identity (with refl modality)

## Diff from lean-fx

lean-fx had Modal as a v3.x roadmap (#920–#925).  lean-fx-2 ships
it as Layer 6 from day 1 — modal infrastructure is foundational.
-/

namespace LeanFX2

end LeanFX2
