import FX1Poly.Typed.HasTypeInfer

/-! # FX1Poly/Typed/HasTypeCheck
    — bidirectional type CHECKING (`check`) for the native pi/sigma-formation HasType core

The check half of bidirectional typing: "does `subject` have the GIVEN type
`targetType`?".  The synthesis-based decision procedure: synthesise `subject`'s
type with `infer` (#478), then coerce it to `targetType` via the conversion rule,
gated by a decidable `Conv`.  Returning `Decidable (HasType Γ subject targetType)`
makes it sound AND complete **by construction** — `isTrue` carries the derivation,
`isFalse` the refutation — so no separate completeness theorem is needed.  (A
literal `Option (HasType …)` cannot be formed: `HasType … : Prop` is not in
`Type`; `Decidable` is the faithful realisation of the spec's "`Option HasType`".)

```
HasType.check : WfContext Γ → (t T : RawTerm scope) → Decidable (HasType Γ t T)
```

This is the GENERAL bidirectional method — it rests only on `infer`, the generic
decidable `Conv` (`Conv.decidableOfIsType`), and the conversion rule, NOT on the
fragment-specific collapse-to-classifier-equality that powers the direct decider
`HasType.decidableOfWellFormed` (#461).  On the native pi/sigma-formation HasType core the two
necessarily decide the same judgment (any two `Decidable p` agree).  `check` is a
parallel decision procedure independent of the fragment-specific collapse — the
synthesise-then-convert skeleton decides typing through `infer` and `Conv` alone,
not a new capability over the direct decider on this fragment.

## The three refutation arms (the real metatheory)

* `infer = none` ⇒ `¬ HasType`: contrapositive of `infer_succeeds` (#478) — a
  typeable subject always synthesises.
* `decideWithWitness targetType = .inr` (target not a type) ⇒ `¬ HasType`: by
  validity (`classifierIsType`), a well-typed subject's classifier is a type.
* `Conv synthType targetType = isFalse` ⇒ `¬ HasType`: by uniqueness of typing
  (#469), the synthesised and target classifiers of a common subject convert.

## Zero-axiom verification

`check` is nested `match`es on `infer` / `decideWithWitness` / the `Conv`
decision (all non-indexed `Option` / `PSum` / `Decidable`), with the refutations
inline; sound+complete by construction.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Bidirectional type checking (#479): decide whether `subject` has the
given `targetType`.  Synthesise with `infer`; confirm `targetType` inhabits a
universe (`decideWithWitness`, which also yields the `targetType : Type@(lvl,
flag)` derivation the conv rule needs); decide `Conv synthType targetType`; on
success coerce via `HasType.conv`.  The three failure arms refute typehood via
`infer_succeeds` / validity / uniqueness — so the result is sound AND complete by
construction. -/
def HasType.check {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (subject targetType : RawTerm scope) :
    Decidable (HasType profile context subject targetType) :=
  match hInfer : HasType.infer wellFormed subject with
  | none =>
      isFalse (fun typed => by
        obtain ⟨_, inferSome⟩ := HasType.infer_succeeds wellFormed typed
        rw [hInfer] at inferSome
        contradiction)
  | some ⟨synthType, synthDeriv⟩ =>
      match IsType.decideWithWitness wellFormed targetType with
      | .inr targetNotType =>
          isFalse (fun typed =>
            targetNotType (HasType.classifierIsType wellFormed typed))
      | .inl ⟨targetLevel, targetFlag, targetTyped⟩ =>
          match Conv.decidableOfIsType
              (HasType.classifierIsType wellFormed synthDeriv)
              ⟨targetLevel, targetFlag, targetTyped⟩ with
          | isTrue convProof =>
              isTrue (HasType.conv targetLevel targetFlag synthDeriv convProof
                targetTyped)
          | isFalse convRefute =>
              isFalse (fun typed =>
                convRefute (HasType.uniqueness wellFormed synthDeriv typed))

end FX1Poly.Typed
