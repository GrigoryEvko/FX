import FX1Poly.Polygraph.Computad.Signature

/-! # Polygraph/Computad/PathFactorization — the self-certifying prefix splitter

The decidable 1-cell prefix factorization: given a candidate prefix and a longer path with
the same source, either produce the unique suffix WITH its factorization proof, or a proof
that NO suffix factors.  Both certificates ride inside the return value (the `Decidable`
discipline), so the splitter needs NO companion soundness/completeness lemmas — consumers
`match` and use the carried proofs directly.  This is the recognizer substrate for the
atom-level swap decision (FREE-6/7): whether two adjacent spine atoms form a swap pair is a
pair of prefix factorizations of their whiskering contexts.

Structural recursion on the prefix; the mode/modality mismatch certificates reuse the
`modalityPathDecEq` discriminators (`length` for the too-short case, `firstStepTarget` for
distinct middle modes, `injection` + `eq_of_heq` for same-index heads).  Raw Lean 4 + Init;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The self-certifying prefix splitter**: either the suffix with its factorization
proof, or a proof that no suffix factors.  Uniqueness of the suffix is automatic downstream
(`composePathLeftCancel`). -/
def ModalityPath.splitPrefix {graph : ModeGraph}
    (modeDecEq : DecidableEq graph.Mode)
    (modalityDecEq : (sourceMode targetMode : graph.Mode) →
      DecidableEq (graph.Modality sourceMode targetMode)) :
    {startMode midMode endMode : graph.Mode} →
    (prefixPath : ModalityPath graph startMode midMode) →
    (longPath : ModalityPath graph startMode endMode) →
    PSum
      { suffixPath : ModalityPath graph midMode endMode //
        longPath = composePath prefixPath suffixPath }
      (∀ suffixPath : ModalityPath graph midMode endMode,
        longPath ≠ composePath prefixPath suffixPath)
  | _, _, _, .nil _, longPath => PSum.inl ⟨longPath, rfl⟩
  | _, _, _, .cons _ _, .nil _ =>
      PSum.inr (fun _suffixPath composedEqual =>
        Nat.noConfusion (congrArg ModalityPath.length composedEqual))
  | _, _, _, @ModalityPath.cons _ _ prefixMiddleMode _ prefixModality prefixRest,
      @ModalityPath.cons _ _ longMiddleMode _ longModality longRest =>
      match modeDecEq longMiddleMode prefixMiddleMode with
      | .isFalse middlesDiffer =>
          PSum.inr (fun _suffixPath composedEqual =>
            middlesDiffer (Option.some.inj
              (congrArg ModalityPath.firstStepTarget composedEqual)))
      | .isTrue middlesEqual => by
          subst middlesEqual
          exact match modalityDecEq _ _ longModality prefixModality with
          | .isFalse modalitiesDiffer =>
              PSum.inr (fun suffixPath composedEqual => by
                have consEqual : ModalityPath.cons longModality longRest
                    = ModalityPath.cons prefixModality
                        (composePath prefixRest suffixPath) := composedEqual
                injection consEqual with _sourceEqual _middleEqual _targetEqual
                  modalityEqual _restEqual
                exact modalitiesDiffer modalityEqual)
          | .isTrue modalitiesEqual =>
              match ModalityPath.splitPrefix modeDecEq modalityDecEq prefixRest longRest
                  with
              | .inl ⟨suffixPath, suffixFactors⟩ =>
                  PSum.inl ⟨suffixPath, by rw [modalitiesEqual, suffixFactors]; rfl⟩
              | .inr restNeverFactors =>
                  PSum.inr (fun suffixPath composedEqual => by
                    have consEqual : ModalityPath.cons longModality longRest
                        = ModalityPath.cons prefixModality
                            (composePath prefixRest suffixPath) := composedEqual
                    injection consEqual with _sourceEqual _middleEqual _targetEqual
                      _modalityEqual restEqual
                    exact restNeverFactors suffixPath restEqual)

end FX1Poly.Polygraph
