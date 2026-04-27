import FX.KernelMTT.Term
import FX.KernelMTT.Substitution

/-!
# Reduction over the well-scoped mode-indexed Term (V1.15)

Single-step reductions and weak head normalization for the W2 +
W3 well-scoped `Term : Nat → Type`.  Every reduction is
`Term n → Term n` (or `Option (Term n)` for the per-rule
predicates) — out-of-range scoping is structurally impossible
because shift / subst (W3) preserve the index.

## Six reduction rules

  * **β** (`betaStep?`) — App on Lam dispatches to subst:
    `(λ x. body) arg ↦ body[0 := arg]`.

  * **ι** (`iotaIndRecStep?`) — Inductive recursor on a ctor:
    `indRec C mot ms (ctor C i ts vs) ↦ ms[i] applied to vs`.
    V1.15 minimum: NO auto-insertion of induction hypotheses.
    A user wanting recursion on a recursive inductive must
    supply the IH manually.  Auto-IH is a follow-on task once
    the IndSpec lookup is wired through KernelMTT.

  * **ν** (`nuStep?`) — Coinductive destructor on coindUnfold:
    `destructIdx (unfold T arms) ↦ arms[destructIdx]`.

  * **modElim-ι** (`modElimIotaStep?`) — modElim on modIntro:
    `modElim _ _ μ (modIntro _ _ μ inner) body ↦
      body[0 := inner]` when the modalities match.

  * **idJ-ι** (`idJIotaStep?`) — Identity J on refl:
    `idJ mot base (refl _ w) ↦ base w`.

  * **coerceCell-strip** (`coerceCellStrip?`) — 2-cell
    subsumption coercion is a no-op marker that can always be
    removed: `coerceCell _ _ _ inner ↦ inner`.

## whnf

`whnf : Nat → Term n → Term n` applies the six rules until the
term is in weak head normal form or fuel is exhausted.  At
every step it first reduces the head subterm (the function of
an App, the target of an indRec / coindDestruct / idJ, the
modalTerm of modElim) so that the head reduction can fire.

Strips outermost coerceCell eagerly — the coercion is purely a
typing artifact and never blocks reduction.

## What's not here

Auto-IH for ι (mentioned above), full normalization (whnf goes
to weak head form only; full normalization recurses under
binders), η-conversion (a *convertibility* rule per Appendix
H.9, lives in Conversion.lean not Reduction.lean), and
transport-iota (depends on the equivalence proof's encoding,
deferred to V2.17).

## Termination

`whnf` is fuel-bounded.  Per-rule `step?` functions are total
(structural pattern match returning Option).  `whnf` itself is
`partial def` because the recursion includes substitution,
which can in principle grow the term.  Fuel exhaustion returns
the partially-reduced term, matching the legacy kernel's
discipline.

## Trust layer

`FX/KernelMTT/**` is UNTRUSTED scaffold.  Zero `sorry`, zero new
axioms.  Soundness of reductions established at runtime via
`tests/Tests/KernelMTT/ReductionTests.lean`; mechanized
preservation theorems are V_meta scope.

## Cross-references

  * `FX/KernelMTT/Term.lean` — well-scoped Term inductive
  * `FX/KernelMTT/Substitution.lean` — shift / subst primitives
  * `FX/Kernel/Reduction.lean` — legacy un-indexed counterpart
    (returns same `Term` type, scope safety is checker-enforced)
  * `fx_design.md` §30 — kernel β / ι / ν / η axioms
  * Appendix H.4 (Ind-ι), H.5 (Coind-ν), H.6 (Id-J), H.7 (HIT)
-/

namespace FX.KernelMTT

namespace TermArgs

/-- `nth` access on a `TermArgs n`.  Returns `none` on
    out-of-range index.  Used by ι and ν to select the relevant
    method or arm by constructor / destructor index. -/
def get? {n : Nat} : TermArgs n → Nat → Option (Term n)
  | .nil,       _    => none
  | .cons h _,  0    => some h
  | .cons _ t,  k+1  => get? t k

end TermArgs

namespace Term

/-- Apply `head` to each element of `args` left-to-right,
    building `app head args[0] |> app args[1] |> ...`.  Used
    by ι to apply the selected inductive method to the
    constructor's value arguments. -/
def applyArgs {n : Nat} (mode : Mode) (head : Term n) :
    TermArgs n → Term n
  | .nil       => head
  | .cons x xs => applyArgs mode (Term.app mode head x) xs

/-- β-reduction.  `(λ x. body) arg ↦ body[0 := arg]`. -/
def betaStep? {n : Nat} : Term n → Option (Term n)
  | .app _ (.lam _ _ _ body) arg => some (Term.subst body arg)
  | _ => none

/-- ι-reduction on inductive recursors.

    `indRec C mot ms (ctor C i ts vs) ↦ ms[i] applied to vs`
    when the recursor's type name matches the ctor's type
    name and the method index is in range.

    V1.15 minimum: no auto-IH; recursive inductive arguments
    that should carry an induction hypothesis are passed
    through unchanged.  The user supplies the IH manually
    until the IndSpec lookup wires through KernelMTT. -/
def iotaIndRecStep? {n : Nat} : Term n → Option (Term n)
  | .indRec recMode recTypeName _mot ms
      (.ctor _ ctorTypeName ctorIdx _ts vs) =>
    if recTypeName == ctorTypeName then
      match TermArgs.get? ms ctorIdx with
      | some method => some (applyArgs recMode method vs)
      | none        => none
    else
      none
  | _ => none

/-- ν-reduction on coinductive destructors.

    `coindDestruct C i (coindUnfold C ts arms) ↦ arms[i]`
    when the destructor's type name matches the unfold's. -/
def nuStep? {n : Nat} : Term n → Option (Term n)
  | .coindDestruct _ destTypeName destIdx
      (.coindUnfold _ unfoldTypeName _ts arms) =>
    if destTypeName == unfoldTypeName then
      TermArgs.get? arms destIdx
    else
      none
  | _ => none

/-- modElim-ι reduction.

    `modElim _ _ μ (modIntro _ _ μ inner) body ↦
       body[0 := inner]`
    when the eliminator's modality equals the introduction's.
    Mode coherence (outer src = inner tgt, etc.) is the V1.5
    checker's obligation; this step fires whenever the
    modalities agree. -/
def modElimIotaStep? {n : Nat} : Term n → Option (Term n)
  | .modElim _ _ elimMod
      (.modIntro _ _ introMod inner) body =>
    if decide (elimMod = introMod) then
      some (Term.subst body inner)
    else
      none
  | _ => none

/-- idJ-ι reduction.

    `idJ m mot base (refl _ w) ↦ app m base w`.

    For the J base case at `refl w`, J reduces to the base
    function applied to `w`.  Standard MLTT identity-elim
    iota rule (Appendix H.6 Id-J). -/
def idJIotaStep? {n : Nat} : Term n → Option (Term n)
  | .idJ recMode _mot base (.refl _ w) =>
    some (Term.app recMode base w)
  | _ => none

/-- coerceCell strip.  A 2-cell subsumption coercion records
    a typing-time witness that one grade is reachable from
    another in the modality's preorder; semantically it is
    the identity, so any reduction may strip it. -/
def coerceCellStrip? {n : Nat} : Term n → Option (Term n)
  | .coerceCell _ _ _ inner => some inner
  | _ => none

/-- Try one head-level reduction.  Order: coerceCell strip
    first (always applicable, exposes the underlying head),
    then β, ι, ν, modElim-ι, idJ-ι.

    Returns `none` if no head rule fires.  Used by callers that
    want to inspect a single step rather than iterate to whnf. -/
def headStep? {n : Nat} (t : Term n) : Option (Term n) :=
  match coerceCellStrip? t with
  | some t' => some t'
  | none =>
  match betaStep? t with
  | some t' => some t'
  | none =>
  match iotaIndRecStep? t with
  | some t' => some t'
  | none =>
  match nuStep? t with
  | some t' => some t'
  | none =>
  match modElimIotaStep? t with
  | some t' => some t'
  | none =>
  idJIotaStep? t

/-- Default fuel for `whnf`.  Matches the legacy kernel's
    `defaultFuel` so kernel reductions converge on the same
    bound across V1.5's parallel-kernel dispatch. -/
def defaultFuel : Nat := 4096

/-- Weak head normal form via fuel-bounded reduction.  Recurses
    into the head subterm before attempting head reduction at
    every level (function of App, target of indRec /
    coindDestruct / idJ, modalTerm of modElim).  Strips
    outermost coerceCell eagerly.  Returns the input unchanged
    on fuel exhaustion. -/
partial def whnf {n : Nat} (fuel : Nat) (t : Term n) : Term n :=
  match fuel with
  | 0 => t
  | f + 1 =>
    match t with
    -- Strip coerceCell eagerly; expose the underlying head.
    | .coerceCell _ _ _ inner => whnf f inner
    -- β: recurse into function, then check for lam.
    | .app m fn arg =>
      let fn' := whnf f fn
      match fn' with
      | .lam _ _ _ body => whnf f (Term.subst body arg)
      | _               => Term.app m fn' arg
    -- ι: recurse into target, then check for ctor.
    | .indRec m name mot ms tgt =>
      let tgt' := whnf f tgt
      match tgt' with
      | .ctor _ ctorTypeName ctorIdx _ vs =>
        if name == ctorTypeName then
          match TermArgs.get? ms ctorIdx with
          | some method => whnf f (applyArgs m method vs)
          | none        => Term.indRec m name mot ms tgt'
        else
          Term.indRec m name mot ms tgt'
      | _ => Term.indRec m name mot ms tgt'
    -- ν: recurse into target, then check for coindUnfold.
    | .coindDestruct m name destIdx tgt =>
      let tgt' := whnf f tgt
      match tgt' with
      | .coindUnfold _ unfoldName _ arms =>
        if name == unfoldName then
          match TermArgs.get? arms destIdx with
          | some arm => whnf f arm
          | none     => Term.coindDestruct m name destIdx tgt'
        else
          Term.coindDestruct m name destIdx tgt'
      | _ => Term.coindDestruct m name destIdx tgt'
    -- idJ: recurse into eq proof, then check for refl.
    | .idJ m mot base eq =>
      let eq' := whnf f eq
      match eq' with
      | .refl _ w => whnf f (Term.app m base w)
      | _         => Term.idJ m mot base eq'
    -- modElim-ι: recurse into modal term, then check for modIntro.
    | .modElim src tgt elimMod modT body =>
      let modT' := whnf f modT
      match modT' with
      | .modIntro _ _ introMod inner =>
        if decide (elimMod = introMod) then
          whnf f (Term.subst body inner)
        else
          Term.modElim src tgt elimMod modT' body
      | _ => Term.modElim src tgt elimMod modT' body
    -- All other forms are already in head normal form (var,
    -- lam, pi, sigma, type, forallLevel, const, ind, ctor,
    -- coind, coindUnfold, id, refl, hit, hitMk, hitRec,
    -- modIntro, transport).
    | _ => t

end Term

end FX.KernelMTT
