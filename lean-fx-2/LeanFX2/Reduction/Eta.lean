import LeanFX2.Term.EtaRecognizers

/-! # Reduction/Eta — single-step η reduction (opt-in)

`Step.eta` is the keystone η rule, deliberately kept SEPARATE from
the βι `Step` inductive (see `Reduction/Step/Inductive.lean` header
comment).  Folding η into `Step` cascades through every βι confluence
arm: η's LHS `Term.lam (eta_lam_shape_construct functionTerm)` has a
structurally-weakened sub-term, so the cd-lemma against an arbitrary
`lam body`-step would need to invoke the strength-T1/T2 inverse-renaming
machinery in every βι case.  Keeping η here keeps βι Church-Rosser
textbook and Reduces the per-ctor cost of adding η from "rewrite ~80
βι arms" to "ship one new sibling inductive plus its own cd story".

The Geuvers 1992 β-η critical-pair joinability theorem still applies —
it is stated over the JOIN of the two relations (`Step ∨ Step.eta`).
Local confluence of η-alone follows from the rule being left-linear and
non-overlapping with itself.

## Shipped rules

* `Step.eta.etaLam`  — non-dependent arrow η:
  `Term.lam (fRaw.weaken `app` var 0)  ⟶  f`
* `Step.eta.etaPath` — cubical path η (mode = univalent):
  `Term.pathLam (pathRaw.weaken `pathApp` var 0)  ⟶  p`

## Deferred to follow-up

* `Step.eta.etaLamPi` (dependent Π η) — the `eta_lamPi_shape_body_construct`
  output sits at the codomain `(codomainType.rename RawRenaming.weaken.lift)
  .subst0 domainType.weaken (var 0)`, which is propositionally but not
  definitionally `codomainType`.  Forcing the equation requires a Ty-level
  substitution lemma + an HEq-cast Step ctor variant; sized out of the
  atomic P0.1 landing and tracked separately.

## Foundations consumed (all SHIPPED — accelerate-P0.1 prerequisites)

* `Term.eta_lam_shape_construct`  / `Term.eta_lam_shape_toRaw`
  (`Term/WeakenInverse.lean`, strength-T12-binder family).
* `Term.eta_path_shape_construct` / `Term.eta_path_shape_toRaw`
  (`Term/WeakenInverse.lean`, strength-T12-binder family).

## Zero-axiom

Inductives at this layer are foundational and carry no axioms
beyond Lean's built-in kernel machinery — no `propext`, no
`Classical.choice`, no `Quot.sound`.  Smoke harness elsewhere
(`Smoke/AuditEta.lean` — added alongside the par-level mirror in
accelerate-P0.2) exercises the constructors on concrete witnesses
and asserts axiom-cleanliness via `#assert_no_axioms`.
-/

namespace LeanFX2

/-- Single-step typed η reduction.  Sibling to the βι `Step`
inductive; combine on demand via `Step ∨ Step.eta`.

Source and target share `sourceType = targetType` (η preserves type
on the nose), but the two-Ty / two-RawTerm signature is retained for
symmetry with `Step` so downstream combinators can treat the two
relations uniformly. -/
inductive Step.eta :
    ∀ {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {sourceType targetType : Ty level scope}
      {sourceRaw targetRaw : RawTerm scope},
      Term context sourceType sourceRaw →
      Term context targetType targetRaw →
      Prop
  /-- η for the non-dependent arrow:
  `λ x. f x  ⟶_η  f` when the bound `x` does not occur free in `f`.

  Source raw  = `RawTerm.lam (RawTerm.app functionRaw.weaken (var 0))`
  Target raw  = `functionRaw`
  Both Ty     = `Ty.arrow domainType codomainType`

  The "binder-0 not free in `f`" side-condition is enforced
  BY CONSTRUCTION — the LHS is built via
  `Term.eta_lam_shape_construct functionTerm`, whose application-side
  function argument is literally `Term.weaken functionTerm` (raw form
  `functionRaw.weaken`).  A weakened term is not in the image of `var
  0` (the freshly-introduced binder slot), so the η-eligibility
  predicate holds definitionally — no `unweaken?` check needed
  in the rule's premises. -/
  | etaLam {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionRaw : RawTerm scope}
      (functionTerm :
        Term context (Ty.arrow domainType codomainType) functionRaw) :
      Step.eta
        (Term.lam (codomainType := codomainType)
                  (Term.eta_lam_shape_construct functionTerm))
        functionTerm
  /-- η for the cubical path:
  `λ i. p @ i  ⟶_η  p` when the bound interval index `i` does not
  occur in `p`.

  Source raw  = `RawTerm.pathLam (RawTerm.pathApp pathRaw.weaken (var 0))`
  Target raw  = `pathRaw`
  Both Ty     = `Ty.path carrierType leftEndpoint rightEndpoint`

  Like `etaLam`, the η-eligibility condition is by-construction:
  the LHS is built from `Term.eta_path_shape_construct pathTerm`,
  whose path-side argument is literally `Term.weaken pathTerm` under
  the fresh interval binder.  Restricted to `Mode.univalent` because
  the underlying `Term.pathLam` / `Term.pathApp` ctors require it. -/
  | etaPath {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint pathRaw : RawTerm scope}
      (pathTerm :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRaw) :
      Step.eta
        (Term.pathLam
          (mode := mode) (context := context)
          modeIsUnivalent carrierType leftEndpoint rightEndpoint
          (Term.eta_path_shape_construct modeIsUnivalent pathTerm))
        pathTerm

end LeanFX2
