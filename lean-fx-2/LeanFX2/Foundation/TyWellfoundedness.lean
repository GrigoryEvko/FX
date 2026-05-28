import LeanFX2.Foundation.Ty

/-! # Foundation/TyWellfoundedness
   — Ty.size measure + per-ctor structural-decrease lemmas

M-Ty-wf (#383, 2026-05-28).  Ships the well-foundedness measure
for Ty enabling type-directed recursion in both:

* `quote_atTy : ValueTerm → Ty → RawTerm` (M15a-e #359-#363) —
  η-long readback that descends per type former (Π → lam-of-app,
  Σ → pair-of-fst-snd, etc.).
* `Reducible : Ty → RawTerm → Prop` (M9-Tait-rescope #382) —
  Tait reducibility predicate inducting on Ty's type-former
  structure.

Without `Ty.size` and its structural-decrease lemmas, both
recursions hit Lean's termination wall: at Π type `(x : A) → B`,
recursion descends to codomain B at scope+1, which is "deeper"
in scope but not obviously smaller in Ty's structure.

## API surface

* `Ty.size : Ty level scope → Nat` — counts ctors recursively
  over Ty-children (RawTerm payloads NOT counted; only Ty
  substructure matters for type-directed recursion).
* `Ty.size_pos : ∀ ty, 0 < ty.size` — every type has positive
  size (no zero-size types).
* Per-ctor `size_lt_X_childN` lemmas for the binary + unary
  ctors that downstream recursions need (Π codomain smaller
  than piTy, Σ second smaller than sigmaTy, etc.).
* Auxiliary structural facts used by termination_by clauses.

## Why `Ty.size` not `sizeOf`

Lean's auto-derived `sizeOf` for an inductive over the entire
record (including RawTerm payloads via their own `sizeOf`).
For Ty.size we want to count ONLY Ty-substructure — RawTerm
endpoints (in `id`/`path`/`oeq`/`idStrict`/`glue`/`refine`/
`session`/`effect`) and Nat/Fin payloads don't contribute to
the well-foundedness measure for typed-quote recursion (the
recursion only descends into Ty children, not into raw payloads).

So we ship our own measure with the natural recursion-friendly
shape: 1 + sum of Ty-children sizes.

## Ctor count: 25 total

Per the Ty inductive declaration at `Foundation/Ty.lean:65-162`:

**Nullary in Ty** (8 ctors): unit, bool, nat, tyVar, universe,
empty, interval, session.  Size = 1.

**Unary in Ty** (11 ctors): listType, optionType, record, glue,
refine, effect, modal, id, path, oeq, idStrict.  Size = 1 +
childSize.

**Binary in Ty** (6 ctors): arrow, piTy, sigmaTy, eitherType,
equiv, codata.  Size = 1 + leftSize + rightSize.

## Proof technique

`Ty.size` defined by pattern-form structural recursion over
the indexed Ty inductive, mirroring `Ty.rename`'s style at
`Foundation/Ty.lean:171-225`.  Scope is left polymorphic;
level is hoisted to the function header per the multi-Nat-
index propext-avoidance recipe
(`feedback_lean_match_arity_axioms.md`).

Per-ctor `size_lt_X` lemmas close by `Nat`-arithmetic on the
`leftLtSumSucc` / `rightLtSumSucc` / `ltSuccSelf` shapes
mirroring `RawSize.lean`'s pattern.

## Zero-axiom verification

All declarations close by structural recursion or direct Nat
lemma application.  No `simp`, no `omega`, no `propext`.  The
pattern-form match on Ty is the same style as `Ty.rename`
which audit-clean per `#assert_no_axioms` in AuditTerm.
Audit-gated. -/

namespace LeanFX2

/-- Structural size measure for `Ty level scope`.

Counts ctors recursively over Ty-substructure.  Recursive
arms add up child sizes and add 1 for the current ctor.

Nullary ctors return 1.  Unary ctors return childSize + 1.
Binary ctors return leftSize + rightSize + 1.

RawTerm payloads (in `id`, `path`, `oeq`, `idStrict`, `glue`,
`refine`, `session`, `effect`) and other non-Ty payloads
(Fin / Nat / UniverseLevel) do NOT contribute to the size —
the measure is for type-directed recursion over Ty's TYPE
structure. -/
def Ty.size {level : Nat} : ∀ {scope : Nat}, Ty level scope → Nat
  -- Nullary (8 ctors): size = 1
  | _, .unit => 1
  | _, .bool => 1
  | _, .nat => 1
  | _, .tyVar _ => 1
  | _, .universe _ _ => 1
  | _, .empty => 1
  | _, .interval => 1
  | _, .session _ => 1
  -- Unary (11 ctors): size = childSize + 1
  | _, .listType elementType => elementType.size + 1
  | _, .optionType elementType => elementType.size + 1
  | _, .record singleFieldType => singleFieldType.size + 1
  | _, .glue baseType _ => baseType.size + 1
  | _, .refine baseType _ => baseType.size + 1
  | _, .effect carrierType _ => carrierType.size + 1
  | _, .modal _ carrierType => carrierType.size + 1
  | _, .id carrier _ _ => carrier.size + 1
  | _, .path carrier _ _ => carrier.size + 1
  | _, .oeq carrier _ _ => carrier.size + 1
  | _, .idStrict carrier _ _ => carrier.size + 1
  -- Binary (6 ctors): size = leftSize + rightSize + 1
  | _, .arrow domainType codomainType =>
      domainType.size + codomainType.size + 1
  | _, .piTy domainType codomainType =>
      domainType.size + codomainType.size + 1
  | _, .sigmaTy firstType secondType =>
      firstType.size + secondType.size + 1
  | _, .eitherType leftType rightType =>
      leftType.size + rightType.size + 1
  | _, .equiv domainType codomainType =>
      domainType.size + codomainType.size + 1
  | _, .codata stateType outputType =>
      stateType.size + outputType.size + 1

/-! ## Nat arithmetic shapes (private helpers) -/

private theorem Ty.leftLtSumSucc (leftVal rightVal : Nat) :
    leftVal < leftVal + rightVal + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_right leftVal rightVal)

private theorem Ty.rightLtSumSucc (leftVal rightVal : Nat) :
    rightVal < leftVal + rightVal + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_left rightVal leftVal)

private theorem Ty.ltSuccSelf (val : Nat) : val < val + 1 :=
  Nat.lt_succ_self val

/-! ## Positivity: every Ty has size ≥ 1 -/

/-- Every Ty has positive size (no zero-size types).  Useful for
downstream termination_by clauses that need a strict positive
lower bound. -/
theorem Ty.size_pos {level : Nat} : ∀ {scope : Nat} (someType : Ty level scope),
    0 < someType.size
  | _, .unit => Nat.zero_lt_succ _
  | _, .bool => Nat.zero_lt_succ _
  | _, .nat => Nat.zero_lt_succ _
  | _, .tyVar _ => Nat.zero_lt_succ _
  | _, .universe _ _ => Nat.zero_lt_succ _
  | _, .empty => Nat.zero_lt_succ _
  | _, .interval => Nat.zero_lt_succ _
  | _, .session _ => Nat.zero_lt_succ _
  | _, .listType _ => Nat.zero_lt_succ _
  | _, .optionType _ => Nat.zero_lt_succ _
  | _, .record _ => Nat.zero_lt_succ _
  | _, .glue _ _ => Nat.zero_lt_succ _
  | _, .refine _ _ => Nat.zero_lt_succ _
  | _, .effect _ _ => Nat.zero_lt_succ _
  | _, .modal _ _ => Nat.zero_lt_succ _
  | _, .id _ _ _ => Nat.zero_lt_succ _
  | _, .path _ _ _ => Nat.zero_lt_succ _
  | _, .oeq _ _ _ => Nat.zero_lt_succ _
  | _, .idStrict _ _ _ => Nat.zero_lt_succ _
  | _, .arrow _ _ => Nat.zero_lt_succ _
  | _, .piTy _ _ => Nat.zero_lt_succ _
  | _, .sigmaTy _ _ => Nat.zero_lt_succ _
  | _, .eitherType _ _ => Nat.zero_lt_succ _
  | _, .equiv _ _ => Nat.zero_lt_succ _
  | _, .codata _ _ => Nat.zero_lt_succ _

/-! ## Per-ctor structural-decrease lemmas

Each lemma states that a child Ty's size is strictly less than
its parent ctor's size.  Used by downstream recursions whose
termination_by clauses cite these as the proof obligation. -/

/-- Π codomain is structurally smaller than Π type (binder shift
preserves measure-positivity).  Used by M15b η-long quote at Π
types + M9-Tait's Π-arm. -/
theorem Ty.size_lt_piTy_codomain {level scope : Nat}
    (domainType : Ty level scope)
    (codomainType : Ty level (scope + 1)) :
    codomainType.size < (Ty.piTy domainType codomainType).size :=
  Ty.rightLtSumSucc _ _

/-- Π domain is structurally smaller than Π type. -/
theorem Ty.size_lt_piTy_domain {level scope : Nat}
    (domainType : Ty level scope)
    (codomainType : Ty level (scope + 1)) :
    domainType.size < (Ty.piTy domainType codomainType).size :=
  Ty.leftLtSumSucc _ _

/-- Σ second is structurally smaller than Σ type. -/
theorem Ty.size_lt_sigmaTy_second {level scope : Nat}
    (firstType : Ty level scope)
    (secondType : Ty level (scope + 1)) :
    secondType.size < (Ty.sigmaTy firstType secondType).size :=
  Ty.rightLtSumSucc _ _

/-- Σ first is structurally smaller than Σ type. -/
theorem Ty.size_lt_sigmaTy_first {level scope : Nat}
    (firstType : Ty level scope)
    (secondType : Ty level (scope + 1)) :
    firstType.size < (Ty.sigmaTy firstType secondType).size :=
  Ty.leftLtSumSucc _ _

/-- arrow domain. -/
theorem Ty.size_lt_arrow_domain {level scope : Nat}
    (domainType codomainType : Ty level scope) :
    domainType.size < (Ty.arrow domainType codomainType).size :=
  Ty.leftLtSumSucc _ _

/-- arrow codomain. -/
theorem Ty.size_lt_arrow_codomain {level scope : Nat}
    (domainType codomainType : Ty level scope) :
    codomainType.size < (Ty.arrow domainType codomainType).size :=
  Ty.rightLtSumSucc _ _

/-- eitherType left. -/
theorem Ty.size_lt_eitherType_left {level scope : Nat}
    (leftType rightType : Ty level scope) :
    leftType.size < (Ty.eitherType leftType rightType).size :=
  Ty.leftLtSumSucc _ _

/-- eitherType right. -/
theorem Ty.size_lt_eitherType_right {level scope : Nat}
    (leftType rightType : Ty level scope) :
    rightType.size < (Ty.eitherType leftType rightType).size :=
  Ty.rightLtSumSucc _ _

/-- equiv domain. -/
theorem Ty.size_lt_equiv_domain {level scope : Nat}
    (domainType codomainType : Ty level scope) :
    domainType.size < (Ty.equiv domainType codomainType).size :=
  Ty.leftLtSumSucc _ _

/-- equiv codomain. -/
theorem Ty.size_lt_equiv_codomain {level scope : Nat}
    (domainType codomainType : Ty level scope) :
    codomainType.size < (Ty.equiv domainType codomainType).size :=
  Ty.rightLtSumSucc _ _

/-- codata state. -/
theorem Ty.size_lt_codata_state {level scope : Nat}
    (stateType outputType : Ty level scope) :
    stateType.size < (Ty.codata stateType outputType).size :=
  Ty.leftLtSumSucc _ _

/-- codata output. -/
theorem Ty.size_lt_codata_output {level scope : Nat}
    (stateType outputType : Ty level scope) :
    outputType.size < (Ty.codata stateType outputType).size :=
  Ty.rightLtSumSucc _ _

/-- listType element. -/
theorem Ty.size_lt_listType_element {level scope : Nat}
    (elementType : Ty level scope) :
    elementType.size < (Ty.listType elementType).size :=
  Ty.ltSuccSelf _

/-- optionType element. -/
theorem Ty.size_lt_optionType_element {level scope : Nat}
    (elementType : Ty level scope) :
    elementType.size < (Ty.optionType elementType).size :=
  Ty.ltSuccSelf _

/-- record single-field. -/
theorem Ty.size_lt_record_singleField {level scope : Nat}
    (singleFieldType : Ty level scope) :
    singleFieldType.size < (Ty.record singleFieldType).size :=
  Ty.ltSuccSelf _

/-- modal carrier. -/
theorem Ty.size_lt_modal_carrier {level scope : Nat}
    (modalityTag : Nat) (carrierType : Ty level scope) :
    carrierType.size < (Ty.modal modalityTag carrierType).size :=
  Ty.ltSuccSelf _

/-- glue base. -/
theorem Ty.size_lt_glue_base {level scope : Nat}
    (baseType : Ty level scope) (boundaryWitness : RawTerm scope) :
    baseType.size < (Ty.glue baseType boundaryWitness).size :=
  Ty.ltSuccSelf _

/-- refine base. -/
theorem Ty.size_lt_refine_base {level scope : Nat}
    (baseType : Ty level scope)
    (predicate : RawTerm (scope + 1)) :
    baseType.size < (Ty.refine baseType predicate).size :=
  Ty.ltSuccSelf _

/-- effect carrier. -/
theorem Ty.size_lt_effect_carrier {level scope : Nat}
    (carrierType : Ty level scope) (effectTag : RawTerm scope) :
    carrierType.size < (Ty.effect carrierType effectTag).size :=
  Ty.ltSuccSelf _

/-- id carrier. -/
theorem Ty.size_lt_id_carrier {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    carrier.size < (Ty.id carrier leftEndpoint rightEndpoint).size :=
  Ty.ltSuccSelf _

/-- path carrier. -/
theorem Ty.size_lt_path_carrier {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    carrier.size < (Ty.path carrier leftEndpoint rightEndpoint).size :=
  Ty.ltSuccSelf _

/-- oeq carrier. -/
theorem Ty.size_lt_oeq_carrier {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    carrier.size < (Ty.oeq carrier leftEndpoint rightEndpoint).size :=
  Ty.ltSuccSelf _

/-- idStrict carrier. -/
theorem Ty.size_lt_idStrict_carrier {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    carrier.size < (Ty.idStrict carrier leftEndpoint rightEndpoint).size :=
  Ty.ltSuccSelf _

end LeanFX2
