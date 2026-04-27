import FX.Kernel.Level
import FX.Kernel.Grade

/-!
# Kernel term forms

The kernel term forms matching `fx_design.md` §31.2 and
Appendix H.  Trusted layer.  Zero `sorry`.  No `axiom`
declarations beyond the allowlist in `AXIOMS.md`.

## Phase status

**Phase 2.1 locks in** the Pi/Sigma/universe core plus the typed
pair/match-free fragment.  Kernel rejects `ind`/`coind` with
`T100` until their full metadata lands.

**Phase 2.2 (task A1)** splits the old placeholder `ind spec` into
three term forms and references inductive specs by name:

  * `ind typeName args` — the applied inductive type, e.g.
    `ind "Nat" []` or `ind "List" [i64]`.
  * `ctor typeName ctorIndex typeArgs args` — a fully-applied
    constructor, e.g. `ctor "Nat" 1 [] [Nat.zero]` for `Nat.succ
    Nat.zero`.
  * `indRec typeName motive methods target` — the eliminator.
    `indRec "Nat" P [p_zero, p_succ] n` iota-reduces per H.4.

Name-based indirection avoids a mutual inductive between `Term`
and `IndSpec`; the full `IndSpec` structure lives in
`FX/Kernel/Inductive.lean` and is looked up by name at every
typing / reduction site via `Inductive.specByName?`.

## Kernel terms

Every FX surface feature in §3-§26 reduces to a combination of
these via `FX.Derived.*`.
-/

namespace FX.Kernel

-- CoindSpec moved to FX/Kernel/Coinductive.lean per A2 — real
-- spec has destructors + size index, which means its fields
-- reference `Term`.  To avoid a mutual cycle with Term.lean, the
-- spec is name-indirected (same pattern `IndSpec` uses):
-- `Term.coind` stores a `(typeName, typeArgs)` reference, and
-- `Coinductive.specByName?` resolves the name at each typing /
-- reduction site.

/-- The kernel term forms.  This is the CLOSED set of syntactic
    constructors; every FX surface feature reduces to combinations
    of these via `FX.Derived.*`. -/
inductive Term : Type where
  /-- De Bruijn variable reference. -/
  | var    (deBruijnIndex : Nat) : Term
  /-- Function application. -/
  | app    (funcTerm : Term) (argTerm : Term) : Term
  /-- Graded lambda abstraction. -/
  | lam    (grade : Grade) (domain : Term) (body : Term) : Term
  /-- Graded dependent function type with a declared return-effect
      row.  Per `fx_design.md` §9 and Appendix B E-App, function
      types carry an effect annotation `{ef}` on their arrow —
      calling a `Π (x :_g A) →{ef} B` value incurs effects `ef`.

      The `grade` field describes the parameter-binder's
      requirements (e.g. linearity, lifetime, provenance — §6.2
      App rule scales the arg's grade by this); the
      `returnEffect` field describes what the *function* does
      when called.  These are dual in the typing calculus:
      `grade` is contravariant (what the caller must supply),
      `returnEffect` is covariant (what evaluating the call
      promises to the caller).

      Construction: elaboration of a surface `with IO, Alloc`
      row on a fn signature sets `returnEffect` on the
      constructed Pi.  Subtyping: a Pi `→{Tot}` is a subtype of
      a Pi `→{IO}` (Tot ≤ any effect row) — callers expecting
      effectful fns can safely receive pure ones.

      Per Appendix H.2 Pi-form. -/
  | pi     (grade : Grade) (domain : Term) (body : Term)
           (returnEffect : Effect) : Term
  /-- Graded dependent pair type. -/
  | sigma  (grade : Grade) (domain : Term) (body : Term) : Term
  /-- Universe at a given level. -/
  | type   (universeLevel : Level) : Term
  /-- Universal quantifier over a level (`Π (k : level). body`).
      The kernel's type-level form of universe polymorphism per
      `fx_design.md` §31.4 U-poly and Appendix H.1 U-poly.

      Distinct from `Term.pi` because levels are neither linear
      nor effectful — they're erased at compile time — so no
      grade or value-domain applies.  The `body` is a type (or
      further `forallLevel` chain) under a level scope one
      deeper than the surrounding context.

      Phase-2 scope: only the TYPE form.  Value-level `Λ k.
      body` abstraction and `f @ level` application are
      A10-followup work.  Until then, typing admits
      `forallLevel body` as a type but has no way to construct
      or apply a level-polymorphic value. -/
  | forallLevel (body : Term) : Term
  /-- Named reference to a top-level declaration (§31.8 / §10.15
      opaque-by-default body visibility).  Resolution is an
      environment lookup: typing consults `GlobalEnv.lookupType?`
      for the const's declared type; evaluation consults
      `GlobalEnv.lookupBody?` for its body.  Opaque by default —
      only delta-reduces at `whnf` when the decl is marked
      `@[transparent]`.  This ctor is the kernel's knot-tying
      mechanism for recursion and forward references: a decl's
      body may mention its own name as `Term.const` without
      requiring the body to be closed over a self binder. -/
  | const  (name : String) : Term
  /-- Applied inductive type, referenced by name.  `ind "List"
      [elemTy]` is the type `list(elemTy)`; `ind "Bool" []` is
      `bool`.  The spec itself lives in
      `FX/Kernel/Inductive.lean`. -/
  | ind    (typeName : String) (typeArgs : List Term) : Term
  /-- Fully-applied inductive constructor.  `ctor "Nat" 1 []
      [ctor "Nat" 0 [] []]` is `Nat.succ Nat.zero`.  `typeArgs`
      are the inductive type's parameters; `valueArgs` are the
      constructor's value arguments.  Partial application is
      represented by wrapping in a lambda at elaboration time. -/
  | ctor   (typeName : String) (ctorIndex : Nat)
           (typeArgs : List Term) (valueArgs : List Term) : Term
  /-- Inductive recursor (eliminator).  `indRec "Nat" motive
      [methodZero, methodSucc] target` — on iota-reduction, when
      `target = ctor "Nat" k _ ctorArgs`, reduces to `methods[k]`
      applied to `ctorArgs` (with recursive results
      auto-inserted for arguments whose type is the same
      inductive). -/
  | indRec (typeName : String) (motive : Term)
           (methods : List Term) (target : Term) : Term
  /-- Applied coinductive type, referenced by name.  Parallel to
      `Term.ind` for inductives — `coind "Stream" [elemTy]` is the
      type `Stream(elemTy)`.  The spec (destructors, size index,
      guardedness metadata) lives in `FX/Kernel/Coinductive.lean`
      as `CoindSpec`; the kernel resolves the reference via
      `Coinductive.specByName?`.  Per Appendix H.5 Coind-form. -/
  | coind  (typeName : String) (typeArgs : List Term) : Term
  /-- Coinductive-value introduction (`unfold`).  The dual of
      `Term.ctor` for codata — produces an inhabitant of the
      `typeName` coinductive by supplying one observation-arm per
      destructor in declaration order.  `typeArgs` are the
      coinductive type's parameters (so the introduced value
      has type `coind typeName typeArgs`); `arms` is the arm
      list, one term per destructor slot.  The surface
      `unfold<s> head => e₁; tail => e₂; end unfold` elaborates
      to `coindUnfold "stream" [elemTy] [e₁, e₂]` (size index
      handled separately by the `sized s;` clause at the fn
      signature level per §3.5).  Arms live in the same de
      Bruijn scope as the enclosing `coindUnfold` — there is no
      implicit "self" binder; recursion goes through a named
      `Term.const` to the enclosing `fn rec`.  Per Appendix H.5
      Coind-intro. -/
  | coindUnfold (typeName : String) (typeArgs : List Term)
                (arms : List Term) : Term
  /-- Coinductive-value elimination (single-destructor
      observation).  `coindDestruct "stream" 1 s` fires the
      destructor at index 1 (e.g., `tail`) on `s`.  The iota
      rule `coindDestruct name i (coindUnfold name _ arms) ≡
      arms[i]` lives in `FX/Kernel/Reduction.lean` as
      `nuStep?` — the dual of `iotaStep?` for inductives but
      without a motive, because a single observation has no
      branching structure to carry a case-discriminating motive
      through.  Per Appendix H.5 Coind-elim. -/
  | coindDestruct (typeName : String) (destructorIndex : Nat)
                  (target : Term) : Term
  /-- Identity type (propositional equality). -/
  | id     (baseType : Term) (leftTerm : Term) (rightTerm : Term) : Term
  /-- Identity-type introduction (`refl`).  `refl witness` is the
      canonical proof of `Id T witness witness` where `T` is the
      type of `witness`.  The type is not stored on the value —
      typing recovers it by inferring `witness`'s type.  Per
      Appendix H.6 Id-refl. -/
  | refl   (witness : Term) : Term
  /-- Identity-type elimination (J, path induction).  Given:
        motive  : Π (x y : T). Π (p : Id T x y). Type<v>
        base    : Π (x : T). motive x x (refl x)
        eqProof : Id T a b
      `idJ motive base eqProof` has type `motive a b eqProof`.
      The iota rule `idJ motive base (refl a) ≡ app base a`
      lives in `FX/Kernel/Reduction.lean`; the motive is
      consumed by typing and discarded at reduction time.  Per
      Appendix H.6 Id-J. -/
  | idJ    (motive : Term) (base : Term) (eqProof : Term) : Term
  /-- Quotient type under a relation. -/
  | quot   (carrier : Term) (relation : Term) : Term
  /-- Quotient-type introduction (`Quot.mk`).  `quotMk R a` is the
      canonical equivalence-class inhabitant `⟦a⟧_R : Quot T R`
      where `T` is the inferred type of `a`.  The relation `R` is
      stored so the typing layer can recover both the carrier (from
      `a`) and the relation (from the stored `relation` field);
      this matches Lean 4's `Quot.mk (r : α → α → Prop) (a : α)`.
      Per Appendix H.7 Quot-mk. -/
  | quotMk (relation : Term) (witness : Term) : Term
  /-- Quotient-type elimination (`Quot.lift`).  Given
        lifted   : T → U
        respects : Π (x y : T). R x y → Id U (lifted x) (lifted y)
        target   : Quot T R
      `quotLift lifted respects target` has type `U`.  The iota
      rule `quotLift f _ (quotMk _ a) ≡ app f a` lives in
      `FX/Kernel/Reduction.lean`; the respects-proof and stored
      relation are discarded at reduction time — both are
      purely typing obligations.  Per Appendix H.7 Quot-lift. -/
  | quotLift (lifted : Term) (respects : Term) (target : Term) : Term
  deriving Repr

/-- `Term` is inhabited by `.type .zero` — the simplest closed
    form.  Needed for `Inhabited CtxEntry` and downstream
    Lake-recognised partial-def return types. -/
instance : Inhabited Term := ⟨.type .zero⟩

namespace Term

/- Structural equality on kernel terms.  `Term` does NOT derive
   `DecidableEq` — the `Grade` field in `lam`/`pi`/`sigma` contains
   a `Provenance`, whose `List Provenance` recursion blocks Lean's
   auto-deriver.  `structEq` + `structEqList` walk the structure
   using `Grade.beq` for grade comparison and `decide (_ = _)` for
   Level.

   Used in two places: `FX/Kernel/Context.lean` `TypingContext.add`
   for shape-consistency checks on entries before grade addition,
   and downstream tests comparing inferred types to expected.
   Never used inside the kernel checker proper —
   `Conversion.lean` normalizes first, then compares, so its
   match cases cover convertibility rather than structural
   identity. -/

mutual

partial def structEq : Term → Term → Bool
  | .var leftIdx, .var rightIdx => leftIdx == rightIdx
  | .app leftFn leftArg, .app rightFn rightArg =>
    structEq leftFn rightFn && structEq leftArg rightArg
  | .lam leftGrade leftTy leftBody, .lam rightGrade rightTy rightBody =>
    Grade.beq leftGrade rightGrade
      && structEq leftTy rightTy && structEq leftBody rightBody
  | .pi leftGrade leftTy leftBody leftEffect,
    .pi rightGrade rightTy rightBody rightEffect =>
    Grade.beq leftGrade rightGrade
      && structEq leftTy rightTy && structEq leftBody rightBody
      && decide (leftEffect = rightEffect)
  | .sigma leftGrade leftTy leftBody, .sigma rightGrade rightTy rightBody =>
    Grade.beq leftGrade rightGrade
      && structEq leftTy rightTy && structEq leftBody rightBody
  | .type leftLevel, .type rightLevel => decide (leftLevel = rightLevel)
  | .forallLevel leftBody, .forallLevel rightBody =>
    structEq leftBody rightBody
  | .const leftName, .const rightName => leftName == rightName
  | .ind leftName leftArgs, .ind rightName rightArgs =>
    leftName == rightName && structEqList leftArgs rightArgs
  | .ctor leftName leftCtorIdx leftTypeArgs leftArgs,
    .ctor rightName rightCtorIdx rightTypeArgs rightArgs =>
    leftName == rightName && leftCtorIdx == rightCtorIdx
      && structEqList leftTypeArgs rightTypeArgs
      && structEqList leftArgs rightArgs
  | .indRec leftName leftMotive leftMethods leftTarget,
    .indRec rightName rightMotive rightMethods rightTarget =>
    leftName == rightName && structEq leftMotive rightMotive
      && structEqList leftMethods rightMethods
      && structEq leftTarget rightTarget
  | .coind leftName leftArgs, .coind rightName rightArgs =>
    leftName == rightName && structEqList leftArgs rightArgs
  | .coindUnfold leftName leftTypeArgs leftArms,
    .coindUnfold rightName rightTypeArgs rightArms =>
    leftName == rightName
      && structEqList leftTypeArgs rightTypeArgs
      && structEqList leftArms rightArms
  | .coindDestruct leftName leftIdx leftTarget,
    .coindDestruct rightName rightIdx rightTarget =>
    leftName == rightName && leftIdx == rightIdx
      && structEq leftTarget rightTarget
  | .id leftTy leftLhs leftRhs, .id rightTy rightLhs rightRhs =>
    structEq leftTy rightTy
      && structEq leftLhs rightLhs && structEq leftRhs rightRhs
  | .refl leftWitness, .refl rightWitness =>
    structEq leftWitness rightWitness
  | .idJ leftMotive leftBase leftEq, .idJ rightMotive rightBase rightEq =>
    structEq leftMotive rightMotive
      && structEq leftBase rightBase
      && structEq leftEq rightEq
  | .quot leftTy leftRel, .quot rightTy rightRel =>
    structEq leftTy rightTy && structEq leftRel rightRel
  | .quotMk leftRel leftWitness, .quotMk rightRel rightWitness =>
    structEq leftRel rightRel && structEq leftWitness rightWitness
  | .quotLift leftLifted leftRespects leftTarget,
    .quotLift rightLifted rightRespects rightTarget =>
    structEq leftLifted rightLifted
      && structEq leftRespects rightRespects
      && structEq leftTarget rightTarget
  | _, _ => false

/-- Pointwise `structEq` over two lists of terms. -/
partial def structEqList : List Term → List Term → Bool
  | [], [] => true
  | leftHead :: leftTail, rightHead :: rightTail =>
    structEq leftHead rightHead && structEqList leftTail rightTail
  | _, _ => false

end

instance : BEq Term := ⟨structEq⟩

/-- Convenience constructor for a Pi with `Effect.tot` return
    effect — the common case for pure kernel terms.  Avoids
    sprinkling `Effect.tot` at every test site after E-1 added
    the 4th positional field to `Term.pi`.  Surface fn types
    with declared `with …` rows construct `Term.pi` directly
    with the elaborated effect. -/
abbrev piTot (grade : Grade) (domain body : Term) : Term :=
  Term.pi grade domain body Effect.tot

end Term

end FX.Kernel
