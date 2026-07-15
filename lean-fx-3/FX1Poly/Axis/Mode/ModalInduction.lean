import FX1Poly.Axis.Mode.Mode

/-! # mode-10 — crisp/modal induction: the modal eliminator coherence + crisp-J

A multimodal type theory adds, per modality `μ` of the mode theory, a MODAL TYPE `⟨μ | A⟩` with an introduction
and a dependent ELIMINATOR, and — for the identity type in a modal (crisp / flat) context — a CRISP path
induction (`crisp-J`).  The metatheoretic obligation is COHERENCE: the eliminators' β-computation rules hold.
`mode-10` ships those eliminators abstractly with their β-coherence, concrete zero-axiom witnesses, and the
derived consequences that exercise the β rules (so this is not merely an interface).

## What this file ships (each piece zero-axiom)

  * **`ModalEliminator`** — the modal type former `⟨μ | -⟩` with `intro`, a DEPENDENT `elim`, and the β-rule
    (`elim` on an introduced value reduces to the method).  `identityModalEliminator` is the concrete witness
    (the identity modality, β by `rfl`).  Derived: `mapModal` (functoriality of the modal type) +
    `mapModal_intro` (its computation, PROVED via β).
  * **`CrispJ`** — the J eliminator for the identity type with its β-rule (`J` on `refl` reduces to the base
    case) — the principle that becomes crisp-J in a flat context.  `equalityCrispJ` is the concrete witness
    (the meta identity via `Eq.rec`, β by `rfl`).  Derived: `transport` + `transport_refl` (transport along
    `refl` is the identity, PROVED via β) — the real consequence of path induction.
  * the mode tie: `identityModalEliminator.ModalType A = A` — the identity modality (the identity 1-cell of the
    mode theory) acts as the identity type former.

## Also shipped — the mode-indexed eliminator

  * **`ModeIndexedModalEliminator`** — modal types INDEXED by `mode-1`'s `ModalityPath` 1-cells (per-modality
    intro / elim / β), FUNCTORIAL in 1-cell composition (`composeLaw`), transparent at the identity, with the
    2-cell subsumption along the locally-discrete 2-cells (`subsumeEq`) + the identity witness + `mapModal`.

## What is DEFERRED (markers)

  * the subsumption over `mode-3`'s GENUINE (non-discrete) free 2-cells, with naturality coherence — the
    remaining half of `hasModeIndexedModalEliminator`;
  * the connection to the kernel's modal SYNTAX (`gen_modIntro` / `gen_modElim` / `gen_subsume`) — cross-axis
    (`hasKernelModalSyntaxConnection`, `fib`);
  * crisp-J in a genuine FLAT / ♭ cohesive context (Shulman's real-cohesive HoTT), beyond the abstract J
    principle modeled here (`hasRealCohesiveCrispJ`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## The modal eliminator (modal induction) -/

/-- A **modal eliminator** — the modal type former `⟨μ | -⟩` with an introduction, a DEPENDENT elimination, and
the β-COHERENCE: eliminating an introduced value computes to the corresponding method.  (Modeled
modality-agnostically; the mode-indexed, 2-cell-functorial version is deferred — see the markers.) -/
structure ModalEliminator where
  /-- The modal type former. -/
  ModalType : Type → Type
  /-- Introduction: a value enters the modal type. -/
  intro : {A : Type} → A → ModalType A
  /-- Dependent elimination into a motive over the modal type. -/
  elim : {A : Type} → (motive : ModalType A → Type) →
    (method : (value : A) → motive (intro value)) → (modalValue : ModalType A) → motive modalValue
  /-- The β-coherence: elimination of an introduced value is the method on that value. -/
  beta : {A : Type} → (motive : ModalType A → Type) →
    (method : (value : A) → motive (intro value)) → (value : A) →
    elim motive method (intro value) = method value

/-- The **identity modality** as a modal eliminator — the modal type is the identity type former, introduction
and elimination are transparent, and β holds by `rfl`.  The concrete witness that the modal-eliminator
coherence is satisfiable. -/
def identityModalEliminator : ModalEliminator where
  ModalType := fun carrier => carrier
  intro := fun value => value
  elim := fun _motive method modalValue => method modalValue
  beta := fun _motive _method _value => rfl

/-- **Functoriality of the modal type** — a map `A → B` lifts to `ModalType A → ModalType B`, by eliminating
into the (constant) motive `ModalType B` and re-introducing.  Derived from `elim`. -/
def ModalEliminator.mapModal (modalElim : ModalEliminator) {A B : Type} (mapFunction : A → B) :
    modalElim.ModalType A → modalElim.ModalType B :=
  modalElim.elim (fun _ => modalElim.ModalType B) (fun value => modalElim.intro (mapFunction value))

/-- ★ The functorial lift's COMPUTATION rule — `mapModal f (intro a) = intro (f a)` — PROVED via the
β-coherence (a genuine use of the modal eliminator's computation). -/
theorem ModalEliminator.mapModal_intro (modalElim : ModalEliminator) {A B : Type} (mapFunction : A → B)
    (value : A) :
    modalElim.mapModal mapFunction (modalElim.intro value) = modalElim.intro (mapFunction value) :=
  modalElim.beta (fun _ => modalElim.ModalType B)
    (fun innerValue => modalElim.intro (mapFunction innerValue)) value

/-- The identity modality's type former is the identity — the identity 1-cell of the mode theory acts trivially
on types.  The mode tie. -/
theorem identityModalEliminator_modalType (carrier : Type) :
    identityModalEliminator.ModalType carrier = carrier := rfl

/-! ## Crisp path induction (crisp-J) -/

/-- **Crisp-J** — the J eliminator for the identity type with its β-rule (`J` on `refl` is the base case).  This
is the path-induction principle that, in a FLAT / ♭ (crisp) context, becomes Shulman's crisp-J; the crispness
(the flat context) is the deferred real-cohesive part (see the marker), while the J principle + its computation
are modeled here. -/
structure CrispJ where
  /-- The identity type (propositional here; the Type-valued cubical version is deferred). -/
  Id : {A : Type} → A → A → Prop
  /-- Reflexivity. -/
  refl : {A : Type} → (point : A) → Id point point
  /-- Path induction into a motive over the based path space. -/
  J : {A : Type} → (basePoint : A) →
    (motive : (endPoint : A) → Id basePoint endPoint → Type) →
    (baseCase : motive basePoint (refl basePoint)) →
    (endPoint : A) → (path : Id basePoint endPoint) → motive endPoint path
  /-- The β-rule: path induction on `refl` is the base case. -/
  beta : {A : Type} → (basePoint : A) →
    (motive : (endPoint : A) → Id basePoint endPoint → Type) →
    (baseCase : motive basePoint (refl basePoint)) →
    J basePoint motive baseCase basePoint (refl basePoint) = baseCase

/-- The meta identity (`Eq`) as a crisp-J witness — `J` is `Eq.rec` (large elimination of the subsingleton
`Eq`, axiom-free) and β holds by `rfl`.  The concrete witness that the crisp-J coherence is satisfiable. -/
def equalityCrispJ : CrispJ where
  Id := fun pointA pointB => pointA = pointB
  refl := fun _point => rfl
  J := fun basePoint motive baseCase endPoint path =>
    @Eq.rec _ basePoint (fun resultPoint resultPath => motive resultPoint resultPath) baseCase endPoint path
  beta := fun _basePoint _motive _baseCase => rfl

/-- **Transport** — derived from crisp-J: a path `a = b` carries `P a` to `P b` (J into the motive
`P a → P endPoint`, base the identity). -/
def CrispJ.transport (crispJ : CrispJ) {A : Type} (typeFamily : A → Type)
    {basePoint endPoint : A} (path : crispJ.Id basePoint endPoint)
    (point : typeFamily basePoint) : typeFamily endPoint :=
  crispJ.J basePoint (fun resultPoint _resultPath => typeFamily basePoint → typeFamily resultPoint)
    (fun innerPoint => innerPoint) endPoint path point

/-- ★ **Transport along `refl` is the identity** — PROVED via the crisp-J β-rule.  The real consequence of path
induction (the unit law of transport), exercising the β-coherence. -/
theorem CrispJ.transport_refl (crispJ : CrispJ) {A : Type} (typeFamily : A → Type)
    (basePoint : A) (point : typeFamily basePoint) :
    crispJ.transport typeFamily (crispJ.refl basePoint) point = point := by
  dsimp only [CrispJ.transport]
  rw [crispJ.beta]

/-! ## The mode-indexed modal eliminator (indexed by the `mode-1` 1-cells)

The `ModalEliminator` above is modality-AGNOSTIC (one `ModalType : Type → Type`).  A genuine multimodal eliminator
is INDEXED by the mode theory's 1-cells — `mode-1`'s `ModalityPath` — with a modal type former `⟨μ | -⟩` PER
modality `μ`, functorial in 1-cell composition (`⟨μ ∘ ν | A⟩` nests as `⟨ν | ⟨μ | A⟩⟩`), the identity 1-cell
acting transparently, and a 2-cell SUBSUMPTION action.  This section ships exactly that, with the subsumption
along `mode-1`'s LOCALLY-DISCRETE 2-cells (which ARE 1-cell equalities, `locallyDiscreteTwoCategory`); the
GENUINE (non-discrete) 2-cell subsumption over `mode-3`'s free 2-cells stays deferred. -/

/-- A **mode-indexed modal eliminator** over a `ModeGraph` — a modal type former `⟨μ | -⟩` INDEXED by a 1-cell
`μ : ModalityPath` of the mode theory, with intro / dependent elim / β-coherence at every modality, FUNCTORIAL in
1-cell composition (the composite-modality law) and transparent at the identity 1-cell. -/
structure ModeIndexedModalEliminator (graph : ModeGraph) where
  /-- The modal type former, INDEXED by a 1-cell (modality path) of the mode theory. -/
  ModalType : {sourceMode targetMode : graph.Mode} →
    ModalityPath graph sourceMode targetMode → Type → Type
  /-- Introduction at a modality. -/
  intro : {sourceMode targetMode : graph.Mode} → {modality : ModalityPath graph sourceMode targetMode} →
    {A : Type} → A → ModalType modality A
  /-- Dependent elimination at a modality. -/
  elim : {sourceMode targetMode : graph.Mode} → {modality : ModalityPath graph sourceMode targetMode} →
    {A : Type} → (motive : ModalType modality A → Type) →
    (method : (value : A) → motive (intro value)) → (modalValue : ModalType modality A) → motive modalValue
  /-- The β-coherence at every modality. -/
  beta : {sourceMode targetMode : graph.Mode} → {modality : ModalityPath graph sourceMode targetMode} →
    {A : Type} → (motive : ModalType modality A → Type) →
    (method : (value : A) → motive (intro value)) → (value : A) →
    elim motive method (intro value) = method value
  /-- FUNCTORIALITY in 1-cell composition: the modal type of a composite 1-cell NESTS — the MTT
      `⟨μ ∘ ν | A⟩ = ⟨ν | ⟨μ | A⟩⟩` modal-type law. -/
  composeLaw : {sourceMode middleMode targetMode : graph.Mode} →
    (firstModality : ModalityPath graph sourceMode middleMode) →
    (secondModality : ModalityPath graph middleMode targetMode) → (A : Type) →
    ModalType (composePath firstModality secondModality) A
      = ModalType secondModality (ModalType firstModality A)
  /-- The identity 1-cell acts transparently: `⟨id | A⟩ = A`. -/
  identityLaw : {mode : graph.Mode} → (A : Type) → ModalType (identityPath mode) A = A

/-- The **identity mode-indexed eliminator** — every modality acts as the identity type former (the discrete
mode theory's eliminator).  All laws — β, the composite-modality nesting, the identity transparency — hold by
`rfl`.  The concrete witness that the mode-indexed coherence is satisfiable. -/
def identityModeIndexedModalEliminator (graph : ModeGraph) : ModeIndexedModalEliminator graph where
  ModalType := fun _modality carrier => carrier
  intro := fun value => value
  elim := fun _motive method modalValue => method modalValue
  beta := fun _motive _method _value => rfl
  composeLaw := fun _firstModality _secondModality _A => rfl
  identityLaw := fun _A => rfl

/-- **Functoriality of each modal type former** — a map `A → B` lifts to `⟨μ | A⟩ → ⟨μ | B⟩` at every modality
`μ`, via the per-modality eliminator.  The mode-indexed twin of `ModalEliminator.mapModal`. -/
def ModeIndexedModalEliminator.mapModal {graph : ModeGraph} (eliminator : ModeIndexedModalEliminator graph)
    {sourceMode targetMode : graph.Mode} (modality : ModalityPath graph sourceMode targetMode)
    {A B : Type} (mapFunction : A → B) : eliminator.ModalType modality A → eliminator.ModalType modality B :=
  eliminator.elim (fun _ => eliminator.ModalType modality B)
    (fun value => eliminator.intro (mapFunction value))

/-- ★ The per-modality functorial lift's COMPUTATION rule — `mapModal μ f (intro a) = intro (f a)` — PROVED via
the β-coherence at `μ` (a genuine use of the mode-indexed eliminator's computation). -/
theorem ModeIndexedModalEliminator.mapModal_intro {graph : ModeGraph}
    (eliminator : ModeIndexedModalEliminator graph) {sourceMode targetMode : graph.Mode}
    (modality : ModalityPath graph sourceMode targetMode) {A B : Type} (mapFunction : A → B) (value : A) :
    eliminator.mapModal modality mapFunction (eliminator.intro value)
      = eliminator.intro (mapFunction value) :=
  eliminator.beta (fun _ => eliminator.ModalType modality B)
    (fun innerValue => eliminator.intro (mapFunction innerValue)) value

/-- ★ The **2-cell subsumption action along a locally-discrete 2-cell** — a `mode-1` locally-discrete 2-cell
`μ ⇒ ν` IS an equality `μ = ν` (`locallyDiscreteTwoCategory`), and it induces `⟨μ | A⟩ → ⟨ν | A⟩` by transport
(`Eq.rec` with the explicit `ModalType · A` motive — the cast goes through a type-level function).  This is the
subsumption for the discrete 2-cell fragment; the genuine free-2-cell subsumption is deferred. -/
def ModeIndexedModalEliminator.subsumeEq {graph : ModeGraph} (eliminator : ModeIndexedModalEliminator graph)
    {sourceMode targetMode : graph.Mode}
    {firstModality secondModality : ModalityPath graph sourceMode targetMode}
    (twoCellEq : firstModality = secondModality) {A : Type}
    (modalValue : eliminator.ModalType firstModality A) : eliminator.ModalType secondModality A :=
  Eq.rec (motive := fun (otherModality : ModalityPath graph sourceMode targetMode) _ =>
    eliminator.ModalType otherModality A) modalValue twoCellEq

/-- The identity 2-cell (`rfl : μ = μ`) subsumes trivially — `subsumeEq` on `rfl` is the identity (the unit
coherence of the subsumption action). -/
theorem ModeIndexedModalEliminator.subsumeEq_rfl {graph : ModeGraph}
    (eliminator : ModeIndexedModalEliminator graph) {sourceMode targetMode : graph.Mode}
    {modality : ModalityPath graph sourceMode targetMode} {A : Type}
    (modalValue : eliminator.ModalType modality A) :
    eliminator.subsumeEq (rfl : modality = modality) modalValue = modalValue := rfl

/-- The mode tie: the identity eliminator's modal type former is the identity at EVERY modality — every 1-cell
of the discrete mode theory acts transparently on types. -/
theorem identityModeIndexedModalEliminator_modalType {graph : ModeGraph}
    {sourceMode targetMode : graph.Mode} (modality : ModalityPath graph sourceMode targetMode) (A : Type) :
    (identityModeIndexedModalEliminator graph).ModalType modality A = A := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The MODE-INDEXED modal eliminator IS now shipped: `ModeIndexedModalEliminator` —
modal types indexed by `mode-1`'s `ModalityPath` 1-cells, with per-modality intro / elim / β, FUNCTORIAL in
1-cell composition (`composeLaw`), transparent at the identity (`identityLaw`), and a 2-cell subsumption action
along the LOCALLY-DISCRETE 2-cells (`subsumeEq`, since `mode-1`'s 2-cells ARE 1-cell equalities) + the identity
witness.  What remains deferred is the subsumption over `mode-3`'s GENUINE (non-discrete) free 2-cells, with its
naturality coherence.  `= false`. -/
def fxMode_hasModeIndexedModalEliminator : Bool := false

/-- **Honesty marker.**  The connection of these abstract eliminators to the kernel's modal SYNTAX
(`gen_modIntro` / `gen_modElim` / `gen_subsume`) fibred over the mode theory is cross-axis (`fib`), deferred.
`= false`. -/
def fxMode_hasKernelModalSyntaxConnection : Bool := false

/-- **Honesty marker.**  Crisp-J in a genuine FLAT / ♭ cohesive context (Shulman real-cohesive HoTT — crisp
variables, the flat-context J), beyond the abstract J principle modeled here, is deferred.  `= false`. -/
def fxMode_hasRealCohesiveCrispJ : Bool := false

end FX1Poly.Axis
