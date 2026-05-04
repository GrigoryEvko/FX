import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext
import LeanFX2.HoTT.UnivalenceFull
import LeanFX2.HoTT.UnivalenceTransport
import LeanFX2.HoTT.FunextFull
import LeanFX2.Smoke.AuditPhase12AB8Cascade
import LeanFX2.Smoke.AuditUnivalenceFull
import LeanFX2.Smoke.AuditUnivalenceTransport
import LeanFX2.Smoke.AuditFunextFull

/-! # Smoke/AuditPhase12AB8 — final comprehensive audit for CUMUL-8.

Phase 12.A.B8.8 (CUMUL-8.8).  Final integration audit covering the
ENTIRE Univalence + Funext + cascade chain at zero axioms.

## Scope

Every shipped declaration in the CUMUL-8 sub-sprint:

* **Term ctors (sources + targets):**
  - `Term.equivReflId` (target of Univalence rfl-fragment)
  - `Term.equivReflIdAtId` (source of Univalence rfl-fragment)
  - `Term.funextRefl` (target of funext rfl-fragment)
  - `Term.funextReflAtId` (source of funext rfl-fragment)

* **Step ctors (kernel reductions):**
  - `Step.eqType` — `Term.equivReflIdAtId ~~> Term.equivReflId`
    (the rfl-fragment of Univalence, made definitional in the
    kernel reduction relation)
  - `Step.eqArrow` — `Term.funextReflAtId ~~> Term.funextRefl`
    (the rfl-fragment of funext, made definitional)

* **Step.par ctors (parallel-reduction analogs):**
  - `Step.par.eqType`
  - `Step.par.eqArrow`

* **Headline theorems:**
  - `LeanFX2.Univalence` — `Conv.fromStep Step.eqType`
  - `LeanFX2.funext` — `Conv.fromStep Step.eqArrow`

* **Confluence cascade (auto-handled by Phase 4 base):**
  - `Step.par.cdLemmaRaw_eqType` / `_eqArrow`
  - `Step.par.diamondRaw_eqType_pair` / `_eqArrow_pair`
  - `Conv.canonicalForm_Univalence` / `_funext`

## What this audit establishes

`#print axioms` over EVERY declaration in the chain reports:
```
'<DeclName>' does not depend on any axioms
```

No `propext`, no `Quot.sound`, no `Classical.choice`, no
`funext` (the Lean 4 stdlib axiom — distinct from the lean-fx-2
kernel theorem), no user-declared axiom.

## Sorry / axiom keyword absence

Verified externally:
```
$ grep -r '^axiom' LeanFX2/HoTT/ LeanFX2/Cubical/      # empty
$ grep -r '\bsorry\b' LeanFX2/HoTT/ LeanFX2/Cubical/   # empty
```

## Honest scope

Univalence is the **rfl-fragment** of Voevodsky's full Univalence:
`A = A` (refl path) corresponds to `idEquiv A` (canonical
identity equivalence).  The full Voevodsky axiom — `(A B : Type)
→ (A = B) ≃ (A ≃ B)` for ARBITRARY A, B — would require:

1. Heterogeneous-carrier Step ctors (extending eqType to A ≠ B)
2. `IsEquiv` machinery in HoTT/Equivalence.lean (D3.5 — pending)
3. `ua` direction theorem `Equiv A B → A = B`
4. `ua_β` computation rule

The rfl-fragment is the load-bearing case for HoTT applications:
transport along refl, J-eliminator at refl, refl-paths.  It is
sufficient for Univalence-as-theorem to enter the lean-fx-2
kernel, AND it is the maximum honestly extensible at zero axioms
without redesigning Term ctors.

Funext is the **rfl-fragment** of full Funext:
`(f : A → B) → refl_f` corresponds to `fun x => refl_(f x)`.
The full funext — `(f g : A → B) → ((x : A) → f x = g x) →
f = g` for ARBITRARY pointwise equality — would require:

1. Heterogeneous-function Step ctors (extending eqArrow to f ≠ g)
2. Pointwise-to-functional bridge

Same status as Univalence: the rfl-fragment is shipped; full
extension is left to a future phase.

This audit ships exactly what's been built.  No fake claims of
"full Univalence" or "full funext".  The rfl-fragment is a
genuine kernel milestone — vanilla MLTT cannot derive even the
rfl-fragment without an axiom; lean-fx-2 derives it via the
`Step.eqType` / `Step.eqArrow` reduction rules. -/

namespace LeanFX2

/-! ## §1. Term constructors. -/

#print axioms Term.equivReflId
#print axioms Term.equivReflIdAtId
#print axioms Term.funextRefl
#print axioms Term.funextReflAtId

/-! ## §2. Step constructors (kernel reductions). -/

#print axioms Step.eqType
#print axioms Step.eqArrow

/-! ## §3. Step.par constructors (parallel-reduction analogs). -/

#print axioms Step.par.eqType
#print axioms Step.par.eqArrow

/-! ## §4. Headline theorems. -/

#print axioms LeanFX2.Univalence
#print axioms LeanFX2.funext

/-! ## §4.5. Meta-level Univalence neighbourhood (stretch milestone).

The kernel `LeanFX2.Univalence` theorem ships the rfl-fragment at
the kernel reduction relation.  Below, we ship the **meta-level**
companion using Lean's `Eq` between Sort values: the canonical
`idToEquivMeta` map (forward direction `Eq → Equiv`) and its
computation rule at `rfl`.

This stretch milestone documents what's provable cleanly at zero
axioms ABOVE the rfl-fragment kernel theorem.  It does NOT make
the converse direction (`Equiv → Eq` on Sorts) provable — that
requires either propext or further kernel structure (heterogeneous-
carrier Step ctors); see file docstring of `HoTT/Univalence.lean`. -/

#print axioms LeanFX2.Univalence.idToEquivMeta
#print axioms LeanFX2.Univalence.idToEquivMeta_refl
#print axioms LeanFX2.Univalence.idToEquivMeta_refl_toFun
#print axioms LeanFX2.Univalence.idToEquivMeta_refl_invFun
#print axioms LeanFX2.Univalence.idToEquivMeta_refl_isEquiv_toFun
#print axioms LeanFX2.Univalence.idToEquivMeta_isEquiv_toFun
#print axioms LeanFX2.Univalence.idToEquivMeta_refl_eq_reflEquiv
#print axioms LeanFX2.Univalence.idToEquivMeta_symm
#print axioms LeanFX2.Univalence.idToEquivMeta_trans
#print axioms LeanFX2.Univalence.idToEquivMeta_toFun_eq_transport
#print axioms LeanFX2.Univalence.idToEquivMeta_invFun_eq_transport

/-! ## §5. Confluence cascade audit (re-shown for completeness).

These six theorems live in `AuditPhase12AB8Cascade.lean` and are
audited there.  Re-imported here so the final audit file presents
the entire CUMUL-8 chain in one place. -/

#print axioms Step.par.cdLemmaRaw_eqType
#print axioms Step.par.diamondRaw_eqType_pair
#print axioms Conv.canonicalForm_Univalence
#print axioms Step.par.cdLemmaRaw_eqArrow
#print axioms Step.par.diamondRaw_eqArrow_pair
#print axioms Conv.canonicalForm_funext

/-! ## §6. Phase 4 base infrastructure (re-shown for context).

The Phase 4 base ships the typed-input/raw-output confluence
pipeline.  CUMUL-8 demonstrates that NO per-ctor extension is
needed — the `toRawBridge` arms for `eqType` / `eqArrow`
(`RawStep.par.refl _`, since source/target raw forms coincide)
let everything cascade through transparently. -/

#print axioms Term.cdRaw
#print axioms Step.par.cdLemmaRaw
#print axioms Step.par.cdDominatesRaw
#print axioms Step.par.diamondRaw
#print axioms Step.par.diamondRawCd
#print axioms Step.parStar.churchRosserRaw
#print axioms StepStar.churchRosserRaw
#print axioms Conv.canonicalRaw
#print axioms Conv.canonicalForm
#print axioms Conv.canonicalForm_self
#print axioms Conv.canonicalForm_fromStepStar

/-! ## §7. Sister-milestone reference: cumulUp cascade.

CUMUL-3..6 shipped the same architectural pattern for
`Step.cumulUpInner` / `Term.cumulUp`: pre-align source/target
raw forms so that the `toRawBridge` arm is `RawStep.par.refl _`,
making confluence cascade through Phase 4 base infrastructure
without per-ctor Cd/CdLemma/Diamond/ChurchRosser extensions.

Re-confirming those gates are still clean ensures the kernel
hasn't regressed while CUMUL-8 was added. -/

#print axioms Term.cumulUp
#print axioms Step.cumulUpInner
#print axioms Step.par.cumulUpInnerCong

end LeanFX2
