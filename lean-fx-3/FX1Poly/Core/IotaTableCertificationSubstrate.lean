import FX1Poly.Core.CertifiedTermSpineProjections
import FX1Poly.Core.IotaRuleTable
import FX1Poly.Core.GeneratorChildSpecsDim0
import FX1Poly.Core.SubstPreservationMutual
import FX1Poly.Core.HasCertifiedIntros
import FX1Poly.Core.RawTermSubstPair

/-! # FX1Poly/Core/IotaTableCertificationSubstrate — IOTA-T3 bricks

The bricks for the generic structural subject reduction over the
iota-rule table (one template induction replacing the seventeen
bespoke `preservedByIota*` arms).  Three primitive families, exactly
as the table discipline prescribes:

  * **Spine projection certifies** — the bespoke arms project with
    concrete `headAtDim0`/`tail` chains; the generic theorem needs
    SLOT-INDEXED projections stated against the interpreter's own
    lookups (`scopedChildAt?` + `atShiftZero?/One?/Two?`).  Each
    projection walks the certified spine by position and surfaces the
    matched `ChildSpec` together with its lookup equation — the
    metadata seam the IOTA-T3 sort-coherence certificate keys on.
  * **Re-assembly certifies** — `PolyCell.gen` is the constructor;
    `PolyCell.invertGenAtDim0` here is its INVERSE (sort-universal,
    per the dependent-elimination discipline: the sort must be a free
    variable for `cases` to unify).
  * **Substitution certifies** — `preservedBySubst0` ships; this file
    adds the TWO-variable sibling (`pairSubstDim0Cells` +
    `preservedBySubstPair`) self-contained, so the generic stack never
    depends on the bespoke SR files slated for the IOTA-T11
    retirement.

## Zero-axiom verification

Structural walks over the spine inductive, the `headAtDim0`
boundary-collapse recipe (generalize the dim, `subst`, `Subsingleton
Unit`), direct `⟨0, _⟩` / `⟨k + 1, h⟩` Fin matching, and the shipped
generic substitution engine.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditIotaTableCertification.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## The dim-0 boundary collapse, factored -/

/-- Collapse any cell of (provably) dimension 0 to the canonical
trivial boundary — the tail of `headAtDim0`, factored so the
slot-indexed projections below can reuse it at every position. -/
def PolyCell.atDim0 {profile : PolyProfile} {sort : CellSort}
    {dim scope : Nat} {boundary : CellBoundary profile sort dim scope}
    {rawCell : RawCell scope}
    (hDim : dim = 0)
    (cell : PolyCell profile sort dim scope boundary rawCell) :
    PolyCell profile sort 0 scope CellBoundary.trivial rawCell := by
  subst hDim
  haveI : Subsingleton (CellBoundary profile sort 0 scope) :=
    inferInstanceAs (Subsingleton Unit)
  have boundaryIsTrivial : boundary = CellBoundary.trivial :=
    Subsingleton.elim boundary CellBoundary.trivial
  exact boundaryIsTrivial ▸ cell

/-! ## Per-shift head extraction (the standalone Nat split)

Splitting the head spec's `scopeShift` INSIDE the spine match leaks
`propext` through the matcher's index-unification equation lemmas (the
cons-index-match trap).  The split therefore lives in standalone
helpers over a PLAIN Nat: the per-shift projection either transports
the head cell (shift agrees) or refutes the lookup equation (shift
disagrees). -/

/-- Head extraction at shift 0: the projection equation forces the
shift to be 0 and pins the projected term to the head raw. -/
def ScopedChild.certifiedOfAtShiftZero {profile : PolyProfile}
    {parentScope : Nat} {sort : CellSort} :
    (shift : Nat) → {headRaw : RawTerm (parentScope + shift)} →
    (headCell :
      PolyCell profile sort 0 (parentScope + shift)
        CellBoundary.trivial (.termBase headRaw)) →
    {childTerm : RawTerm parentScope} →
    (ScopedChild.atShiftZero? ⟨shift, headRaw⟩ = some childTerm) →
    PolyCell profile sort 0 parentScope CellBoundary.trivial
      (.termBase childTerm)
  | 0, _, headCell, _, projEq => Option.some.inj projEq ▸ headCell
  | _ + 1, _, _, _, projEq => by injection projEq

/-- Head extraction at shift 1. -/
def ScopedChild.certifiedOfAtShiftOne {profile : PolyProfile}
    {parentScope : Nat} {sort : CellSort} :
    (shift : Nat) → {headRaw : RawTerm (parentScope + shift)} →
    (headCell :
      PolyCell profile sort 0 (parentScope + shift)
        CellBoundary.trivial (.termBase headRaw)) →
    {childBody : RawTerm (parentScope + 1)} →
    (ScopedChild.atShiftOne? ⟨shift, headRaw⟩ = some childBody) →
    PolyCell profile sort 0 (parentScope + 1) CellBoundary.trivial
      (.termBase childBody)
  | 0, _, _, _, projEq => by injection projEq
  | 1, _, headCell, _, projEq => Option.some.inj projEq ▸ headCell
  | _ + 2, _, _, _, projEq => by injection projEq

/-- Head extraction at shift 2. -/
def ScopedChild.certifiedOfAtShiftTwo {profile : PolyProfile}
    {parentScope : Nat} {sort : CellSort} :
    (shift : Nat) → {headRaw : RawTerm (parentScope + shift)} →
    (headCell :
      PolyCell profile sort 0 (parentScope + shift)
        CellBoundary.trivial (.termBase headRaw)) →
    {childBody : RawTerm (parentScope + 2)} →
    (ScopedChild.atShiftTwo? ⟨shift, headRaw⟩ = some childBody) →
    PolyCell profile sort 0 (parentScope + 2) CellBoundary.trivial
      (.termBase childBody)
  | 0, _, _, _, projEq => by injection projEq
  | 1, _, _, _, projEq => by injection projEq
  | 2, _, headCell, _, projEq => Option.some.inj projEq ▸ headCell
  | _ + 3, _, _, _, projEq => by injection projEq

/-! ## Slot-indexed certified projections

Each projection takes the interpreter's OWN lookup equation
(`scopedChildAt?` on the shift-erased view, then the per-shift
projection) and returns the matched spec, its positional lookup
equation, and the child's certified cell collapsed to dimension 0.
The all-specs-dim-0 hypothesis is discharged at every call site by the
generator-table flatness pin `Generator.childSpecs_cellDimension_zero`.

Indices stay in BINDER FORM (matched `_`); only the spine constructor
and the slot Nat split — the propext-clean indexed-match discipline. -/

/-- Certified projection at binder shift 0: whatever parent-scope term
the interpreter's slot lookup produced, the certified spine holds its
cell. -/
def CertifiedTermSpine.certifiedAtShiftZero {profile : PolyProfile}
    {parentScope : Nat} :
    {childSpecs : List ChildSpec} → {binderShifts : List Nat} →
    {children : RawTermChildren binderShifts parentScope} →
    (spine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    (allSpecsAreDim0 : ∀ spec ∈ childSpecs, spec.cellDimension = 0) →
    (slot : Nat) → {childTerm : RawTerm parentScope} →
    ((scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftZero? = some childTerm) →
    Σ' childSpec : ChildSpec,
      (listEntryAt? childSpecs slot = some childSpec) ×'
      PolyCell profile childSpec.cellSort 0 parentScope
        CellBoundary.trivial (.termBase childTerm)
  | _, _, _, .nil, _, _, _, projEq => by injection projEq
  | _, _, _, .cons headCell _, allSpecsAreDim0, 0, _, projEq =>
      ⟨_, rfl,
        ScopedChild.certifiedOfAtShiftZero _
          (PolyCell.atDim0 (allSpecsAreDim0 _ (.head _)) headCell)
          projEq⟩
  | _, _, _, .cons _ restSpine, allSpecsAreDim0, slot + 1, _, projEq =>
      restSpine.certifiedAtShiftZero
        (fun spec specIsMember =>
          allSpecsAreDim0 spec (.tail _ specIsMember))
        slot projEq

/-- Certified projection at binder shift 1: the one-binder body the
interpreter's lookup produced has its cell at `parentScope + 1`. -/
def CertifiedTermSpine.certifiedAtShiftOne {profile : PolyProfile}
    {parentScope : Nat} :
    {childSpecs : List ChildSpec} → {binderShifts : List Nat} →
    {children : RawTermChildren binderShifts parentScope} →
    (spine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    (allSpecsAreDim0 : ∀ spec ∈ childSpecs, spec.cellDimension = 0) →
    (slot : Nat) → {childBody : RawTerm (parentScope + 1)} →
    ((scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftOne? = some childBody) →
    Σ' childSpec : ChildSpec,
      (listEntryAt? childSpecs slot = some childSpec) ×'
      PolyCell profile childSpec.cellSort 0 (parentScope + 1)
        CellBoundary.trivial (.termBase childBody)
  | _, _, _, .nil, _, _, _, projEq => by injection projEq
  | _, _, _, .cons headCell _, allSpecsAreDim0, 0, _, projEq =>
      ⟨_, rfl,
        ScopedChild.certifiedOfAtShiftOne _
          (PolyCell.atDim0 (allSpecsAreDim0 _ (.head _)) headCell)
          projEq⟩
  | _, _, _, .cons _ restSpine, allSpecsAreDim0, slot + 1, _, projEq =>
      restSpine.certifiedAtShiftOne
        (fun spec specIsMember =>
          allSpecsAreDim0 spec (.tail _ specIsMember))
        slot projEq

/-- Certified projection at binder shift 2: the two-binder body the
interpreter's lookup produced has its cell at `parentScope + 2`. -/
def CertifiedTermSpine.certifiedAtShiftTwo {profile : PolyProfile}
    {parentScope : Nat} :
    {childSpecs : List ChildSpec} → {binderShifts : List Nat} →
    {children : RawTermChildren binderShifts parentScope} →
    (spine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    (allSpecsAreDim0 : ∀ spec ∈ childSpecs, spec.cellDimension = 0) →
    (slot : Nat) → {childBody : RawTerm (parentScope + 2)} →
    ((scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftTwo? = some childBody) →
    Σ' childSpec : ChildSpec,
      (listEntryAt? childSpecs slot = some childSpec) ×'
      PolyCell profile childSpec.cellSort 0 (parentScope + 2)
        CellBoundary.trivial (.termBase childBody)
  | _, _, _, .nil, _, _, _, projEq => by injection projEq
  | _, _, _, .cons headCell _, allSpecsAreDim0, 0, _, projEq =>
      ⟨_, rfl,
        ScopedChild.certifiedOfAtShiftTwo _
          (PolyCell.atDim0 (allSpecsAreDim0 _ (.head _)) headCell)
          projEq⟩
  | _, _, _, .cons _ restSpine, allSpecsAreDim0, slot + 1, _, projEq =>
      restSpine.certifiedAtShiftTwo
        (fun spec specIsMember =>
          allSpecsAreDim0 spec (.tail _ specIsMember))
        slot projEq

/-! ## Cell inversion at a generator head -/

/-- Invert a certified dim-0 term-former cell to its certified child
spine.  The sort is taken as an EXPLICIT universal — dependent
elimination on a sort-pinned cell fails (the natElimSucc lesson), so
callers instantiate the sort AFTER the cases split. -/
def PolyCell.invertGenAtDim0 {profile : PolyProfile} {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} :
    (cellSort : CellSort) →
    PolyCell profile cellSort 0 scope CellBoundary.trivial
      (.termBase (.mkGen generator payload children)) →
    CertifiedTermSpine profile generator.childSpecs scope
      generator.binderShifts children
  | _, .gen _ _ childSpine => childSpine

/-! ## Two-variable substitution certifies -/

/-- Certify every output of the two-entry pair substitution: position
0 maps to the inner substituent, positions `k + 1` route through the
singleton's entries (the outer substituent at 0, fresh variables
above).  Self-contained mirror of the natElim succ-arm's cons-cells —
deliberately NOT importing the bespoke SR file that ships it (that
file retires at IOTA-T11). -/
def PolyCell.pairSubstDim0Cells {profile : PolyProfile} {scope : Nat}
    (innerArg outerArg : RawTerm scope)
    (innerCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase innerArg))
    (outerCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase outerArg)) :
    ∀ variableIndex : Fin (scope + 2),
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          (RawTermSubst.pair innerArg outerArg variableIndex)) := by
  intro variableIndex
  match variableIndex with
  | ⟨0, _⟩ =>
      show PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase innerArg)
      exact innerCell
  | ⟨priorIndexValue + 1, indexBound⟩ =>
      show PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          (RawTermSubst.singleton outerArg
            (⟨priorIndexValue, Nat.lt_of_succ_lt_succ indexBound⟩ :
              Fin (scope + 1))))
      exact PolyCell.singletonSubstDim0Cells outerArg outerCell
        (⟨priorIndexValue, Nat.lt_of_succ_lt_succ indexBound⟩ :
          Fin (scope + 1))

/-- Two-variable substitution stability: a certified two-binder body
substituted with two certified arguments stays certified — the
`substPair` sibling of `preservedBySubst0`, routed through the generic
engine. -/
theorem HasCertifiedCellDim0.preservedBySubstPair
    {profile : PolyProfile} {scope : Nat}
    {body : RawTerm (scope + 2)} {innerArg outerArg : RawTerm scope}
    (bodyCert : HasCertifiedCellDim0 (profile := profile) body)
    (innerCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase innerArg))
    (outerCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase outerArg)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.substPair body innerArg outerArg) :=
  HasCertifiedCellDim0.preservedBySubst
    (RawTermSubst.pair innerArg outerArg)
    (PolyCell.pairSubstDim0Cells innerArg outerArg innerCell outerCell)
    bodyCert

/-! ## Sort-precise cell builders for the interpreter's primitives

The master template induction is SORT-PRECISE (a built spine's `cons`
demands each head cell AT its spec's sort), so each interpreter
primitive gets a sort-preserving cell builder: `HasCertifiedCellDim0`'s
sort-existential wrappers do not compose. -/

/-- The variable cell, sort-precise (`gen_var`'s table sort is
`.term`). -/
def PolyCell.varCell {profile : PolyProfile} {scope : Nat}
    (varIndex : Fin scope) :
    PolyCell profile .term 0 scope CellBoundary.trivial
      (.termBase (.mkGen .gen_var varIndex .childNil)) :=
  PolyCell.gen SupportedGenerator.gen_var
    (genPayloadEvidence (generator := .gen_var) (scope := scope) varIndex)
    CertifiedTermSpine.nil

/-- `subst0` certifies, sort-precise: the body keeps its sort, the
substituent enters at `.term`. -/
def PolyCell.subst0_dim0 {profile : PolyProfile} {scope : Nat}
    {sort : CellSort} {body : RawTerm (scope + 1)} {rawArg : RawTerm scope}
    (bodyCell :
      PolyCell profile sort 0 (scope + 1) CellBoundary.trivial
        (.termBase body))
    (argCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase rawArg)) :
    PolyCell profile sort 0 scope CellBoundary.trivial
      (.termBase (RawTerm.subst0 body rawArg)) :=
  PolyCell.subst_dim0 (RawTermSubst.singleton rawArg)
    (PolyCell.singletonSubstDim0Cells rawArg argCell) bodyCell

/-- `substPair` certifies, sort-precise. -/
def PolyCell.substPair_dim0 {profile : PolyProfile} {scope : Nat}
    {sort : CellSort} {body : RawTerm (scope + 2)}
    {innerArg outerArg : RawTerm scope}
    (bodyCell :
      PolyCell profile sort 0 (scope + 2) CellBoundary.trivial
        (.termBase body))
    (innerCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase innerArg))
    (outerCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase outerArg)) :
    PolyCell profile sort 0 scope CellBoundary.trivial
      (.termBase (RawTerm.substPair body innerArg outerArg)) :=
  PolyCell.subst_dim0 (RawTermSubst.pair innerArg outerArg)
    (PolyCell.pairSubstDim0Cells innerArg outerArg innerCell outerCell)
    bodyCell

/-- Depth weakening certifies (iterated `rename_dim0` at the weakening
renaming — `RawTerm.weaken` IS that rename, definitionally). -/
def PolyCell.weakenBy_dim0 {profile : PolyProfile} {scope : Nat}
    {sort : CellSort} :
    (depth : Nat) → {term : RawTerm scope} →
    PolyCell profile sort 0 scope CellBoundary.trivial (.termBase term) →
    PolyCell profile sort 0 (scope + depth) CellBoundary.trivial
      (.termBase (RawTerm.weakenBy depth term))
  | 0, _, cell => cell
  | innerDepth + 1, _, cell =>
      PolyCell.rename_dim0 RawRenaming.weaken
        (PolyCell.weakenBy_dim0 innerDepth cell)

/-- One-binder-body depth weakening certifies (the weakening renaming
lifted under the body's own binder). -/
def PolyCell.weakenBodyUnderOneBinderBy_dim0 {profile : PolyProfile}
    {scope : Nat} {sort : CellSort} :
    (depth : Nat) → {body : RawTerm (scope + 1)} →
    PolyCell profile sort 0 (scope + 1) CellBoundary.trivial
      (.termBase body) →
    PolyCell profile sort 0 (scope + depth + 1) CellBoundary.trivial
      (.termBase (RawTerm.weakenBodyUnderOneBinderBy depth body))
  | 0, _, cell => cell
  | innerDepth + 1, _, cell =>
      PolyCell.rename_dim0 (RawRenaming.lift RawRenaming.weaken)
        (PolyCell.weakenBodyUnderOneBinderBy_dim0 innerDepth cell)

/-- Two-binder-body depth weakening certifies. -/
def PolyCell.weakenBodyUnderTwoBindersBy_dim0 {profile : PolyProfile}
    {scope : Nat} {sort : CellSort} :
    (depth : Nat) → {body : RawTerm (scope + 2)} →
    PolyCell profile sort 0 (scope + 2) CellBoundary.trivial
      (.termBase body) →
    PolyCell profile sort 0 (scope + depth + 2) CellBoundary.trivial
      (.termBase (RawTerm.weakenBodyUnderTwoBindersBy depth body))
  | 0, _, cell => cell
  | innerDepth + 1, _, cell =>
      PolyCell.rename_dim0
        (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (PolyCell.weakenBodyUnderTwoBindersBy_dim0 innerDepth cell)

/-- Whole-spine depth weakening certifies (iterated spine-level
rename). -/
def CertifiedTermSpine.certifiedWeakenSpineBy {profile : PolyProfile}
    {parentScope : Nat} {childSpecs : List ChildSpec}
    {binderShifts : List Nat}
    {children : RawTermChildren binderShifts parentScope}
    (allSpecsAreDim0 : ∀ spec ∈ childSpecs, spec.cellDimension = 0) :
    (depth : Nat) →
    CertifiedTermSpine profile childSpecs parentScope binderShifts
      children →
    CertifiedTermSpine profile childSpecs (parentScope + depth)
      binderShifts (RawTermChildren.weakenSpineBy depth children)
  | 0, spine => spine
  | innerDepth + 1, spine =>
      CertifiedTermSpine.rename_dim0 RawRenaming.weaken allSpecsAreDim0
        (CertifiedTermSpine.certifiedWeakenSpineBy allSpecsAreDim0
          innerDepth spine)

/-! ## Slot replacement certifies -/

/-- View a dim-0 trivial-boundary cell at a provably-0 dimension —
the inverse of `atDim0`, packaging the (unique) boundary for
`CertifiedTermSpine.cons`. -/
def PolyCell.ofDim0 {profile : PolyProfile} {sort : CellSort}
    {scope : Nat} {rawCell : RawCell scope} :
    (dim : Nat) → (hDim : dim = 0) →
    PolyCell profile sort 0 scope CellBoundary.trivial rawCell →
    Σ' boundary : CellBoundary profile sort dim scope,
      PolyCell profile sort dim scope boundary rawCell
  | _, rfl, cell => ⟨CellBoundary.trivial, cell⟩

/-- Replacement-at-shift transport (standalone Nat split — the
projection equation forces the slot's shift to be 0). -/
def replacementIntoShiftCertified {profile : PolyProfile}
    {parentScope : Nat} {sort : CellSort} :
    (shift : Nat) → {replacement : RawTerm parentScope} →
    (replacementCell :
      PolyCell profile sort 0 parentScope CellBoundary.trivial
        (.termBase replacement)) →
    {shiftedReplacement : RawTerm (parentScope + shift)} →
    (replacementIntoShift? shift replacement = some shiftedReplacement) →
    PolyCell profile sort 0 (parentScope + shift) CellBoundary.trivial
      (.termBase shiftedReplacement)
  | 0, _, replacementCell, _, shiftEq =>
      Option.some.inj shiftEq ▸ replacementCell
  | _ + 1, _, _, _, shiftEq => by injection shiftEq

/-- Slot replacement certifies: replacing a (necessarily shift-0) slot
with a cell at THAT slot's spec sort keeps the spine certified. -/
def CertifiedTermSpine.certifiedReplaceChildAt {profile : PolyProfile}
    {parentScope : Nat} :
    {childSpecs : List ChildSpec} → {binderShifts : List Nat} →
    {children : RawTermChildren binderShifts parentScope} →
    (spine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    (allSpecsAreDim0 : ∀ spec ∈ childSpecs, spec.cellDimension = 0) →
    (slot : Nat) → {replacement : RawTerm parentScope} →
    {slotSpec : ChildSpec} →
    (listEntryAt? childSpecs slot = some slotSpec) →
    (replacementCell :
      PolyCell profile slotSpec.cellSort 0 parentScope
        CellBoundary.trivial (.termBase replacement)) →
    {replacedChildren : RawTermChildren binderShifts parentScope} →
    (children.replaceChildAt? slot replacement = some replacedChildren) →
    CertifiedTermSpine profile childSpecs parentScope binderShifts
      replacedChildren
  | _, _, _, .nil, _, _, _, _, _, _, _, replaceEq => by injection replaceEq
  | _, _, _, @CertifiedTermSpine.cons _ _ headSpec _ _ _ childTail _
      headCell restSpine, allSpecsAreDim0, 0, replacement, slotSpec,
      specLookupEq, replacementCell, replacedChildren, replaceEq => by
      have specEq : headSpec = slotSpec := Option.some.inj specLookupEq
      have replaceEqMapped :
          (replacementIntoShift? headSpec.scopeShift replacement).map
              (RawTermChildren.childCons · childTail)
            = some replacedChildren := replaceEq
      match shiftedEq :
          replacementIntoShift? headSpec.scopeShift replacement with
      | none =>
          rw [shiftedEq] at replaceEqMapped
          injection replaceEqMapped
      | some shiftedReplacement =>
          rw [shiftedEq] at replaceEqMapped
          obtain rfl := Option.some.inj replaceEqMapped
          obtain ⟨headBoundary, headCellAtDim⟩ :=
            PolyCell.ofDim0 _ (allSpecsAreDim0 _ (.head _))
              (replacementIntoShiftCertified headSpec.scopeShift
                (specEq.symm ▸ replacementCell) shiftedEq)
          exact CertifiedTermSpine.cons headCellAtDim restSpine
  | _, _, _, @CertifiedTermSpine.cons _ _ _ _ _ headRaw childTail _
      headCell restSpine, allSpecsAreDim0, slot + 1,
      replacement, _, specLookupEq, replacementCell, replacedChildren,
      replaceEq => by
      have replaceEqMapped :
          (childTail.replaceChildAt? slot replacement).map
              (RawTermChildren.childCons headRaw ·)
            = some replacedChildren := replaceEq
      match restEq :
          RawTermChildren.replaceChildAt? childTail slot replacement with
      | none =>
          rw [restEq] at replaceEqMapped
          injection replaceEqMapped
      | some replacedTail =>
          rw [restEq] at replaceEqMapped
          obtain rfl := Option.some.inj replaceEqMapped
          exact CertifiedTermSpine.cons headCell
            (restSpine.certifiedReplaceChildAt
              (fun spec specIsMember =>
                allSpecsAreDim0 spec (.tail _ specIsMember))
              slot specLookupEq replacementCell restEq)

/-! ## The sort discipline — the IOTA-T3 row certificate

The genuinely CONDITIONAL ingredient of generic structural SR: a
template certifies only at the sort the generator table assigns to the
syntax it projects or builds (type-code generators are `.type`-sorted —
a row whose reduct stuffed a type code into a term slot would
interpret fine but NOT certify).  The walker mirrors the interpreter
arm-for-arm; every lookup it constrains is one the interpreter
performs, so on concrete rows the matches reduce and the 18 pins close
by `rfl`-shaped conjunction trees. -/

mutual

/-- The template certifies at `expectedSort`, given the row's pattern
fired (scrutinee heads pinned by their specs). -/
def ReductTemplate.CertifiesAtSort (rule : IotaRuleDesc) :
    ReductTemplate → CellSort → Prop
  | .boundVarAt _, expectedSort => expectedSort = .term
  | .spineChildAt slot, expectedSort =>
      match listEntryAt? rule.elimGenerator.childSpecs slot with
      | none => False
      | some childSpec => childSpec.cellSort = expectedSort
  | .scrutineeChildAt scrutineeIndex slot, expectedSort =>
      match rule.scrutineeSpecAt? scrutineeIndex with
      | none => False
      | some scrutineeSpec =>
          match listEntryAt? scrutineeSpec.head.childSpecs slot with
          | none => False
          | some childSpec => childSpec.cellSort = expectedSort
  | .theScrutineeAt scrutineeIndex, expectedSort =>
      match rule.scrutineeSpecAt? scrutineeIndex with
      | none => False
      | some scrutineeSpec =>
          match listEntryAt? rule.elimGenerator.childSpecs
              scrutineeSpec.slot with
          | none => False
          | some childSpec => childSpec.cellSort = expectedSort
  | .motiveInstantiatedWith argTemplate, expectedSort =>
      (match rule.motiveSlot? with
        | none => False
        | some motiveSlot =>
            match listEntryAt? rule.elimGenerator.childSpecs motiveSlot with
            | none => False
            | some motiveSpec => motiveSpec.cellSort = expectedSort) ∧
      argTemplate.CertifiesAtSort rule .term
  | .motiveInstantiatedWithPair innerTemplate outerTemplate, expectedSort =>
      (match rule.motiveSlot? with
        | none => False
        | some motiveSlot =>
            match listEntryAt? rule.elimGenerator.childSpecs motiveSlot with
            | none => False
            | some motiveSpec => motiveSpec.cellSort = expectedSort) ∧
      innerTemplate.CertifiesAtSort rule .term ∧
      outerTemplate.CertifiesAtSort rule .term
  | .builtGen builtHead _ childTemplates, expectedSort =>
      builtHead.cellSort = expectedSort ∧
      childTemplates.CertifyAgainstSpecs rule builtHead.childSpecs
  | .reassembledReplacing replacements, expectedSort =>
      rule.elimGenerator.cellSort = expectedSort ∧
      replacements.CertifyReplacementSorts rule
  | .substOneIntoSpineChild bodySlot argTemplate, expectedSort =>
      (match listEntryAt? rule.elimGenerator.childSpecs bodySlot with
        | none => False
        | some bodySpec => bodySpec.cellSort = expectedSort) ∧
      argTemplate.CertifiesAtSort rule .term
  | .substOneIntoScrutineeChild scrutineeIndex bodySlot argTemplate,
      expectedSort =>
      (match rule.scrutineeSpecAt? scrutineeIndex with
        | none => False
        | some scrutineeSpec =>
            match listEntryAt? scrutineeSpec.head.childSpecs bodySlot with
            | none => False
            | some bodySpec => bodySpec.cellSort = expectedSort) ∧
      argTemplate.CertifiesAtSort rule .term
  | .substPairIntoSpineChild bodySlot innerTemplate outerTemplate,
      expectedSort =>
      (match listEntryAt? rule.elimGenerator.childSpecs bodySlot with
        | none => False
        | some bodySpec => bodySpec.cellSort = expectedSort) ∧
      innerTemplate.CertifiesAtSort rule .term ∧
      outerTemplate.CertifiesAtSort rule .term
  | .substPairIntoScrutineeChild scrutineeIndex bodySlot innerTemplate
      outerTemplate, expectedSort =>
      (match rule.scrutineeSpecAt? scrutineeIndex with
        | none => False
        | some scrutineeSpec =>
            match listEntryAt? scrutineeSpec.head.childSpecs bodySlot with
            | none => False
            | some bodySpec => bodySpec.cellSort = expectedSort) ∧
      innerTemplate.CertifiesAtSort rule .term ∧
      outerTemplate.CertifiesAtSort rule .term

/-- Each built child template certifies at its spec's sort, in
lockstep with the built head's spec list. -/
def ReductTemplateSpine.CertifyAgainstSpecs (rule : IotaRuleDesc) :
    ReductTemplateSpine → List ChildSpec → Prop
  | .spineNil, [] => True
  | .spineNil, _ :: _ => False
  | .spineCons _ _, [] => False
  | .spineCons childTemplate restTemplates, childSpec :: restSpecs =>
      childTemplate.CertifiesAtSort rule childSpec.cellSort ∧
      restTemplates.CertifyAgainstSpecs rule restSpecs

/-- Each replacement certifies at its target slot's spec sort. -/
def SpineReplacements.CertifyReplacementSorts (rule : IotaRuleDesc) :
    SpineReplacements → Prop
  | .replaceNil => True
  | .replaceCons slot replacementTemplate restReplacements =>
      (match listEntryAt? rule.elimGenerator.childSpecs slot with
        | none => False
        | some slotSpec =>
            replacementTemplate.CertifiesAtSort rule slotSpec.cellSort) ∧
      restReplacements.CertifyReplacementSorts rule

end

/-- The row-level IOTA-T3 certificate: the reduct template certifies at
SOME sort.  The master redex theorem consumes the witness inside its
(Prop-valued) conclusion. -/
def IotaRuleDesc.HasSortCertifiedTarget (rule : IotaRuleDesc) : Prop :=
  ∃ targetSort, rule.target.CertifiesAtSort rule targetSort

end FX1Poly.Core
