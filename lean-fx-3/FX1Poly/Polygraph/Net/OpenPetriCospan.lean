import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision
import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem

/-! # Open Petri nets as cospans — boundary-glued composition + canonical decision

An **open Petri net** is a Petri net equipped with two ordered boundary legs — a
cospan `leftBoundary → net ← rightBoundary` of finite place-sets (Baez–Master
"Open Petri nets").  Composition glues the right boundary of the first net to the
left boundary of the second along a pushout (identify the paired boundary places);
the pushout is realised concretely by the shipped fuel-bounded **union-find**
(`FX1Poly.Polygraph.unionFindJoin` / `unionFindRootOf`) over `Nat` place ids.  A
composite is canonicalised to a dense boundary-order-first place labelling with
`cswSort`-normalised transition multisets, and two open nets are decided equal by a
structural `beq` of their canonical forms.

Reuse (no re-derivation):
* the union-find pushout engine — `unionFindJoin`, `unionFindRootOf`
  (`WalkingAdjunction.MatchingDecision`);
* the sorted-`List Nat` multiset kit — `cswSort`, `cswListNatBeq`,
  `cswListNatBeqEq`, `cswLe`, `cswNatBeqEq`, `cswBoolAndElim`
  (`ComputerAlgebra.Semigroup.CommWordProblem`).

What lands: the carrier (`OcpTransition`/`OcpNet`/`OcpOpenNet`), `openNetCompose`,
`canonicalizeOpenNet`, a well-formedness predicate, the decision `decideOpenNetEq`
with two-sided-free **soundness** (`decideOpenNetEqSound`), the sound congruence
`OcpOpenNetConv` with `ocpOpenNetConvSound`, and the identity law demonstrated
inside the congruence on concrete nets.

Walls (concrete `false` markers with obstructions below): general net isomorphism
without the ordered boundary is graph-isomorphism-hard (`ocpHasGeneralNetIsoDecision`);
compositional coverability needs a WQO / Karp–Miller = the NET-4 Dickson wall
(`ocpHasCompositionalCoverability`); the *universal* cospan identity / associativity
laws over arbitrary boundary lists need the full `renameLinks_unionFindJoin` root
transport (`ocpHasUniversalIdentityLaw` / `ocpHasCospanAssociativity`).

Zero-axiom: no `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`, `funext`, `WellFounded.fix`, `decide`; no `&&`/`||` and no
wildcard match arms over a split scrutinee in shipped code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Net

open FX1Poly.Polygraph (unionFindJoin unionFindRootOf isSameComponent)
open FX1Poly.ComputerAlgebra (cswLe cswSort cswListNatBeq cswListNatBeqEq cswNatBeqEq cswBoolAndElim)

/-! ## Boolean micro-kit (no `&&`/`||`) -/

/-- Sequential conjunction on `Bool` without the `&&` token. -/
def ocpBoth (leftFlag rightFlag : Bool) : Bool :=
  match leftFlag with
  | true => rightFlag
  | false => false

/-- Elimination for `ocpBoth`: a true conjunction splits into two true conjuncts. -/
theorem ocpBothElim : (leftFlag rightFlag : Bool) → ocpBoth leftFlag rightFlag = true →
    leftFlag = true ∧ rightFlag = true
  | true, _, hBoth => ⟨rfl, hBoth⟩
  | false, _, hBoth => Bool.noConfusion hBoth

/-! ## The carrier — transitions, nets, open nets (cospans of place-sets) -/

/-- A transition: `pre`/`post` multisets over place ids, each a `cswSort`-sorted `List Nat`. -/
structure OcpTransition where
  pre : List Nat
  post : List Nat

/-- A Petri net: a list of place ids plus a list of transitions over them. -/
structure OcpNet where
  places : List Nat
  transitions : List OcpTransition

/-- An open Petri net: a net with two ordered boundary legs (the cospan
`leftBoundary → net ← rightBoundary`).  The legs are order-significant `List Nat`
(NOT sorted): the ordering is what makes the canonical relabelling deterministic. -/
structure OcpOpenNet where
  net : OcpNet
  leftBoundary : List Nat
  rightBoundary : List Nat

/-! ## Cons-only list utilities over `Nat` id lists -/

/-- Relabel every id in a `List Nat` by `renamer` (cons-only, no `List.map`). -/
def ocpMapId (renamer : Nat → Nat) : List Nat → List Nat
  | [] => []
  | head :: rest => renamer head :: ocpMapId renamer rest

/-- Membership as a `Bool` (cons-only, no `List.elem`). -/
def ocpMemBool (target : Nat) : List Nat → Bool
  | [] => false
  | head :: rest => cond (Nat.beq target head) true (ocpMemBool target rest)

/-- Every id in `candidates` is a member of `population`. -/
def ocpAllMem : List Nat → List Nat → Bool
  | [], _ => true
  | head :: rest, population => ocpBoth (ocpMemBool head population) (ocpAllMem rest population)

/-- Maximum of a `List Nat` (`0` on empty), via `cswLe`. -/
def ocpListMax : List Nat → Nat
  | [] => 0
  | head :: rest => let restMax := ocpListMax rest; cond (cswLe head restMax) restMax head

/-- Deduplicate keeping first occurrence, threading a `seen` accumulator. -/
def ocpDedupFrom (seen : List Nat) : List Nat → List Nat
  | [] => []
  | head :: rest =>
      cond (ocpMemBool head seen)
        (ocpDedupFrom seen rest)
        (head :: ocpDedupFrom (head :: seen) rest)

/-- Deduplicate a `List Nat` keeping first occurrence. -/
def ocpDedup (ids : List Nat) : List Nat := ocpDedupFrom [] ids

/-- First index of `target` in `order` (`order.length` when absent). -/
def ocpIndexOf : List Nat → Nat → Nat
  | [], _ => 0
  | head :: rest, target => cond (Nat.beq target head) 0 (Nat.succ (ocpIndexOf rest target))

/-! ## Transition relabelling and multiset normalisation -/

/-- Relabel a transition's pre/post ids by `renamer`. -/
def ocpTransRelabel (renamer : Nat → Nat) (transition : OcpTransition) : OcpTransition :=
  { pre := ocpMapId renamer transition.pre, post := ocpMapId renamer transition.post }

/-- Relabel every transition in a list. -/
def ocpTransListRelabel (renamer : Nat → Nat) : List OcpTransition → List OcpTransition
  | [] => []
  | head :: rest => ocpTransRelabel renamer head :: ocpTransListRelabel renamer rest

/-- Relabel then `cswSort`-normalise a transition's pre/post multisets. -/
def ocpTransNormalize (renamer : Nat → Nat) (transition : OcpTransition) : OcpTransition :=
  { pre := cswSort (ocpMapId renamer transition.pre),
    post := cswSort (ocpMapId renamer transition.post) }

/-- Normalise every transition in a list. -/
def ocpTransListNormalize (renamer : Nat → Nat) : List OcpTransition → List OcpTransition
  | [] => []
  | head :: rest => ocpTransNormalize renamer head :: ocpTransListNormalize renamer rest

/-! ## A total-ish transition order and insertion sort of transition lists -/

/-- Lexicographic `≤` on id lists (`cswLe` at the first differing position). -/
def ocpListLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      cond (Nat.beq leftHead rightHead) (ocpListLe leftRest rightRest) (cswLe leftHead rightHead)

/-- `≤` on transitions: compare `pre`, breaking ties on `post`. -/
def ocpTransLe (leftTransition rightTransition : OcpTransition) : Bool :=
  cond (cswListNatBeq leftTransition.pre rightTransition.pre)
    (ocpListLe leftTransition.post rightTransition.post)
    (ocpListLe leftTransition.pre rightTransition.pre)

/-- Ordered insert of a transition into a `ocpTransLe`-sorted list. -/
def ocpTransInsert (transition : OcpTransition) : List OcpTransition → List OcpTransition
  | [] => [transition]
  | head :: rest =>
      cond (ocpTransLe transition head)
        (transition :: head :: rest)
        (head :: ocpTransInsert transition rest)

/-- Insertion sort of a transition list (a deterministic canonical order). -/
def ocpTransSort : List OcpTransition → List OcpTransition
  | [] => []
  | head :: rest => ocpTransInsert head (ocpTransSort rest)

/-! ## Well-formedness -/

/-- Well-formed: both boundary legs' places are members of the net's place set. -/
def ocpIsWellFormed (openNet : OcpOpenNet) : Bool :=
  ocpBoth (ocpAllMem openNet.leftBoundary openNet.net.places)
    (ocpAllMem openNet.rightBoundary openNet.net.places)

/-! ## Boundary-glued composition (the pushout via union-find) -/

/-- All ids appearing in an open net (places and both legs). -/
def ocpAllIds (openNet : OcpOpenNet) : List Nat :=
  openNet.net.places ++ openNet.leftBoundary ++ openNet.rightBoundary

/-- A fresh offset strictly above every id of `openNet`. -/
def ocpOffset (openNet : OcpOpenNet) : Nat := Nat.succ (ocpListMax (ocpAllIds openNet))

/-- Fold `unionFindJoin` down two zipped boundary legs — the pushout gluing. -/
def ocpBuildGlue : List Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], _, links => links
  | _ :: _, [], links => links
  | leftHead :: leftRest, rightHead :: rightRest, links =>
      ocpBuildGlue leftRest rightRest (unionFindJoin links leftHead rightHead)

/-- Compose two open nets: offset the second net disjointly, glue the first's right
boundary to the second's (offset) left boundary via union-find, then rewrite every id
to its glued root.  New legs: the first's left boundary and the second's right boundary. -/
def openNetCompose (first second : OcpOpenNet) : OcpOpenNet :=
  let offset := ocpOffset first
  let shift := fun (placeId : Nat) => placeId + offset
  let secondPlaces := ocpMapId shift second.net.places
  let secondTransitions := ocpTransListRelabel shift second.net.transitions
  let secondLeft := ocpMapId shift second.leftBoundary
  let secondRight := ocpMapId shift second.rightBoundary
  let glueLinks := ocpBuildGlue first.rightBoundary secondLeft []
  let toRoot := fun (placeId : Nat) => unionFindRootOf glueLinks placeId
  { net :=
      { places := ocpMapId toRoot (first.net.places ++ secondPlaces),
        transitions := ocpTransListRelabel toRoot (first.net.transitions ++ secondTransitions) },
    leftBoundary := ocpMapId toRoot first.leftBoundary,
    rightBoundary := ocpMapId toRoot secondRight }

/-- The identity open net on a boundary: discrete places = the boundary, no
transitions, both legs = the boundary. -/
def identityOpenNet (boundary : List Nat) : OcpOpenNet :=
  { net := { places := boundary, transitions := [] },
    leftBoundary := boundary,
    rightBoundary := boundary }

/-! ## Canonicalisation to a dense boundary-order-first normal form -/

/-- The canonical id order: left leg, then right leg, then remaining places,
deduplicated keeping first occurrence. -/
def ocpCanonOrder (openNet : OcpOpenNet) : List Nat :=
  ocpDedup (openNet.leftBoundary ++ openNet.rightBoundary ++ openNet.net.places)

/-- Canonicalise: relabel every id to its dense boundary-order-first index, `cswSort`
each transition's multisets, sort the place list and the transition list. -/
def canonicalizeOpenNet (openNet : OcpOpenNet) : OcpOpenNet :=
  let order := ocpCanonOrder openNet
  let dense := fun (placeId : Nat) => ocpIndexOf order placeId
  { net :=
      { places := cswSort (ocpDedup (ocpMapId dense openNet.net.places)),
        transitions := ocpTransSort (ocpTransListNormalize dense openNet.net.transitions) },
    leftBoundary := ocpMapId dense openNet.leftBoundary,
    rightBoundary := ocpMapId dense openNet.rightBoundary }

/-! ## The decision — structural `beq` of canonical forms + soundness -/

/-- Structural equality of transitions (via `cswListNatBeq` on both multisets). -/
def ocpTransBeq (leftTransition rightTransition : OcpTransition) : Bool :=
  ocpBoth (cswListNatBeq leftTransition.pre rightTransition.pre)
    (cswListNatBeq leftTransition.post rightTransition.post)

/-- Structural equality of transition lists (cons-only). -/
def ocpTransListBeq : List OcpTransition → List OcpTransition → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      ocpBoth (ocpTransBeq leftHead rightHead) (ocpTransListBeq leftRest rightRest)

/-- Structural equality of nets. -/
def ocpNetBeq (leftNet rightNet : OcpNet) : Bool :=
  ocpBoth (cswListNatBeq leftNet.places rightNet.places)
    (ocpTransListBeq leftNet.transitions rightNet.transitions)

/-- Structural equality of open nets (net, then both legs). -/
def ocpOpenNetBeq (leftOpen rightOpen : OcpOpenNet) : Bool :=
  ocpBoth (ocpNetBeq leftOpen.net rightOpen.net)
    (ocpBoth (cswListNatBeq leftOpen.leftBoundary rightOpen.leftBoundary)
      (cswListNatBeq leftOpen.rightBoundary rightOpen.rightBoundary))

/-- Decide open-net equality: structural `beq` of the two canonical forms. -/
def decideOpenNetEq (leftOpen rightOpen : OcpOpenNet) : Bool :=
  ocpOpenNetBeq (canonicalizeOpenNet leftOpen) (canonicalizeOpenNet rightOpen)

/-- Soundness of transition `beq`. -/
theorem ocpTransBeqEq : (leftTransition rightTransition : OcpTransition) →
    ocpTransBeq leftTransition rightTransition = true → leftTransition = rightTransition
  | ⟨leftPre, leftPost⟩, ⟨rightPre, rightPost⟩, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      rw [cswListNatBeqEq leftPre rightPre hSplit.left,
        cswListNatBeqEq leftPost rightPost hSplit.right]

/-- Soundness of transition-list `beq`. -/
theorem ocpTransListBeqEq : (leftList rightList : List OcpTransition) →
    ocpTransListBeq leftList rightList = true → leftList = rightList
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      rw [ocpTransBeqEq leftHead rightHead hSplit.left,
        ocpTransListBeqEq leftRest rightRest hSplit.right]

/-- Soundness of net `beq`. -/
theorem ocpNetBeqEq : (leftNet rightNet : OcpNet) →
    ocpNetBeq leftNet rightNet = true → leftNet = rightNet
  | ⟨leftPlaces, leftTransitions⟩, ⟨rightPlaces, rightTransitions⟩, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      rw [cswListNatBeqEq leftPlaces rightPlaces hSplit.left,
        ocpTransListBeqEq leftTransitions rightTransitions hSplit.right]

/-- Soundness of open-net `beq`. -/
theorem ocpOpenNetBeqEq : (leftOpen rightOpen : OcpOpenNet) →
    ocpOpenNetBeq leftOpen rightOpen = true → leftOpen = rightOpen
  | ⟨leftNet, leftLeft, leftRight⟩, ⟨rightNet, rightLeft, rightRight⟩, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      have hLegs := ocpBothElim _ _ hSplit.right
      rw [ocpNetBeqEq leftNet rightNet hSplit.left,
        cswListNatBeqEq leftLeft rightLeft hLegs.left,
        cswListNatBeqEq leftRight rightRight hLegs.right]

/-- **The decision soundness**: `decideOpenNetEq` returning `true` means the two
open nets have equal canonical forms. -/
theorem decideOpenNetEqSound (leftOpen rightOpen : OcpOpenNet) :
    decideOpenNetEq leftOpen rightOpen = true →
    canonicalizeOpenNet leftOpen = canonicalizeOpenNet rightOpen := by
  intro hDecide
  exact ocpOpenNetBeqEq (canonicalizeOpenNet leftOpen) (canonicalizeOpenNet rightOpen) hDecide

/-! ## The cospan-algebra congruence and its soundness -/

/-- The cospan congruence on open nets, generated by canonical-form equality and
closed under symmetry and transitivity.  `OcpOpenNetConv l r` witnesses that `l`
and `r` denote the same morphism of the cospan category. -/
inductive OcpOpenNetConv : OcpOpenNet → OcpOpenNet → Prop where
  | ofCanonEq {leftOpen rightOpen : OcpOpenNet} :
      canonicalizeOpenNet leftOpen = canonicalizeOpenNet rightOpen → OcpOpenNetConv leftOpen rightOpen
  | symm {leftOpen rightOpen : OcpOpenNet} :
      OcpOpenNetConv leftOpen rightOpen → OcpOpenNetConv rightOpen leftOpen
  | trans {leftOpen middleOpen rightOpen : OcpOpenNet} :
      OcpOpenNetConv leftOpen middleOpen → OcpOpenNetConv middleOpen rightOpen →
      OcpOpenNetConv leftOpen rightOpen

/-- Reflexivity of the congruence. -/
theorem ocpOpenNetConvRefl (openNet : OcpOpenNet) : OcpOpenNetConv openNet openNet :=
  OcpOpenNetConv.ofCanonEq rfl

/-- **Congruence soundness**: convertible open nets have equal canonical forms. -/
theorem ocpOpenNetConvSound : (leftOpen rightOpen : OcpOpenNet) →
    OcpOpenNetConv leftOpen rightOpen → canonicalizeOpenNet leftOpen = canonicalizeOpenNet rightOpen
  | _, _, OcpOpenNetConv.ofCanonEq hEq => hEq
  | _, _, OcpOpenNetConv.symm hConv =>
      (ocpOpenNetConvSound _ _ hConv).symm
  | _, _, OcpOpenNetConv.trans hLeft hRight =>
      (ocpOpenNetConvSound _ _ hLeft).trans (ocpOpenNetConvSound _ _ hRight)

/-! ## Concrete open nets for the fires and the identity-law demonstration -/

/-- A concrete open net: one place `0` on the left, one place `1` on the right, a
single transition consuming `0` and producing `1`. -/
def ocpExampleA : OcpOpenNet :=
  { net := { places := [0, 1], transitions := [{ pre := [0], post := [1] }] },
    leftBoundary := [0],
    rightBoundary := [1] }

/-- A genuinely different open net: two disconnected places, transition `1 → 0`. -/
def ocpExampleB : OcpOpenNet :=
  { net := { places := [0, 1], transitions := [{ pre := [1], post := [0] }] },
    leftBoundary := [0],
    rightBoundary := [1] }

/-- The identity open net on `ocpExampleA`'s left boundary. -/
def ocpIdOnLeftA : OcpOpenNet := identityOpenNet ocpExampleA.leftBoundary

/-- The identity open net on `ocpExampleA`'s right boundary. -/
def ocpIdOnRightA : OcpOpenNet := identityOpenNet ocpExampleA.rightBoundary

/-! ## Capability markers and the walls -/

/-- Landed: the carrier + boundary-glued composition + canonical decision + the
soundness of the decision and of the cospan congruence. -/
def ocpHasOpenNetCospanDecision : Bool := true

/-- **WALL** — general net isomorphism WITHOUT the ordered boundary is
graph-isomorphism-complete.  The ordered legs `L → N ← R` are exactly what make the
canonical relabelling deterministic (boundary-index-first).  Drop the ordering and
`canonicalizeOpenNet` would have to canonicalise an unlabelled directed multigraph —
GI-hard, no zero-axiom decider.  Burned attacks: (1) a place-degree-sequence
invariant is incomplete (cospectral / regular counterexamples); (2) a brute-force
permutation search over place ids needs `WellFounded.fix` to terminate over the
unbounded id space. -/
def ocpHasGeneralNetIsoDecision : Bool := false

/-- **WALL** — compositional coverability / reachability across a composite is
Karp–Miller, whose termination rests on Dickson's lemma = the almost-full product,
a certified zero-axiom impossibility here (`fxNet4_dicksonWall`, needs
`WellFounded.fix`).  Burned attacks: (1) a bounded-unrolling `Bool` under-approximation
is one-sided (cannot certify non-coverability); (2) the covering-tree acceleration
that would make it two-sided is exactly Karp–Miller, walled at the NET-4 WQO. -/
def ocpHasCompositionalCoverability : Bool := false

/-- **WALL** — the *universal* cospan identity law
`canonicalizeOpenNet (openNetCompose (identityOpenNet a.leftBoundary) a) =
canonicalizeOpenNet a` for arbitrary `a`.  `openNetCompose` pattern-matches on `a`'s
boundary ids to build the glue links, so no `rfl`/`simp` reduction closes it
uniformly; the honest proof must transport `unionFindRootOf` through the offset+glue
relabelling — the `renameLinks_unionFindJoin` / `unionFindRootOf_unionFindJoin`
transport (`ArcSwapRenameable`), whose root-stabilisation over an arbitrary boundary
list rests on `WellFounded.fix`.  Burned attacks: (1) `by rfl` — fails, compose
matches on `a`; (2) structural induction on `a.leftBoundary` — the offset `ocpOffset`
and the dense `ocpIndexOf` both re-scan the whole net per step, so the inductive
hypothesis does not compose without the root-transport lemma.  Shipped instead: the
identity law on concrete nets (`ocpLeftIdConvConcrete` / `ocpRightIdConvConcrete`)
inside the sound congruence. -/
def ocpHasUniversalIdentityLaw : Bool := false

/-- **WALL** — the *universal* cospan associativity law
`canonicalizeOpenNet (openNetCompose (openNetCompose a b) c) =
canonicalizeOpenNet (openNetCompose a (openNetCompose b c))`.  Same obstruction as
the universal identity law, compounded: the two grouping orders offset `c` (resp.
`b,c`) by different amounts, so the pushouts agree only up to the injective
relabelling `renameLinks_unionFindJoin` — associativity of union-find gluing up to
canonical relabelling — which needs the root-transport / `WellFounded.fix`-backed
stabilisation of `ArcSwapRenameable`.  Burned attacks: (1) `by rfl` — the offsets
differ, canonical forms are not definitionally equal; (2) reduce to the abstract
`IsPushout.uniqueUpToIso` (`PushoutContexts`) — that is the *statement* to mirror but
gives no concrete zero-axiom `unionFindRootOf` computation. -/
def ocpHasCospanAssociativity : Bool := false

/-! ## Fires (T5) — ground `rfl` evaluations the build must accept -/

/-- FIRE: an open net composed with the identity open net (on its left boundary)
decides equal to the original, up to canonical form. -/
theorem ocpFireLeftIdDecidesEqual :
    decideOpenNetEq (openNetCompose ocpIdOnLeftA ocpExampleA) ocpExampleA = true := rfl

/-- FIRE: an open net composed with the identity on its right boundary decides equal. -/
theorem ocpFireRightIdDecidesEqual :
    decideOpenNetEq (openNetCompose ocpExampleA ocpIdOnRightA) ocpExampleA = true := rfl

/-- FIRE: two genuinely different open nets decide `false`. -/
theorem ocpFireDistinctDecideFalse : decideOpenNetEq ocpExampleA ocpExampleB = false := rfl

/-- FIRE (control): every open net decides equal to itself. -/
theorem ocpFireSelfDecidesEqual : decideOpenNetEq ocpExampleA ocpExampleA = true := rfl

/-- FIRE: the boundary glue of the identity on `[0]` with `ocpExampleA` produces a
composite whose canonical form has exactly the two expected places `[0, 1]`. -/
theorem ocpFireGlueCanonicalPlaces :
    (canonicalizeOpenNet (openNetCompose ocpIdOnLeftA ocpExampleA)).net.places = [0, 1] := rfl

/-- The identity law INSIDE the sound congruence, on a concrete net (left unit). -/
theorem ocpLeftIdConvConcrete :
    OcpOpenNetConv (openNetCompose ocpIdOnLeftA ocpExampleA) ocpExampleA :=
  OcpOpenNetConv.ofCanonEq (by rfl)

/-- The identity law INSIDE the sound congruence, on a concrete net (right unit). -/
theorem ocpRightIdConvConcrete :
    OcpOpenNetConv (openNetCompose ocpExampleA ocpIdOnRightA) ocpExampleA :=
  OcpOpenNetConv.ofCanonEq (by rfl)

end FX1Poly.Polygraph.Net
