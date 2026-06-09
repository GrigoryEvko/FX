import FX1Poly.Core.MultisetOrder

/-! # FX1Poly/Core/RecursivePathOrderInductive
    — #1139 (Leg 3): the genuine INDUCTIVE recursive path order on a rose-tree term algebra, defined
    zero-axiom (positivity-accepted) and shown to ORIENT the firing-68 branch-duplication obstruction arm
    that defeats every flat measure

Firing-67 (`IotaNonRecursiveTermination`) gave the 13 NON-recursive ι arms a clean `RawTerm.size`-decrease
SN.  Firing-68 (`RecursiveIotaSizeGrowth`) proved the RECURSIVE arm `natElim (succ n) z s ↝ app (app s n)
(elim n z s)` INCREASES `RawTerm.size` by `branch.size + 5`, growing without bound — so NO flat numeric
measure certifies it.  The branch `s` is DUPLICATED (it appears in both `app s n` and the recursive
`elim n z s`), and a flat multiset of scrutinee-sizes fails for the same reason: the duplicated copies of
`s`'s internal eliminators are ADDED with no corresponding removal, which is not a Dershowitz-Manna step.

The honest resolution — the standard one for primitive recursion / Gödel's T ι-rules — is a genuine
RECURSIVE PATH ORDER (RPO) whose multiset comparison is over the RPO relation ITSELF (recursively), with a
precedence `eliminator > app` on the head symbols.  The single-level certificates in `RecursivePathOrder`
(`wellFounded_of_precedence{Lex,Multiset}Measure`) compare head precedence then the IMMEDIATE-argument
multiset over a FIXED base order — they do not recurse into subterms, so they cannot certify the
congruence-closed recursive ι.  This file builds the genuine inductive RPO that does.

## What this ships

  * `RoseTerm Symbol` — the generic rose-tree term algebra (`mkGen gen children` of `RawTerm` instantiates
    it: gen ↦ symbol, children ↦ child list).  The RPO is generic so it ports to `RawTerm` directly.
  * `Rpo prec` — the inductive recursive path order with MULTISET status (`Rpo prec big small` reads
    `big ≻ small`).  Four clauses: `subtermEq` (a node dominates each direct child), `subtermStrict` (a node
    dominates anything a child dominates — the subterm property), `precedence` (higher head precedence, and
    the bigger dominates every reduct child), and `multiset` (equal head, the argument multiset
    Dershowitz-Manna-decreases under `Rpo` itself, and the bigger dominates every reduct child).
  * **`rpo_orients_natElim` (★)** — the RPO ORIENTS the firing-68 obstruction arm: `redex ≻ reduct` for
    `natElim (succ n) z s ≻ app (app s n) (elim n z s)`, for an ARBITRARY branch `s` (faithful
    branch-duplication).  This is exactly the arm no flat measure could orient (firing-68); the subterm
    property tames the duplication regardless of `s`'s size.
  * **`fxPrecedence_wellFounded` (★)** — the head precedence is well-founded (the first ingredient of RPO
    well-foundedness): `eliminator > app > succ > zero` is the inverse image of `Nat.lt` under a rank.

## Positivity (the genuine Lean hurdle this firing cleared)

Two kernel obstructions, both solved:
  * The subterm clause is SPLIT into `subtermEq` / `subtermStrict` rather than written with a single
    `subtermChild = small ∨ Rpo prec subtermChild small` premise — the kernel treats `Or` applied to the
    inductive-being-defined as a NESTED inductive whose parameters may not contain the local variables, and
    rejects it.  Splitting removes the `Or`.
  * The `multiset` clause INLINES the Dershowitz-Manna witnesses (`removed`, `prefix`/`suffix`/`added`
    lists, and the two `∀ … → Rpo prec …` premises) directly, rather than carrying `MultisetRedOne (Rpo
    prec)` as a premise — passing the inductive-being-defined as a relation argument to the external
    `MultisetRedOne` def is rejected by the strict-positivity checker (it cannot see the positive use).
    Inlined, every `Rpo` occurrence sits strictly positively to the right of `∀`/`→`.

## The named WF crux (next, multi-firing)

The full RPO WELL-FOUNDEDNESS theorem `WellFounded (fun small big => Rpo prec big small)` (given
`WellFounded prec`) is the Nipkow/Buchholz nested-accessibility proof: `acc_node` by induction on the head's
precedence-accessibility (outer) and the children's multiset-accessibility (inner, supplied by the shipped
`MultisetRedOne.consAccessible` from each child's accessibility), discharging the four clauses.  That is the
genuinely large remaining proof; this file supplies its definition, its orientation obligation (the
per-arm decrease), and its precedence-WF ingredient.  The β boundary stays honestly Tait-imported (raw β is
non-SN — Ω, SN-NECESSITY #950); #1139 separates the terminating ι/η fragment from it.

## Zero-axiom verification

The inductive is strictly positive (subterm-split + inlined multiset witnesses); the orientation is by the
four constructors + `List.Mem.head`/`.tail` (propext-free) + `decide` on closed `Nat` `<`; precedence-WF is
`InvImage.wf` of `Nat.lt`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core.RpoInductive

/-- Generic rose-tree term algebra: a head symbol applied to a list of child terms.
    `RawTerm`'s `mkGen gen children` instantiates this (gen ↦ symbol, children ↦ child list). -/
inductive RoseTerm (Symbol : Type) where
  | node : Symbol → List (RoseTerm Symbol) → RoseTerm Symbol

variable {Symbol : Type}

/-- The recursive path order with multiset status.  `Rpo prec big small` reads `big ≻ small`.
    `prec smallSym bigSym` reads `bigSym ≻F smallSym` (precedence on heads).
    The subterm clause is SPLIT into `subtermEq`/`subtermStrict` (no `∨`, which the kernel would treat as a
    nested inductive forbidding the local `Rpo` occurrence); the multiset clause's witnesses are INLINED
    (not via the external `MultisetRedOne (Rpo prec)`, which strict-positivity rejects). -/
inductive Rpo (prec : Symbol → Symbol → Prop) : RoseTerm Symbol → RoseTerm Symbol → Prop where
  | subtermEq (headSym : Symbol) (children : List (RoseTerm Symbol))
      (subtermChild : RoseTerm Symbol) :
      subtermChild ∈ children →
      Rpo prec (.node headSym children) subtermChild
  | subtermStrict (headSym : Symbol) (children : List (RoseTerm Symbol))
      (smaller subtermChild : RoseTerm Symbol) :
      subtermChild ∈ children →
      Rpo prec subtermChild smaller →
      Rpo prec (.node headSym children) smaller
  | precedence (bigSym : Symbol) (bigChildren : List (RoseTerm Symbol))
      (smallSym : Symbol) (smallChildren : List (RoseTerm Symbol)) :
      prec smallSym bigSym →
      (∀ smallChild, smallChild ∈ smallChildren →
        Rpo prec (.node bigSym bigChildren) smallChild) →
      Rpo prec (.node bigSym bigChildren) (.node smallSym smallChildren)
  | multiset (headSym : Symbol) (bigChildren smallChildren : List (RoseTerm Symbol))
      (removed : RoseTerm Symbol)
      (prefixChildren suffixChildren addedChildren : List (RoseTerm Symbol)) :
      bigChildren = prefixChildren ++ removed :: suffixChildren →
      smallChildren = prefixChildren ++ addedChildren ++ suffixChildren →
      (∀ addedChild, addedChild ∈ addedChildren → Rpo prec removed addedChild) →
      (∀ smallChild, smallChild ∈ smallChildren →
        Rpo prec (.node headSym bigChildren) smallChild) →
      Rpo prec (.node headSym bigChildren) (.node headSym smallChildren)

/-- A concrete eliminator-fragment symbol set: app, zero, succ, elim. -/
inductive FxElimSym where
  | appSym | zeroSym | succSym | elimSym

/-- Precedence rank: `elim` outranks `app` outranks the constructors. -/
def precedenceRank : FxElimSym → Nat
  | .zeroSym => 0
  | .succSym => 1
  | .appSym => 2
  | .elimSym => 3

/-- The precedence: a smaller rank is `≻F`-below a bigger one. -/
def fxPrecedence (smallSym bigSym : FxElimSym) : Prop :=
  precedenceRank smallSym < precedenceRank bigSym

abbrev FxTerm := RoseTerm FxElimSym

/-- `natElim (succ n) z s` redex (firing-68's obstruction arm), faithful branch `s`. -/
def natElimRedex (predScrut zeroBranch succBranch : FxTerm) : FxTerm :=
  .node .elimSym [.node .succSym [predScrut], zeroBranch, succBranch]

/-- Its reduct `app (app s n) (elim n z s)` — branch `s` DUPLICATED. -/
def natElimReduct (predScrut zeroBranch succBranch : FxTerm) : FxTerm :=
  .node .appSym
    [.node .appSym [succBranch, predScrut],
     .node .elimSym [predScrut, zeroBranch, succBranch]]

/-- `node f children ≻ n` whenever a direct `succ`-child holds `n`: the `succ n ≻ n` step packaged. -/
private theorem rpo_via_succ_child (predScrut : FxTerm) (headSym : FxElimSym)
    (children : List FxTerm) (membership : (.node .succSym [predScrut]) ∈ children) :
    Rpo fxPrecedence (.node headSym children) predScrut :=
  Rpo.subtermStrict headSym children predScrut (.node .succSym [predScrut]) membership
    (Rpo.subtermEq .succSym [predScrut] predScrut (List.Mem.head _))

/-- **The RPO orients the firing-68 obstruction arm** — `redex ≻ reduct` despite branch-duplication.
The reduct's outer head is `app`, below the redex's `elim` in the precedence, and the redex dominates each
reduct child: `app s n` (again by precedence, dominating `s` and `n` as subterms) and the recursive
`elim n z s` (same head, multiset step `[succ n] ↦ [n]` since `succ n ≻ n`).  No flat measure could orient
this (firing-68); the subterm property tames the duplicated `s` regardless of its size. -/
theorem rpo_orients_natElim (predScrut zeroBranch succBranch : FxTerm) :
    Rpo fxPrecedence (natElimRedex predScrut zeroBranch succBranch)
      (natElimReduct predScrut zeroBranch succBranch) := by
  dsimp only [natElimRedex, natElimReduct]
  -- redex ≻ app(app s n)(elim n z s) by precedence (elim ≻F app), redex ≻ each child
  refine Rpo.precedence (bigSym := FxElimSym.elimSym) (bigChildren := _)
    (smallSym := FxElimSym.appSym) (smallChildren := _) ?_ ?_
  · exact (by decide : precedenceRank .appSym < precedenceRank .elimSym)
  · intro smallChild membership
    rcases membership with _ | ⟨_, membershipRest⟩
    · -- child = app s n : redex ≻ app s n by precedence (elim ≻F app), redex ≻ s, redex ≻ n
      refine Rpo.precedence (bigSym := FxElimSym.elimSym) (bigChildren := _)
        (smallSym := FxElimSym.appSym) (smallChildren := _) ?_ ?_
      · exact (by decide : precedenceRank .appSym < precedenceRank .elimSym)
      · intro innerChild innerMembership
        rcases innerMembership with _ | ⟨_, innerRest⟩
        · -- s : direct subterm (3rd child of redex)
          exact Rpo.subtermEq .elimSym _ succBranch
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        · rcases innerRest with _ | ⟨_, innerEmpty⟩
          · -- n : subterm via succ child
            exact rpo_via_succ_child predScrut .elimSym _ (List.Mem.head _)
          · nomatch innerEmpty
    · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
      · -- child = elim n z s : same head, multiset step [succ n] ↦ [n] (succ n ≻ n)
        refine Rpo.multiset _ _ _ (.node .succSym [predScrut]) [] [zeroBranch, succBranch]
          [predScrut] rfl rfl ?_ ?_
        · intro addedChild addedMembership
          rcases addedMembership with _ | ⟨_, addedEmpty⟩
          · exact Rpo.subtermEq .succSym _ predScrut (List.Mem.head _)
          · nomatch addedEmpty
        · intro smallChild smallMembership
          rcases smallMembership with _ | ⟨_, smallRest⟩
          · -- n : subterm via succ child
            exact rpo_via_succ_child predScrut .elimSym _ (List.Mem.head _)
          · rcases smallRest with _ | ⟨_, smallRest2⟩
            · -- z : direct subterm (2nd child)
              exact Rpo.subtermEq .elimSym _ zeroBranch (List.Mem.tail _ (List.Mem.head _))
            · rcases smallRest2 with _ | ⟨_, smallEmpty⟩
              · -- s : direct subterm (3rd child)
                exact Rpo.subtermEq .elimSym _ succBranch
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              · nomatch smallEmpty
      · nomatch membershipEmpty

/-- **The precedence is well-founded** (the first ingredient of RPO well-foundedness): a smaller
`precedenceRank` is below a bigger, so `fxPrecedence` is the inverse image of `Nat.lt` under the rank. -/
theorem fxPrecedence_wellFounded : WellFounded fxPrecedence :=
  InvImage.wf precedenceRank Nat.lt_wfRel.wf

end FX1Poly.Core.RpoInductive
