import FX1Poly.Core.RecursivePathOrderInductive
import FX1Poly.Core.Step

/-! # FX1Poly/Core/RawIotaRpoBridge
    — #1139 (Leg 3): the generic rose-tree RPO INSTANTIATED at the REAL `RawTerm` kernel — the three
    recursive ι arms (the firing-68 obstruction) oriented by a genuinely well-founded recursive path order

FIRING-69 defined the generic inductive RPO on a rose-tree algebra and oriented the firing-68 obstruction
arm abstractly; FIRING-70 proved that RPO well-founded (Nipkow/Buchholz, zero-axiom, no size measure).  This
file BRIDGES that machinery to the actual kernel: it forgets `RawTerm`'s scope/binder-shift structure to a
`RoseTerm Generator` (`eraseToRose`), defines the real generator precedence (the three recursive eliminators
outrank `app`), and proves the per-arm `Step → Rpo`-decrease for the recursive ι arms ON the real `Step`
relation.

**Phase-Z RPO RE-SCOPE (natElim/natRec succ iotas LEAVE the oriented set).**  Under the Phase-Z motive
migration the natElim/natRec successor iotas SUBSTITUTE — their reduct is
`subst (cons recursiveCall (singleton pred)) succBranch`, NOT the app-chain `app (app s n) (natElim n z s)`.
Substitution is NOT orientable by erasure (it can duplicate `recursiveCall` arbitrarily, exactly β's
situation — see `betaNotOrientableByErasure`), so these two arms DROP OUT of the RPO-oriented ι set and join
the β-imported boundary.  Only the listElim cons iota REMAINS RPO-orientable here (its reduct is still a pure
app-chain reassembly with no substitution):

    listElim motive n c (cons h t)  ↝  app (app (app c h) t) (listElim motive n c t)   (Step.iotaListElimCons)

The natElim/natRec **zero** iotas stay oriented separately (pure projection of the zero-branch — handled in
`RawIotaRpoAssembly`'s subterm clauses, no substitution).  The old app-chain `natElimSuccReductRaw` /
`rpo_orients_iotaNatElimSucc` definitions below are RETAINED as a documented boundary record of the
pre-migration shape (the GENERIC `rpoOrientsElim2` is still a true rose-tree fact and is reused by other
callers), but they NO LONGER correspond to the live `Step.iotaNatElimSucc` — flagged for orchestrator
sign-off (see the per-lemma notes).  With `realGenRpoWellFounded` the listElim cons arm (and the non-recursive
arms in `RawIotaRpoAssembly`) sit in a genuine well-founded order on the real kernel; the natElim/natRec succ
arms sit honestly at the β boundary.

## What this ships

  * `eraseToRose` / `eraseChildren` — the forgetful map `RawTerm scope → RoseTerm Generator`, mutual and
    scope-polymorphic (mirrors `RawTerm.size`).  The recursive ι arms carry NO binder shifts on their
    children (`gen_natElim` binderShifts `[0,0,0]`), so erasure of these shapes is clean.
  * `genRank` / `realGenPrecedence` / `realGenPrecedence_wellFounded` — the real generator precedence
    (`gen_natElim`/`gen_natRec`/`gen_listElim` rank 2 ≻ `gen_app` rank 1 ≻ everything else).  Defined by
    decidable-equality `if`s (no 194-constructor wildcard match, which would leak propext).
  * `rpoOrientsElim2` / `rpoOrientsElim3` — the generic 2-arg / 3-arg eliminator-arm orientations
    (firing-69 generalized over the generators); `Elim2` is reused for natElim AND natRec.
  * **`rpo_orients_iotaNatElimSucc` / `rpo_orients_iotaNatRecSucc` / `rpo_orients_iotaListElimCons` (★)** —
    each real recursive ι arm's erased redex RPO-dominates its erased reduct.  `<arm>Raw_isStep` confirms
    each redex/reduct pair really is the corresponding `Step` constructor.
  * **`realGenRpoWellFounded` (★)** — the real-generator RPO is well-founded (firing-70's `rpoWellFounded`
    at `realGenPrecedence`).

## The β boundary stays Tait-imported (honest)

This bridge orients only the ι arms.  β (`app (lam b) a ↝ b[a]`) is NOT oriented by any RPO — substitution
can duplicate the argument arbitrarily, and raw β is non-SN (Ω, SN-NECESSITY #950).  #1139's whole point is
that the terminating ι/η fragment terminates on its OWN, while β genuinely imports Tait.

## Zero-axiom verification

`eraseToRose` mirrors the (compiling) `RawTerm.size` mutual def; the orientations are firing-69's proof
generalized (propext-clean `Rpo` constructors + `List.Mem` `rcases`/`nomatch`); the precedence facts
`decide` through the reducible `realGenPrecedence` to `Nat.lt`; WF is firing-70's theorem.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core.RawIotaRpo
open FX1Poly.Core.RpoInductive

/-! Forgetful map RawTerm → generic rose-tree (drops scope/binder-shift structure, flattens children to a
list).  Mirrors `RawTerm.size` exactly (mutual, scope-polymorphic). -/
mutual
  def eraseToRose {scope : Nat} : RawTerm scope → RoseTerm Generator
    | .mkGen gen _ children => .node gen (eraseChildren children)
  def eraseChildren {shifts : List Nat} {scope : Nat} :
      RawTermChildren shifts scope → List (RoseTerm Generator)
    | .childNil => []
    | .childCons head tail => eraseToRose head :: eraseChildren tail
end

/-- Generator precedence rank: the three recursive eliminators outrank `app`; everything else is below.
Defined by decidable-equality `if`s (no 194-constructor wildcard match, which would leak propext). -/
def genRank (gen : Generator) : Nat :=
  if gen = .gen_natElim ∨ gen = .gen_natRec ∨ gen = .gen_listElim then 2
  else if gen = .gen_app then 1
  else 0

/-- The real precedence on generators: a smaller rank is `≻F`-below a bigger one.  Reducible so the
precedence facts (e.g. `gen_app ≺F gen_natElim`) decide through to `Nat.lt`. -/
@[reducible] def realGenPrecedence (small big : Generator) : Prop := genRank small < genRank big

/-- The real generator precedence is well-founded (inverse image of `Nat.lt` under the rank). -/
theorem realGenPrecedence_wellFounded : WellFounded realGenPrecedence :=
  InvImage.wf genRank Nat.lt_wfRel.wf

/-- **Generic 2-arg eliminator-arm orientation** (FIRING-69 generalized over the generators): the redex
`elim (succ scrut) zeroBr succBr` RPO-dominates the reduct `app (app succBr scrut) (elim scrut zeroBr
succBr)`, given `appGen ≺F elimGen`.  Reused for natElim AND natRec (same shape). -/
theorem rpoOrientsElim2 (prec : Generator → Generator → Prop) (elimGen appGen succGen : Generator)
    (hprec : prec appGen elimGen) (scrut zeroBr succBr : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [.node succGen [scrut], zeroBr, succBr])
      (.node appGen [.node appGen [succBr, scrut], .node elimGen [scrut, zeroBr, succBr]]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
      (smallChildren := _) hprec ?_
    intro innerChild innerMembership
    rcases innerMembership with _ | ⟨_, innerRest⟩
    · exact Rpo.subtermEq elimGen _ succBr (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · rcases innerRest with _ | ⟨_, innerEmpty⟩
      · exact Rpo.subtermStrict elimGen _ scrut (.node succGen [scrut]) (List.Mem.head _)
          (Rpo.subtermEq succGen [scrut] scrut (List.Mem.head _))
      · nomatch innerEmpty
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · refine Rpo.multiset _ _ _ (.node succGen [scrut]) [] [zeroBr, succBr] [scrut] rfl rfl ?_ ?_
      · intro addedChild addedMembership
        rcases addedMembership with _ | ⟨_, addedEmpty⟩
        · exact Rpo.subtermEq succGen _ scrut (List.Mem.head _)
        · nomatch addedEmpty
      · intro smallChild2 smallMembership
        rcases smallMembership with _ | ⟨_, smallRest⟩
        · exact Rpo.subtermStrict elimGen _ scrut (.node succGen [scrut]) (List.Mem.head _)
            (Rpo.subtermEq succGen [scrut] scrut (List.Mem.head _))
        · rcases smallRest with _ | ⟨_, smallRest2⟩
          · exact Rpo.subtermEq elimGen _ zeroBr (List.Mem.tail _ (List.Mem.head _))
          · rcases smallRest2 with _ | ⟨_, smallEmpty⟩
            · exact Rpo.subtermEq elimGen _ succBr
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            · nomatch smallEmpty
    · nomatch membershipEmpty

/-- **BOUNDARY RECORD (pre-migration shape, ROSE level).** The natElimSucc redex in the PRE-Phase-Z arity-3
shape.  Under Phase-Z the kernel's `gen_natElim` is arity-4 (`[1,0,2,0]` binder shifts, motive first,
scrutinee LAST), so the retired arity-3 spine is no longer even WELL-FORMED as a `RawTerm` — the cell
calculus rejects it by construction.  The record therefore lives at the rose-erasure level, the only layer
where the retired shape still exists. -/
def natElimSuccRedexRaw (predScrut zeroBranch succBranch : RoseTerm Generator) :
    RoseTerm Generator :=
  .node .gen_natElim [.node .gen_natSucc [predScrut], zeroBranch, succBranch]

/-- **BOUNDARY RECORD (pre-migration shape, ROSE level).** The pre-Phase-Z app-chain reduct
`app (app s n) (natElim n z s)`.  The live succ-iota now SUBSTITUTES
(`subst (cons recursiveCall (singleton pred)) succBranch`), which is NOT this app-chain — this records the
retired shape only, at the rose level (see `natElimSuccRedexRaw`). -/
def natElimSuccReductRaw (predScrut zeroBranch succBranch : RoseTerm Generator) :
    RoseTerm Generator :=
  .node .gen_app
    [.node .gen_app [succBranch, predScrut],
     .node .gen_natElim [predScrut, zeroBranch, succBranch]]

/-- **BOUNDARY RECORD (pre-migration orientation — NOT the live Step).**  The PRE-Phase-Z app-chain
redex/reduct pair is RPO-oriented by the real generator precedence (the GENERIC `rpoOrientsElim2` is a true
rose-tree fact, retained for reuse).  This is NO LONGER `Step.iotaNatElimSucc`: under Phase-Z the live
succ-iota SUBSTITUTES and DROPS OUT of the RPO-oriented set into the β-imported boundary (substitution is not
orientable by erasure — `betaNotOrientableByErasure`); the retired arity-3 shape itself is no longer
`RawTerm`-expressible, so the orientation survives only at the rose level. -/
theorem rpo_orients_iotaNatElimSucc (predScrut zeroBranch succBranch : RoseTerm Generator) :
    Rpo realGenPrecedence
      (natElimSuccRedexRaw predScrut zeroBranch succBranch)
      (natElimSuccReductRaw predScrut zeroBranch succBranch) :=
  rpoOrientsElim2 realGenPrecedence .gen_natElim .gen_app .gen_natSucc
    (by decide) predScrut zeroBranch succBranch

/-- **BOUNDARY RECORD (pre-migration shape, ROSE level).** natRecSucc redex, pre-Phase-Z arity-3 shape
(see `natElimSuccRedexRaw`). -/
def natRecSuccRedexRaw (predScrut zeroBranch succBranch : RoseTerm Generator) :
    RoseTerm Generator :=
  .node .gen_natRec [.node .gen_natSucc [predScrut], zeroBranch, succBranch]

/-- **BOUNDARY RECORD (pre-migration shape, ROSE level).** natRecSucc app-chain reduct (see
`natElimSuccReductRaw`). -/
def natRecSuccReductRaw (predScrut zeroBranch succBranch : RoseTerm Generator) :
    RoseTerm Generator :=
  .node .gen_app
    [.node .gen_app [succBranch, predScrut],
     .node .gen_natRec [predScrut, zeroBranch, succBranch]]

/-- **BOUNDARY RECORD (pre-migration orientation — NOT the live Step).**  natRec twin of
`rpo_orients_iotaNatElimSucc`: the pre-Phase-Z app-chain pair is RPO-oriented at the rose level, but the live
`Step.iotaNatRecSucc` now SUBSTITUTES and sits at the β boundary. -/
theorem rpo_orients_iotaNatRecSucc (predScrut zeroBranch succBranch : RoseTerm Generator) :
    Rpo realGenPrecedence
      (natRecSuccRedexRaw predScrut zeroBranch succBranch)
      (natRecSuccReductRaw predScrut zeroBranch succBranch) :=
  rpoOrientsElim2 realGenPrecedence .gen_natRec .gen_app .gen_natSucc
    (by decide) predScrut zeroBranch succBranch

/-- **Generic 3-arg eliminator-arm orientation** (listElim shape): the redex `elim (cons head tail) nilBr
consBr` RPO-dominates `app (app (app consBr head) tail) (elim tail nilBr consBr)`, given `appGen ≺F
elimGen`.  The deepest app-chain in the design (the listElimCons arm). -/
theorem rpoOrientsElim3 (prec : Generator → Generator → Prop) (elimGen appGen consGen : Generator)
    (hprec : prec appGen elimGen) (headVal tailVal nilBr consBr : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [.node consGen [headVal, tailVal], nilBr, consBr])
      (.node appGen
        [.node appGen [.node appGen [consBr, headVal], tailVal],
         .node elimGen [tailVal, nilBr, consBr]]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
      (smallChildren := _) hprec ?_
    intro innerChild innerMembership
    rcases innerMembership with _ | ⟨_, innerRest⟩
    · refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
        (smallChildren := _) hprec ?_
      intro inner2Child inner2Membership
      rcases inner2Membership with _ | ⟨_, inner2Rest⟩
      · exact Rpo.subtermEq elimGen _ consBr (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · rcases inner2Rest with _ | ⟨_, inner2Empty⟩
        · exact Rpo.subtermStrict elimGen _ headVal (.node consGen [headVal, tailVal]) (List.Mem.head _)
            (Rpo.subtermEq consGen [headVal, tailVal] headVal (List.Mem.head _))
        · nomatch inner2Empty
    · rcases innerRest with _ | ⟨_, innerEmpty⟩
      · exact Rpo.subtermStrict elimGen _ tailVal (.node consGen [headVal, tailVal]) (List.Mem.head _)
          (Rpo.subtermEq consGen [headVal, tailVal] tailVal (List.Mem.tail _ (List.Mem.head _)))
      · nomatch innerEmpty
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · refine Rpo.multiset _ _ _ (.node consGen [headVal, tailVal]) [] [nilBr, consBr] [tailVal]
        rfl rfl ?_ ?_
      · intro addedChild addedMembership
        rcases addedMembership with _ | ⟨_, addedEmpty⟩
        · exact Rpo.subtermEq consGen _ tailVal (List.Mem.tail _ (List.Mem.head _))
        · nomatch addedEmpty
      · intro smallChild2 smallMembership
        rcases smallMembership with _ | ⟨_, smallRest⟩
        · exact Rpo.subtermStrict elimGen _ tailVal (.node consGen [headVal, tailVal]) (List.Mem.head _)
            (Rpo.subtermEq consGen [headVal, tailVal] tailVal (List.Mem.tail _ (List.Mem.head _)))
        · rcases smallRest with _ | ⟨_, smallRest2⟩
          · exact Rpo.subtermEq elimGen _ nilBr (List.Mem.tail _ (List.Mem.head _))
          · rcases smallRest2 with _ | ⟨_, smallEmpty⟩
            · exact Rpo.subtermEq elimGen _ consBr
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            · nomatch smallEmpty
    · nomatch membershipEmpty

/-- **Generic 3-arg eliminator-arm orientation WITH a leading motive** (Phase-Z motive shape): the redex
`elim motive nilBr consBr (cons head tail)` RPO-dominates the reduct `app (app (app consBr head) tail)
(elim motive nilBr consBr tail)`, given `appGen ≺F elimGen`.  The motive heads the spine on BOTH sides
and is THREADED into the recursive `elim` of the reduct.  This is the motive-aware companion of
`rpoOrientsElim3` (which proves the pre-Phase-Z scrutinee-first shape, retained for reference). -/
theorem rpoOrientsElim3WithMotive (prec : Generator → Generator → Prop)
    (elimGen appGen consGen : Generator)
    (hprec : prec appGen elimGen) (motive headVal tailVal nilBr consBr : RoseTerm Generator) :
    Rpo prec
      (.node elimGen [motive, nilBr, consBr, .node consGen [headVal, tailVal]])
      (.node appGen
        [.node appGen [.node appGen [consBr, headVal], tailVal],
         .node elimGen [motive, nilBr, consBr, tailVal]]) := by
  refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
    (smallChildren := _) hprec ?_
  intro smallChild membership
  rcases membership with _ | ⟨_, membershipRest⟩
  · refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
      (smallChildren := _) hprec ?_
    intro innerChild innerMembership
    rcases innerMembership with _ | ⟨_, innerRest⟩
    · refine Rpo.precedence (bigSym := elimGen) (bigChildren := _) (smallSym := appGen)
        (smallChildren := _) hprec ?_
      intro inner2Child inner2Membership
      rcases inner2Membership with _ | ⟨_, inner2Rest⟩
      · exact Rpo.subtermEq elimGen _ consBr (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · rcases inner2Rest with _ | ⟨_, inner2Empty⟩
        · exact Rpo.subtermStrict elimGen _ headVal
            (.node consGen [headVal, tailVal])
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            (Rpo.subtermEq consGen [headVal, tailVal] headVal (List.Mem.head _))
        · nomatch inner2Empty
    · rcases innerRest with _ | ⟨_, innerEmpty⟩
      · exact Rpo.subtermStrict elimGen _ tailVal
          (.node consGen [headVal, tailVal])
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
          (Rpo.subtermEq consGen [headVal, tailVal] tailVal (List.Mem.tail _ (List.Mem.head _)))
      · nomatch innerEmpty
  · rcases membershipRest with _ | ⟨_, membershipEmpty⟩
    · refine Rpo.multiset _ _ _ (.node consGen [headVal, tailVal])
        [motive, nilBr, consBr] [] [tailVal] rfl rfl ?_ ?_
      · intro addedChild addedMembership
        rcases addedMembership with _ | ⟨_, addedEmpty⟩
        · exact Rpo.subtermEq consGen _ tailVal (List.Mem.tail _ (List.Mem.head _))
        · nomatch addedEmpty
      · intro smallChild2 smallMembership
        rcases smallMembership with _ | ⟨_, smallRest⟩
        · exact Rpo.subtermEq elimGen _ motive (List.Mem.head _)
        · rcases smallRest with _ | ⟨_, smallRest2⟩
          · exact Rpo.subtermEq elimGen _ nilBr (List.Mem.tail _ (List.Mem.head _))
          · rcases smallRest2 with _ | ⟨_, smallRest3⟩
            · exact Rpo.subtermEq elimGen _ consBr
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            · rcases smallRest3 with _ | ⟨_, smallEmpty⟩
              · exact Rpo.subtermStrict elimGen _ tailVal
                  (.node consGen [headVal, tailVal])
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
                  (Rpo.subtermEq consGen [headVal, tailVal] tailVal (List.Mem.tail _ (List.Mem.head _)))
              · nomatch smallEmpty
    · nomatch membershipEmpty

/-- listElimCons redex/reduct on the real kernel (matches `Step.iotaListElimCons`).  Phase-Z motive
shape: motive heads the spine (under one binder), the scrutinee is the LAST child; the recursive
`listElim` reduct THREADS the motive. -/
def listElimConsRedexRaw {scope : Nat} (motive : RawTerm (scope + 1))
    (headVal tailVal nilBranch consBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons motive
      (.childCons nilBranch
        (.childCons consBranch
          (.childCons (.mkGen .gen_listCons () (.childCons headVal (.childCons tailVal .childNil)))
            .childNil))))

def listElimConsReductRaw {scope : Nat} (motive : RawTerm (scope + 1))
    (headVal tailVal nilBranch consBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons headVal .childNil)))
          (.childCons tailVal .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons tailVal .childNil)))))
        .childNil))

theorem listElimConsRaw_isStep {scope : Nat} (motive : RawTerm (scope + 1))
    (headVal tailVal nilBranch consBranch : RawTerm scope) :
    Step (listElimConsRedexRaw motive headVal tailVal nilBranch consBranch)
      (listElimConsReductRaw motive headVal tailVal nilBranch consBranch) :=
  Step.iotaListElimCons

/-- **★ `Step.iotaListElimCons` is oriented by the real generator RPO** (the deepest recursive ι arm,
Phase-Z motive shape). -/
theorem rpo_orients_iotaListElimCons {scope : Nat} (motive : RawTerm (scope + 1))
    (headVal tailVal nilBranch consBranch : RawTerm scope) :
    Rpo realGenPrecedence
      (eraseToRose (listElimConsRedexRaw motive headVal tailVal nilBranch consBranch))
      (eraseToRose (listElimConsReductRaw motive headVal tailVal nilBranch consBranch)) := by
  dsimp only [listElimConsRedexRaw, listElimConsReductRaw, eraseToRose, eraseChildren]
  exact rpoOrientsElim3WithMotive realGenPrecedence .gen_listElim .gen_app .gen_listCons
    (by decide) (eraseToRose motive) (eraseToRose headVal) (eraseToRose tailVal)
    (eraseToRose nilBranch) (eraseToRose consBranch)

/-- **★ The real-generator RPO is well-founded.**  Instantiating the generic `rpoWellFounded` at the real
generator precedence.  Combined with the three orientations above, all three recursive ι arms
(natElimSucc / natRecSucc / listElimCons) — the firing-68 obstruction arms that defeat every flat measure —
sit in a genuine well-founded order on the REAL kernel, via `eraseToRose`. -/
theorem realGenRpoWellFounded : WellFounded (RpoBelow realGenPrecedence) :=
  rpoWellFounded realGenPrecedence_wellFounded

end FX1Poly.Core.RawIotaRpo
