import FX1Poly.Tier0.Syntax.RawTermWeaken

/-! # Foundation/PolyCell/Core/EtaSources — raw eta-redex source shapes

The five raw-syntax SHAPES whose head a raw eta contraction matches:
`etaLamSource`, `etaPairSource`, `etaPathLamSource`, `etaModIntroSource`,
`etaGlueIntroSource`.  Each is a `@[reducible]` term-former skeleton —
no proof content — built from `RawTerm.weaken` and `RawTerm.newestVar`
(both in `RawTermWeaken`) plus bare generator constructors.

These shapes are shared substrate, NOT bespoke-relation content: they
are referenced by the bespoke `Step.eta` inductive (`StepEta`), by the
table eta relation (`etaRuleTable` / `StepEtaOverTable`), and by the
raw-shape-stated eta subject-reduction arms (`preservedByEtaLam` et al.).
Housing them here — in a file that imports only `RawTermWeaken` — lets
each of those consumers depend on the SHAPES without depending on the
bespoke `Step.eta` inductive.  (Relocated out of `StepEta` so the
shape-stated SR arms can move to a bespoke-import-free home —
TABLE-CANON-ETA re-base.)

Zero-axiom: every declaration is a `@[reducible] def` with no tactic
content.  Per-declaration audit-gated via the substrate sweeps. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

namespace RawTerm

/-- Raw eta source for functions:
`lam domainAnn (app (weaken f) newestVar)`.  Church-style: the lambda
carries a domain annotation; eta contraction discards it. -/
@[reducible] def etaLamSource {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_lam ()
    (.childCons domainAnn
      (.childCons
        (.mkGen .gen_app ()
          (.childCons
            (RawTerm.weaken innerFunction)
            (.childCons RawTerm.newestVar .childNil)))
        .childNil))

/-- Raw eta source for pairs:
`pair (fst p) (snd p)`. -/
@[reducible] def etaPairSource {scope : Nat}
    (pairTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_pair ()
    (.childCons
      (.mkGen .gen_fst () (.childCons pairTerm .childNil))
      (.childCons
        (.mkGen .gen_snd () (.childCons pairTerm .childNil))
        .childNil))

/-- Raw eta source for cubical paths:
`pathLam (pathApp (weaken p) newestVar)`.  The current raw substrate
uses `gen_var` for the bound interval slot; the typed cubical layer
interprets that slot as an interval variable. -/
@[reducible] def etaPathLamSource {scope : Nat}
    (innerPath : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_pathLam ()
    (.childCons
      (.mkGen .gen_pathApp ()
        (.childCons
          (RawTerm.weaken innerPath)
          (.childCons RawTerm.newestVar .childNil)))
      .childNil)

/-- Raw eta source for modal introduction/elimination:
`modIntro (modElim m)`.  Profile-level admissibility decides which
modalities may consume this eta rule downstream. -/
@[reducible] def etaModIntroSource {scope : Nat}
    (modalTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_modIntro ()
    (.childCons
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil))
      .childNil)

/-- Raw eta source for cubical Glue:
`glueIntro (glueElim g) g`.  The second child records the same glued
term so the rule is syntactically by-construction; CCHM coherence
side conditions remain profile-layer obligations. -/
@[reducible] def etaGlueIntroSource {scope : Nat}
    (gluedTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_glueIntro ()
    (.childCons
      (.mkGen .gen_glueElim () (.childCons gluedTerm .childNil))
      (.childCons gluedTerm .childNil))

end RawTerm

end FX1Poly.Core
