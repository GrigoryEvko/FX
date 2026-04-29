import LeanFX.Syntax.Reduction.Congruence.NatConv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Natural-number Conv congruences end here.

The list-side congruences (Step / StepStar / Conv on listCons / listElim)
mirror the natElim layout but with `elementType` as an extra parametric
implicit. -/

/-- Multi-step reduction threads through `listCons`'s head. -/
theorem StepStar.listCons_cong_head {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    (tl : Term ctx (Ty.list elementType)) :
    StepStar hd₁ hd₂ →
    StepStar (Term.listCons hd₁ tl) (Term.listCons hd₂ tl)
  :=
    StepStar.mapStep
      (fun head => Term.listCons head tl)
      (fun singleStep => Step.listConsHead singleStep)

/-- Multi-step reduction threads through `listCons`'s tail. -/
theorem StepStar.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} :
    StepStar tl₁ tl₂ →
    StepStar (Term.listCons hd tl₁) (Term.listCons hd tl₂)
  :=
    StepStar.mapStep
      (fun tail => Term.listCons hd tail)
      (fun singleStep => Step.listConsTail singleStep)

/-- Multi-step reduction threads through both head and tail of `listCons`. -/
theorem StepStar.listCons_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    {tl₁ tl₂ : Term ctx (Ty.list elementType)}
    (h_hd : StepStar hd₁ hd₂) (h_tl : StepStar tl₁ tl₂) :
    StepStar (Term.listCons hd₁ tl₁) (Term.listCons hd₂ tl₂) :=
  StepStar.trans (StepStar.listCons_cong_head tl₁ h_hd)
                 (StepStar.listCons_cong_tail hd₂ h_tl)

/-- Multi-step reduction threads through `listElim`'s scrutinee. -/
theorem StepStar.listElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.listElim scrutinee₁ nilBranch consBranch)
             (Term.listElim scrutinee₂ nilBranch consBranch)
  :=
    StepStar.mapStep
      (fun scrutinee => Term.listElim scrutinee nilBranch consBranch)
      (fun singleStep => Step.listElimScrutinee singleStep)

/-- Multi-step reduction threads through `listElim`'s nil-branch. -/
theorem StepStar.listElim_cong_nil
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    StepStar nilBranch₁ nilBranch₂ →
    StepStar (Term.listElim scrutinee nilBranch₁ consBranch)
             (Term.listElim scrutinee nilBranch₂ consBranch)
  :=
    StepStar.mapStep
      (fun nilBranch => Term.listElim scrutinee nilBranch consBranch)
      (fun singleStep => Step.listElimNil singleStep)

/-- Multi-step reduction threads through `listElim`'s cons-branch. -/
theorem StepStar.listElim_cong_cons
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))} :
    StepStar consBranch₁ consBranch₂ →
    StepStar (Term.listElim scrutinee nilBranch consBranch₁)
             (Term.listElim scrutinee nilBranch consBranch₂)
  :=
    StepStar.mapStep
      (fun consBranch => Term.listElim scrutinee nilBranch consBranch)
      (fun singleStep => Step.listElimCons singleStep)

/-- Multi-step reduction threads through all three `listElim` positions. -/
theorem StepStar.listElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_nil : StepStar nilBranch₁ nilBranch₂)
    (h_cons : StepStar consBranch₁ consBranch₂) :
    StepStar (Term.listElim scrutinee₁ nilBranch₁ consBranch₁)
             (Term.listElim scrutinee₂ nilBranch₂ consBranch₂) :=
  StepStar.trans
    (StepStar.listElim_cong_scrutinee nilBranch₁ consBranch₁ h_scr)
    (StepStar.trans
      (StepStar.listElim_cong_nil scrutinee₂ consBranch₁ h_nil)
      (StepStar.listElim_cong_cons scrutinee₂ nilBranch₂ h_cons))

/-- Definitional equivalence threads through `listCons`'s head. -/
theorem Conv.listCons_cong_head {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    (tl : Term ctx (Ty.list elementType)) (h : Conv hd₁ hd₂) :
    Conv (Term.listCons hd₁ tl) (Term.listCons hd₂ tl) :=
  Conv.mapStep
    (fun head => Term.listCons head tl)
    (fun singleStep => Step.listConsHead singleStep)
    h

/-- Definitional equivalence threads through `listCons`'s tail. -/
theorem Conv.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} (h : Conv tl₁ tl₂) :
    Conv (Term.listCons hd tl₁) (Term.listCons hd tl₂) :=
  Conv.mapStep
    (fun tail => Term.listCons hd tail)
    (fun singleStep => Step.listConsTail singleStep)
    h

/-- Definitional equivalence threads through both `listCons` positions. -/
theorem Conv.listCons_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    {tl₁ tl₂ : Term ctx (Ty.list elementType)}
    (h_hd : Conv hd₁ hd₂) (h_tl : Conv tl₁ tl₂) :
    Conv (Term.listCons hd₁ tl₁) (Term.listCons hd₂ tl₂) :=
  Conv.trans (Conv.listCons_cong_head tl₁ h_hd)
             (Conv.listCons_cong_tail hd₂ h_tl)

/-- Definitional equivalence threads through `listElim`'s scrutinee. -/
theorem Conv.listElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.listElim scrutinee₁ nilBranch consBranch)
         (Term.listElim scrutinee₂ nilBranch consBranch) :=
  Conv.mapStep
    (fun scrutinee => Term.listElim scrutinee nilBranch consBranch)
    (fun singleStep => Step.listElimScrutinee singleStep)
    h

/-- Definitional equivalence threads through `listElim`'s nil-branch. -/
theorem Conv.listElim_cong_nil
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (h : Conv nilBranch₁ nilBranch₂) :
    Conv (Term.listElim scrutinee nilBranch₁ consBranch)
         (Term.listElim scrutinee nilBranch₂ consBranch) :=
  Conv.mapStep
    (fun nilBranch => Term.listElim scrutinee nilBranch consBranch)
    (fun singleStep => Step.listElimNil singleStep)
    h

/-- Definitional equivalence threads through `listElim`'s cons-branch. -/
theorem Conv.listElim_cong_cons
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h : Conv consBranch₁ consBranch₂) :
    Conv (Term.listElim scrutinee nilBranch consBranch₁)
         (Term.listElim scrutinee nilBranch consBranch₂) :=
  Conv.mapStep
    (fun consBranch => Term.listElim scrutinee nilBranch consBranch)
    (fun singleStep => Step.listElimCons singleStep)
    h

/-- Definitional equivalence threads through all three `listElim` positions. -/
theorem Conv.listElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_nil : Conv nilBranch₁ nilBranch₂)
    (h_cons : Conv consBranch₁ consBranch₂) :
    Conv (Term.listElim scrutinee₁ nilBranch₁ consBranch₁)
         (Term.listElim scrutinee₂ nilBranch₂ consBranch₂) :=
  Conv.trans
    (Conv.listElim_cong_scrutinee nilBranch₁ consBranch₁ h_scr)
    (Conv.trans
      (Conv.listElim_cong_nil scrutinee₂ consBranch₁ h_nil)
      (Conv.listElim_cong_cons scrutinee₂ nilBranch₂ h_cons))


end LeanFX.Syntax
