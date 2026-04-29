import LeanFX.Syntax.Reduction.Conv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-- Append a single step to an existing multi-step path — companion
to `StepStar.step` (which prepends).  Both directions are useful for
trace manipulation in conversion algorithms. -/
theorem StepStar.append
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-! ## Boolean reduction congruences.

Multi-step and definitional-equivalence threading through `boolElim`'s
three positions, plus combined three-position congruences. -/

/-- Multi-step reduction threads through `boolElim`'s scrutinee. -/
theorem StepStar.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.boolElim scrutinee₁ thenBr elseBr)
             (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimScrutinee s)
        (StepStar.boolElim_cong_scrutinee thenBr elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s then-branch. -/
theorem StepStar.boolElim_cong_then
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    StepStar thenBr₁ thenBr₂ →
    StepStar (Term.boolElim scrutinee thenBr₁ elseBr)
             (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimThen s)
        (StepStar.boolElim_cong_then scrutinee elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s else-branch. -/
theorem StepStar.boolElim_cong_else
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    StepStar elseBr₁ elseBr₂ →
    StepStar (Term.boolElim scrutinee thenBr elseBr₁)
             (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimElse s)
        (StepStar.boolElim_cong_else scrutinee thenBr rest)

/-- Multi-step reduction threads through all three `boolElim`
positions simultaneously.  Sequenced via three `trans` calls over
the single-position congruences. -/
theorem StepStar.boolElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_then : StepStar thenBr₁ thenBr₂)
    (h_else : StepStar elseBr₁ elseBr₂) :
    StepStar (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
             (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  StepStar.trans
    (StepStar.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (StepStar.trans
      (StepStar.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (StepStar.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-- Definitional equivalence threads through `boolElim`'s scrutinee. -/
theorem Conv.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    Conv scrutinee₁ scrutinee₂ →
    Conv (Term.boolElim scrutinee₁ thenBr elseBr)
         (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_scrutinee thenBr elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₁)
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimScrutinee s)

/-- Definitional equivalence threads through `boolElim`'s then-branch. -/
theorem Conv.boolElim_cong_then
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    Conv thenBr₁ thenBr₂ →
    Conv (Term.boolElim scrutinee thenBr₁ elseBr)
         (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_then scrutinee elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_then scrutinee elseBr h₁)
        (Conv.boolElim_cong_then scrutinee elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimThen s)

/-- Definitional equivalence threads through `boolElim`'s else-branch. -/
theorem Conv.boolElim_cong_else
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    Conv elseBr₁ elseBr₂ →
    Conv (Term.boolElim scrutinee thenBr elseBr₁)
         (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_else scrutinee thenBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_else scrutinee thenBr h₁)
        (Conv.boolElim_cong_else scrutinee thenBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimElse s)

/-- Definitional equivalence threads through all three `boolElim`
positions simultaneously. -/
theorem Conv.boolElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_then : Conv thenBr₁ thenBr₂)
    (h_else : Conv elseBr₁ elseBr₂) :
    Conv (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
         (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  Conv.trans
    (Conv.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (Conv.trans
      (Conv.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (Conv.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-! ## Natural-number reduction congruences.

Multi-step and definitional-equivalence threading through `Term.natSucc`
and `Term.natElim`'s three positions, mirroring the boolean section. -/

/-- Definitional equivalence threads through `Term.natSucc`. -/
theorem Conv.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat}
    (h : Conv pred₁ pred₂) :
    Conv (Term.natSucc pred₁) (Term.natSucc pred₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natSuccPred s)

/-- Definitional equivalence threads through `natElim`'s scrutinee. -/
theorem Conv.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch succBranch)
         (Term.natElim scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimScrutinee s)

/-- Definitional equivalence threads through `natElim`'s zero-branch. -/
theorem Conv.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch₁ succBranch)
         (Term.natElim scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimZero s)

/-- Definitional equivalence threads through `natElim`'s succ-branch. -/
theorem Conv.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch succBranch₁)
         (Term.natElim scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimSucc s)

/-- Definitional equivalence threads through all three `natElim` positions. -/
theorem Conv.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec Conv congruences (parallel to natElim, with the richer
succBranch type `Ty.arrow Ty.nat (Ty.arrow resultType resultType)`). -/

/-- Definitional equivalence threads through `natRec`'s scrutinee. -/
theorem Conv.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch succBranch)
         (Term.natRec scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecScrutinee s)

/-- Definitional equivalence threads through `natRec`'s zero-branch. -/
theorem Conv.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch₁ succBranch)
         (Term.natRec scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecZero s)

/-- Definitional equivalence threads through `natRec`'s succ-branch. -/
theorem Conv.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch succBranch₁)
         (Term.natRec scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecSucc s)

/-- Definitional equivalence threads through all three `natRec` positions. -/
theorem Conv.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))

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
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listConsHead s)
        (StepStar.listCons_cong_head tl rest)

/-- Multi-step reduction threads through `listCons`'s tail. -/
theorem StepStar.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} :
    StepStar tl₁ tl₂ →
    StepStar (Term.listCons hd tl₁) (Term.listCons hd tl₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listConsTail s)
        (StepStar.listCons_cong_tail hd rest)

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
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimScrutinee s)
        (StepStar.listElim_cong_scrutinee nilBranch consBranch rest)

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
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimNil s)
        (StepStar.listElim_cong_nil scrutinee consBranch rest)

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
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimCons s)
        (StepStar.listElim_cong_cons scrutinee nilBranch rest)

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
    Conv (Term.listCons hd₁ tl) (Term.listCons hd₂ tl) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listConsHead s)

/-- Definitional equivalence threads through `listCons`'s tail. -/
theorem Conv.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} (h : Conv tl₁ tl₂) :
    Conv (Term.listCons hd tl₁) (Term.listCons hd tl₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listConsTail s)

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
         (Term.listElim scrutinee₂ nilBranch consBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimScrutinee s)

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
         (Term.listElim scrutinee nilBranch₂ consBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimNil s)

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
         (Term.listElim scrutinee nilBranch consBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimCons s)

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

/-! ## Option Conv congruences (mirror the list versions). -/

/-- Definitional equivalence threads through `Term.optionSome`'s value. -/
theorem Conv.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} (h : Conv value₁ value₂) :
    Conv (Term.optionSome value₁) (Term.optionSome value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionSomeValue s)

/-- Definitional equivalence threads through `optionMatch`'s scrutinee. -/
theorem Conv.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch someBranch)
         (Term.optionMatch scrutinee₂ noneBranch someBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchScrutinee s)

/-- Definitional equivalence threads through `optionMatch`'s none-branch. -/
theorem Conv.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv noneBranch₁ noneBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch₁ someBranch)
         (Term.optionMatch scrutinee noneBranch₂ someBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchNone s)

/-- Definitional equivalence threads through `optionMatch`'s some-branch. -/
theorem Conv.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch someBranch₁)
         (Term.optionMatch scrutinee noneBranch someBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchSome s)

/-- Definitional equivalence threads through all three `optionMatch` positions. -/
theorem Conv.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_none : Conv noneBranch₁ noneBranch₂)
    (h_some : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
         (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  Conv.trans
    (Conv.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (Conv.trans
      (Conv.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (Conv.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))

/-! ## Either Conv congruences (mirror the option versions). -/

/-- Definitional equivalence threads through `Term.eitherInl`'s value. -/
theorem Conv.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInl (rightType := rightType) value₁)
         (Term.eitherInl (rightType := rightType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInlValue s)

/-- Definitional equivalence threads through `Term.eitherInr`'s value. -/
theorem Conv.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInr (leftType := leftType) value₁)
         (Term.eitherInr (leftType := leftType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInrValue s)

/-- Definitional equivalence threads through `eitherMatch`'s scrutinee. -/
theorem Conv.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
         (Term.eitherMatch scrutinee₂ leftBranch rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchScrutinee s)

/-- Definitional equivalence threads through `eitherMatch`'s left-branch. -/
theorem Conv.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv leftBranch₁ leftBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
         (Term.eitherMatch scrutinee leftBranch₂ rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchLeft s)

/-- Definitional equivalence threads through `eitherMatch`'s right-branch. -/
theorem Conv.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch rightBranch₁)
         (Term.eitherMatch scrutinee leftBranch rightBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchRight s)

/-- Definitional equivalence threads through all three `eitherMatch` positions. -/
theorem Conv.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_left : Conv leftBranch₁ leftBranch₂)
    (h_right : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
         (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  Conv.trans
    (Conv.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (Conv.trans
      (Conv.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (Conv.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))

/-! ## idJ Conv congruences. -/

/-- Definitional equivalence threads through `Term.idJ`'s baseCase. -/
theorem Conv.idJ_cong_base {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd))
    (h : Conv baseCase₁ baseCase₂) :
    Conv (Term.idJ baseCase₁ witness) (Term.idJ baseCase₂ witness) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.idJBase s)

/-- Definitional equivalence threads through `Term.idJ`'s witness. -/
theorem Conv.idJ_cong_witness {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h : Conv witness₁ witness₂) :
    Conv (Term.idJ baseCase witness₁) (Term.idJ baseCase witness₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.idJWitness baseCase s)

/-- Definitional equivalence threads through both `Term.idJ` positions. -/
theorem Conv.idJ_cong {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h_base : Conv baseCase₁ baseCase₂)
    (h_witness : Conv witness₁ witness₂) :
    Conv (Term.idJ baseCase₁ witness₁) (Term.idJ baseCase₂ witness₂) :=
  Conv.trans
    (Conv.idJ_cong_base witness₁ h_base)
    (Conv.idJ_cong_witness baseCase₂ h_witness)

/-! ## StepStar congruences for nat (defined above the Conv versions
because Step.par.toStar consumes them). -/

/-- Multi-step reduction threads through `Term.natSucc`. -/
theorem StepStar.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat} :
    StepStar pred₁ pred₂ →
    StepStar (Term.natSucc pred₁) (Term.natSucc pred₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natSuccPred s)
        (StepStar.natSucc_cong rest)

/-- Multi-step reduction threads through `natElim`'s scrutinee. -/
theorem StepStar.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natElim scrutinee₁ zeroBranch succBranch)
             (Term.natElim scrutinee₂ zeroBranch succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimScrutinee s)
        (StepStar.natElim_cong_scrutinee zeroBranch succBranch rest)

/-- Multi-step reduction threads through `natElim`'s zero-branch. -/
theorem StepStar.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch₁ succBranch)
             (Term.natElim scrutinee zeroBranch₂ succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimZero s)
        (StepStar.natElim_cong_zero scrutinee succBranch rest)

/-- Multi-step reduction threads through `natElim`'s succ-branch. -/
theorem StepStar.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch succBranch₁)
             (Term.natElim scrutinee zeroBranch succBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimSucc s)
        (StepStar.natElim_cong_succ scrutinee zeroBranch rest)

/-- Multi-step reduction threads through all three `natElim` positions. -/
theorem StepStar.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec StepStar congruences (placed before Step.par.toStar
which consumes them, parallel to natElim). -/

/-- Multi-step reduction threads through `natRec`'s scrutinee. -/
theorem StepStar.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natRec scrutinee₁ zeroBranch succBranch)
             (Term.natRec scrutinee₂ zeroBranch succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecScrutinee s)
        (StepStar.natRec_cong_scrutinee zeroBranch succBranch rest)

/-- Multi-step reduction threads through `natRec`'s zero-branch. -/
theorem StepStar.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch₁ succBranch)
             (Term.natRec scrutinee zeroBranch₂ succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecZero s)
        (StepStar.natRec_cong_zero scrutinee succBranch rest)

/-- Multi-step reduction threads through `natRec`'s succ-branch. -/
theorem StepStar.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch succBranch₁)
             (Term.natRec scrutinee zeroBranch succBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecSucc s)
        (StepStar.natRec_cong_succ scrutinee zeroBranch rest)

/-- Multi-step reduction threads through all three `natRec` positions. -/
theorem StepStar.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## Option StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.optionSome`. -/
theorem StepStar.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} :
    StepStar value₁ value₂ →
    StepStar (Term.optionSome value₁) (Term.optionSome value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionSomeValue s)
        (StepStar.optionSome_cong rest)

/-- Multi-step reduction threads through `optionMatch`'s scrutinee. -/
theorem StepStar.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.optionMatch scrutinee₁ noneBranch someBranch)
             (Term.optionMatch scrutinee₂ noneBranch someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchScrutinee s)
        (StepStar.optionMatch_cong_scrutinee noneBranch someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s none-branch. -/
theorem StepStar.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar noneBranch₁ noneBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch₁ someBranch)
             (Term.optionMatch scrutinee noneBranch₂ someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchNone s)
        (StepStar.optionMatch_cong_none scrutinee someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s some-branch. -/
theorem StepStar.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)} :
    StepStar someBranch₁ someBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch someBranch₁)
             (Term.optionMatch scrutinee noneBranch someBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchSome s)
        (StepStar.optionMatch_cong_some scrutinee noneBranch rest)

/-- Multi-step reduction threads through all three `optionMatch` positions. -/
theorem StepStar.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_none : StepStar noneBranch₁ noneBranch₂)
    (h_some : StepStar someBranch₁ someBranch₂) :
    StepStar (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
             (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  StepStar.trans
    (StepStar.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (StepStar.trans
      (StepStar.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (StepStar.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))

/-! ## Either StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.eitherInl`. -/
theorem StepStar.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInl (rightType := rightType) value₁)
             (Term.eitherInl (rightType := rightType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInlValue s)
        (StepStar.eitherInl_cong rest)

/-- Multi-step reduction threads through `Term.eitherInr`. -/
theorem StepStar.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInr (leftType := leftType) value₁)
             (Term.eitherInr (leftType := leftType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInrValue s)
        (StepStar.eitherInr_cong rest)

/-- Multi-step reduction threads through `eitherMatch`'s scrutinee. -/
theorem StepStar.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
             (Term.eitherMatch scrutinee₂ leftBranch rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchScrutinee s)
        (StepStar.eitherMatch_cong_scrutinee leftBranch rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s left-branch. -/
theorem StepStar.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar leftBranch₁ leftBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
             (Term.eitherMatch scrutinee leftBranch₂ rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchLeft s)
        (StepStar.eitherMatch_cong_left scrutinee rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s right-branch. -/
theorem StepStar.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)} :
    StepStar rightBranch₁ rightBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch rightBranch₁)
             (Term.eitherMatch scrutinee leftBranch rightBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchRight s)
        (StepStar.eitherMatch_cong_right scrutinee leftBranch rest)

/-- Multi-step reduction threads through all three `eitherMatch` positions. -/
theorem StepStar.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_left : StepStar leftBranch₁ leftBranch₂)
    (h_right : StepStar rightBranch₁ rightBranch₂) :
    StepStar (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
             (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  StepStar.trans
    (StepStar.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (StepStar.trans
      (StepStar.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (StepStar.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))

/-! ## idJ StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.idJ`'s baseCase. -/
theorem StepStar.idJ_cong_base {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd)) :
    StepStar baseCase₁ baseCase₂ →
    StepStar (Term.idJ baseCase₁ witness) (Term.idJ baseCase₂ witness)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.idJBase s)
        (StepStar.idJ_cong_base witness rest)

/-- Multi-step reduction threads through `Term.idJ`'s witness. -/
theorem StepStar.idJ_cong_witness {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)} :
    StepStar witness₁ witness₂ →
    StepStar (Term.idJ baseCase witness₁) (Term.idJ baseCase witness₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.idJWitness baseCase s)
        (StepStar.idJ_cong_witness baseCase rest)

/-- Multi-step reduction threads through both positions of `Term.idJ`. -/
theorem StepStar.idJ_cong {mode level scope} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase₁ baseCase₂ : Term ctx resultType}
    {witness₁ witness₂ : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (h_base : StepStar baseCase₁ baseCase₂)
    (h_witness : StepStar witness₁ witness₂) :
    StepStar (Term.idJ baseCase₁ witness₁) (Term.idJ baseCase₂ witness₂) :=
  StepStar.trans
    (StepStar.idJ_cong_base witness₁ h_base)
    (StepStar.idJ_cong_witness baseCase₂ h_witness)


end LeanFX.Syntax
