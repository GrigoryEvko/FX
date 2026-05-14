import LeanFX2.Reducibility.Kripke.Basic

/-! Kripke arrow-arm projections.

The arrow arm of ReducibleK at step `n+1` is a pair `SN(f) ∧
Kripke-closure`.  This file exposes the SN projection and the
closure-application combinator — the load-bearing operational
interface for the Kripke arrow case. -/

namespace LeanFX2

/-- SN projection from arrow reducibility. -/
theorem ReducibleK.arrow_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {domainType codomainType : Ty level scope}
    {raw : RawTerm scope}
    {functionTerm : Term context (Ty.arrow domainType codomainType) raw}
    (functionIsR :
      @ReducibleK mode level scope context (stepCount + 1)
          (Ty.arrow domainType codomainType) raw functionTerm) :
    Term.isStronglyNormalizing functionTerm :=
  functionIsR.1

/-- Apply the Kripke closure: in any future context, a reducible
argument at the renamed domain gives a reducible application at the
renamed codomain.  The headline operational consequence of arrow
Kripke. -/
theorem ReducibleK.arrow_apply
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {domainType codomainType : Ty level scope}
    {raw : RawTerm scope}
    {functionTerm : Term context (Ty.arrow domainType codomainType) raw}
    (functionIsR :
      @ReducibleK mode level scope context (stepCount + 1)
          (Ty.arrow domainType codomainType) raw functionTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.rename rho) argumentRaw)
    (argumentIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (domainType.rename rho) argumentRaw argumentTerm) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (codomainType.rename rho) _
      (Term.app (Term.rename termRenaming functionTerm) argumentTerm) :=
  functionIsR.2 termRenaming argumentTerm argumentIsR

end LeanFX2
