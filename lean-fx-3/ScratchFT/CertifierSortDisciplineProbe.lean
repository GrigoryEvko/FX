import FX1Poly.Core.CertifiedTerm
import FX1Poly.Typed.CellConstructors

/-! Probe: does the certifier's child-SORT discipline reject grown-TYPED cells?

Suspicion: gen_lam's childSpecs demand a .term domain annotation, but typed lambdas
carry TYPE-CODE annotations (.type-rooted, e.g. universeCodeCell); gen_piTyCode's
childSpecs demand .type children, but typed Pi codes can have VARIABLE (.term-rooted)
domains. If both reject, O-STACK (#1194) as stated is FALSE. -/

namespace FX1Poly.Probe

open FX1Poly.Core FX1Poly.Universe FX1Poly.Typed

/-- λ(A : Type@0). A — lam with a universe-code (.type-rooted) domain annotation. -/
def lamWithUniverseAnnotation : RawTerm 0 :=
  .mkGen .gen_lam ()
    (.childCons (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (.childCons (.mkGen .gen_var ⟨0, by decide⟩ .childNil) .childNil))

/-- Π (x : X). X at scope 1 — Pi code with a VARIABLE (.term-rooted) domain. -/
def piCodeWithVarDomain : RawTerm 1 :=
  piTyCodeCell (.mkGen .gen_var ⟨0, by decide⟩ .childNil)
    (.mkGen .gen_var ⟨1, by decide⟩ .childNil)

/-- A plain term cell for contrast: λ(x : <var>). x is all-.term — should pass. -/
def lamWithVarAnnotation : RawTerm 1 :=
  .mkGen .gen_lam ()
    (.childCons (.mkGen .gen_var ⟨0, by decide⟩ .childNil)
      (.childCons (.mkGen .gen_var ⟨0, by decide⟩ .childNil) .childNil))

#eval match certifyRawCellExact? (profile := fxProfile) 0
        (.termBase lamWithUniverseAnnotation) with
  | .ok _ => "lamWithUniverseAnnotation: CERTIFIED"
  | .error rejection => s!"lamWithUniverseAnnotation: REJECTED"

#eval match certifyRawCellExact? (profile := fxProfile) 1
        (.termBase piCodeWithVarDomain) with
  | .ok _ => "piCodeWithVarDomain: CERTIFIED"
  | .error rejection => s!"piCodeWithVarDomain: REJECTED"

#eval match certifyRawCellExact? (profile := fxProfile) 1
        (.termBase lamWithVarAnnotation) with
  | .ok _ => "lamWithVarAnnotation: CERTIFIED"
  | .error rejection => s!"lamWithVarAnnotation: REJECTED"

end FX1Poly.Probe
