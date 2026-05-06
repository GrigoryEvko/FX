import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census
import LeanFX2.Tools.StrictHarness.DeclShape
import LeanFX2.Tools.StrictHarness.AxiomAdjacent
import LeanFX2.Tools.StrictHarness.TrustEscape

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Lean meta-level Expr manipulation gate

Production-tier kernel decls should not depend on `Lean.Expr`,
`Lean.MVarId`, `Lean.Syntax`, `Lean.Name`, or other metaprogramming
data structures.  These are for tactic mode and elaboration; their
appearance in a kernel theorem signals that the theorem is reasoning
about Lean syntax rather than mathematical content.
-/

def isLeanMetaExprName (someName : Name) : Bool :=
  someName == `Lean.Expr ||
    someName == `Lean.Expr.app ||
    someName == `Lean.Expr.lam ||
    someName == `Lean.Expr.forallE ||
    someName == `Lean.Expr.const ||
    someName == `Lean.Expr.fvar ||
    someName == `Lean.Expr.bvar ||
    someName == `Lean.Expr.mvar ||
    someName == `Lean.MVarId ||
    someName == `Lean.LMVarId ||
    someName == `Lean.Syntax ||
    someName == `Lean.Name ||
    someName == `Lean.Level ||
    someName == `Lean.LocalContext ||
    someName == `Lean.MetavarContext ||
    someName == `Lean.Environment ||
    someName == `Lean.ConstantInfo

def collectLeanMetaExprDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun metaDependencies dependencyName =>
      if isLeanMetaExprName dependencyName then
        metaDependencies.push dependencyName
      else
        metaDependencies)

elab "#assert_lean_meta_expr_dependent_budget " namespaceSyntax:ident
    metaExprBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let metaExprBudget := metaExprBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectLeanMetaExprDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= metaExprBudget then
    logInfo
      (s!"Lean meta-Expr dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{metaExprBudget} kernel decls reference " ++
      "Lean.Expr / MVarId / Syntax / Name / Level)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Lean meta-Expr dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {metaExprBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Monadic-stack dependent gate

Production kernel decls should not depend on monad transformers
(`StateRefT`, `ReaderT`, `StateT`, `ExceptT`, `OptionT`).  These are
for elaboration / tactic infrastructure.  In a kernel theorem they
indicate stateful reasoning that's not first-class mathematics.
-/

def isMonadicStackName (someName : Name) : Bool :=
  someName == `StateT ||
    someName == `StateRefT ||
    someName == `ReaderT ||
    someName == `ExceptT ||
    someName == `OptionT ||
    someName == `WriterT ||
    someName == `Lean.CoreM ||
    someName == `Lean.MetaM ||
    someName == `Lean.Elab.TermElabM ||
    someName == `Lean.Elab.Term.TermElabM ||
    someName == `Lean.Elab.Tactic.TacticM ||
    someName == `Lean.Elab.Command.CommandElabM

def collectMonadicStackDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun monadDependencies dependencyName =>
      if isMonadicStackName dependencyName then
        monadDependencies.push dependencyName
      else
        monadDependencies)

elab "#assert_monadic_stack_dependent_budget " namespaceSyntax:ident
    monadBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let monadBudget := monadBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectMonadicStackDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= monadBudget then
    logInfo
      (s!"Monadic-stack dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{monadBudget} kernel decls reference " ++
      "StateRefT / ReaderT / CoreM / MetaM / etc.)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Monadic-stack dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {monadBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Heavyweight-tactic dependent gate

Beyond `decide`, several tactics introduce heavy reasoning machinery:
`omega`, `linarith`, `nlinarith`, `polyrith`, `aesop`, `tauto`,
`exact?`, `apply?`, `simp_all`, `simp_rw`.  These can prove false
from inconsistent hypotheses or hide structural reasoning.  Pin
current count.
-/

def isHeavyweightTacticName (someName : Name) : Bool :=
  someName == `Mathlib.Tactic.omega ||
    someName == `Lean.Elab.Tactic.Omega.evalOmega ||
    someName == `Lean.Elab.Tactic.evalAesop ||
    someName == `Aesop ||
    someName == `Lean.Elab.Tactic.evalLinarith ||
    someName == `Mathlib.Tactic.linarith ||
    someName == `Mathlib.Tactic.polyrith ||
    someName == `Lean.Elab.Tactic.evalSimpAll ||
    someName == `Lean.Parser.Tactic.simpAll ||
    someName == `Lean.Elab.Tactic.evalDecide ||
    someName == `Lean.Parser.Tactic.tacticDecide_ ||
    someName == `Lean.Elab.Tactic.evalTautology

def collectHeavyweightTacticDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun tacticDependencies dependencyName =>
      if isHeavyweightTacticName dependencyName then
        tacticDependencies.push dependencyName
      else
        tacticDependencies)

elab "#assert_heavyweight_tactic_dependent_budget " namespaceSyntax:ident
    tacticBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let tacticBudget := tacticBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectHeavyweightTacticDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= tacticBudget then
    logInfo
      (s!"Heavyweight-tactic dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{tacticBudget} kernel decls reference " ++
      "omega / aesop / linarith / tauto / simp_all)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Heavyweight-tactic dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {tacticBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Term ctor → Smoke namespace usage parity

Every Term constructor should be referenced by at least one declaration
in `LeanFX2.Smoke.*` — without smoke usage, the ctor is silently
unverified by the regression suite.  This gate scans for the existence
of any decl in the Smoke namespace whose body mentions the Term ctor's
constant by name.
-/

/-- Whether a declaration belongs to the smoke/audit cone.  Some older smoke
files use namespaces such as `LeanFX2.SmokePhase9DCheck` instead of living
under `LeanFX2.Smoke.*`, so this deliberately accepts any `LeanFX2.Smoke...`
prefix. -/
def isSmokeAuditDeclName (declName : Name) : Bool :=
  (toString declName).startsWith "LeanFX2.Smoke"

/-- Whether any decl in the LeanFX2.Smoke.* namespace mentions the
given Term constructor.  Heuristic: walk every smoke decl's type and
value Expr looking for a const reference.  Checking types matters for
smoke declarations whose body is just `rfl` but whose theorem statement
mentions the constructor being audited. -/
def hasAnySmokeReference
    (environment : Environment) (constructorName : Name) : Bool :=
  let smokeMatches :=
    environment.constants.toList.filter fun (declName, _) =>
      isSmokeAuditDeclName declName
  smokeMatches.any fun (_, constantInfo) =>
    doesExprMentionConst constructorName constantInfo.type ||
      match constantInfo.value? with
      | some bodyExpr => doesExprMentionConst constructorName bodyExpr
      | none => false

/-- Term ctors lacking any reference from the Smoke namespace. -/
def smokeReferenceDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array Name :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array Name))
    (fun records constructorName =>
      if hasAnySmokeReference environment constructorName then
        records
      else
        records.push constructorName)

elab "#assert_smoke_reference_coverage_budget " inductiveSyntax:ident
    smokeRefBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let smokeRefBudget := smokeRefBudgetSyntax.getNat
  let unreferencedCtors :=
    smokeReferenceDebtRecordsForInductive environment inductiveName
  let totalCtors :=
    (getInductiveConstructorNames environment inductiveName).size
  let referencedCtors :=
    if totalCtors >= unreferencedCtors.size then
      totalCtors - unreferencedCtors.size
    else 0
  if unreferencedCtors.size <= smokeRefBudget then
    logInfo
      (s!"smoke reference coverage budget ok: {inductiveName} " ++
      s!"({referencedCtors}/{totalCtors} ctors referenced from Smoke; " ++
      s!"unreferenced {unreferencedCtors.size}/{smokeRefBudget})")
  else
    let perCtorLines := unreferencedCtors.toList.take 20 |>.map fun ctorName =>
      s!"  - {ctorName}"
    let header :=
      s!"smoke reference coverage budget FAILED for {inductiveName}: " ++
      s!"{unreferencedCtors.size} ctors lack Smoke reference, " ++
      s!"exceeds budget {smokeRefBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## absurd / False.elim direct dependent gate

`absurd : a → ¬a → b` and `False.elim : False → C` discharge
contradictions.  Heavy use signals proofs that thread through
contradictory hypotheses — usually fine but worth tracking.  The
distinguishing concern: `absurd` / `False.elim` on a hypothesis that
might itself be vacuous can mask issues.
-/

def isAbsurdFalseFamilyName (someName : Name) : Bool :=
  someName == `absurd ||
    someName == `False.elim ||
    someName == `False.rec ||
    someName == `False.recOn ||
    someName == `False.casesOn

def collectAbsurdFalseDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun absurdDependencies dependencyName =>
      if isAbsurdFalseFamilyName dependencyName then
        absurdDependencies.push dependencyName
      else
        absurdDependencies)

elab "#assert_absurd_false_dependent_budget " namespaceSyntax:ident
    absurdBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let absurdBudget := absurdBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectAbsurdFalseDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= absurdBudget then
    logInfo
      (s!"absurd / False.elim dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{absurdBudget} kernel decls reference " ++
      "absurd / False.elim / False.rec)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"absurd / False.elim dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {absurdBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## `Setoid` / `Quotient` / `Quot` extended dependent gate

Beyond the existing Quot family gate, this widens to `Setoid`
(equivalence-relation typeclass) and the `Quotient` API on top of
`Setoid`.  These let users build quotient types beyond the kernel
primitive `Quot`; uses signal classical-style mathematical reasoning.
-/

def isSetoidQuotientFamilyName (someName : Name) : Bool :=
  someName == `Setoid ||
    someName == `Setoid.r ||
    someName == `Setoid.refl ||
    someName == `Setoid.symm ||
    someName == `Setoid.trans ||
    someName == `Setoid.iseqv ||
    someName == `Quotient.mk' ||
    someName == `Quotient.lift' ||
    someName == `Quotient.exact ||
    someName == `Quotient.sound

def collectSetoidQuotientDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun setoidDependencies dependencyName =>
      if isSetoidQuotientFamilyName dependencyName then
        setoidDependencies.push dependencyName
      else
        setoidDependencies)

elab "#assert_setoid_quotient_dependent_budget " namespaceSyntax:ident
    setoidBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let setoidBudget := setoidBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectSetoidQuotientDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= setoidBudget then
    logInfo
      (s!"Setoid / Quotient dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{setoidBudget} kernel decls reference " ++
      "Setoid / Quotient.mk' / Quotient.sound)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Setoid / Quotient dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {setoidBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)


end LeanFX2.Tools
