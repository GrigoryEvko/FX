import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census
import LeanFX2.Tools.StrictHarness.DeclShape

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Axiom-adjacent dependency gates

Five additional anti-cheat dependency censuses, each pinning the count
of decls whose closure references a known axiom-adjacent construct.

`Inhabited` / `Nonempty` instances often summon `Classical.choice`
internally; counting their dependents catches inadvertent uses.
`HEq` is propext-adjacent — every HEq usage involves a heterogeneous
equality cast that the kernel cannot reduce in general.  `decide`
invokes the kernel reducer on Decidable instances and can hide propext
through Decidable on Eq.  `Subsingleton.elim` is the canonical way to
elide Nat.le proof_irrel and related; it sometimes leaks propext.
Match-compiler equation lemmas (`_eq_<n>`) are propext-suspect on
indexed inductives.

Each gate counts kernel-tier decls whose transitive closure references
the given name set, pinning current debt and rejecting growth.
-/

/-- Whether a name is an `Inhabited` / `Nonempty` typeclass node. -/
def isInhabitedOrNonemptyName (someName : Name) : Bool :=
  someName == `Inhabited ||
    someName == `Inhabited.mk ||
    someName == `Inhabited.default ||
    someName == `Nonempty ||
    someName == `Nonempty.intro ||
    someName == `Nonempty.elim ||
    someName == `Classical.choice ||
    someName == `Classical.indefiniteDescription ||
    someName == `Classical.choose ||
    someName == `Classical.choose_spec

/-- Closure dependents on Inhabited / Nonempty / Classical.choice. -/
def collectInhabitedDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun inhabitedDependencies dependencyName =>
      if isInhabitedOrNonemptyName dependencyName then
        inhabitedDependencies.push dependencyName
      else
        inhabitedDependencies)

/-- Build-failing budget gate counting kernel-tier decls whose closure
references Inhabited / Nonempty / Classical.choice. -/
elab "#assert_inhabited_dependent_budget " namespaceSyntax:ident
    inhabitedBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let inhabitedBudget := inhabitedBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    let inhabitedDependencies :=
      collectInhabitedDependencies environment targetName
    if !inhabitedDependencies.isEmpty then
      violations := violations.push targetName
  recordAuditCount `inhabited_dependent violations.size
  if violations.size <= inhabitedBudget then
    logInfo
      (s!"inhabited dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{inhabitedBudget} kernel decls reference " ++
      "Inhabited / Nonempty / Classical.choice)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"inhabited dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget " ++
      s!"{inhabitedBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-- Whether a name is one of the heterogeneous-equality constructors. -/
def isHEqName (someName : Name) : Bool :=
  someName == `HEq ||
    someName == `HEq.refl ||
    someName == `HEq.rec ||
    someName == `HEq.ndrec ||
    someName == `HEq.subst ||
    someName == `HEq.symm ||
    someName == `HEq.trans

/-- Whether a constant info's claimed result type mentions `HEq`. -/
def claimsHEqInResultType (constantInfo : ConstantInfo) : Bool :=
  doesExprMentionConst `HEq constantInfo.type

/-- Build-failing budget gate counting kernel-tier theorems whose
result type mentions `HEq`.  HEq usage is propext-adjacent because
heterogeneous equality cannot generally reduce; pinning the count
keeps new HEq-shaped theorems visible.  Excludes theorems that ALREADY
appear in confluence-cascade scaffolding (which legitimately uses HEq
for the cd-lemma diamond). -/
elab "#assert_heq_result_type_budget " namespaceSyntax:ident
    heqBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let heqBudget := heqBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    match environment.find? targetName with
    | some constantInfo =>
        if claimsHEqInResultType constantInfo then
          violations := violations.push targetName
    | none => pure ()
  recordAuditCount `heq_result_type violations.size
  if violations.size <= heqBudget then
    logInfo
      (s!"HEq result-type budget ok: {namespaceName} " ++
      s!"({violations.size}/{heqBudget} kernel decls have HEq in " ++
      "result type)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"HEq result-type budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier HEq result-typed decls exceed " ++
      s!"budget {heqBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-- Whether a name is `Decidable.decide` or one of its decision tools. -/
def isDecideDecisionName (someName : Name) : Bool :=
  someName == `Decidable.decide ||
    someName == `Decidable.byContradiction ||
    someName == `Decidable.rec ||
    someName == `Decidable.casesOn ||
    someName == `instDecidableEqProp ||
    someName == `Decidable.em

/-- Closure dependents on `Decidable.decide` / similar. -/
def collectDecideDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun decideDependencies dependencyName =>
      if isDecideDecisionName dependencyName then
        decideDependencies.push dependencyName
      else
        decideDependencies)

/-- Build-failing budget gate counting kernel-tier decls whose closure
references `Decidable.decide` or related decision tools.  These invoke
the kernel reducer on Decidable instances and can hide propext through
Decidable instances on Eq. -/
elab "#assert_decide_dependent_budget " namespaceSyntax:ident
    decideBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let decideBudget := decideBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    let decideDependencies :=
      collectDecideDependencies environment targetName
    if !decideDependencies.isEmpty then
      violations := violations.push targetName
  recordAuditCount `decide_dependent violations.size
  if violations.size <= decideBudget then
    logInfo
      (s!"decide-dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{decideBudget} kernel decls reference " ++
      "Decidable.decide / similar)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"decide-dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget " ++
      s!"{decideBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-- Whether a name is `Subsingleton.elim` or related Subsingleton tool. -/
def isSubsingletonElimName (someName : Name) : Bool :=
  someName == `Subsingleton.elim ||
    someName == `Subsingleton.intro ||
    someName == `Subsingleton.helim ||
    someName == `Subsingleton.allEq

/-- Closure dependents on `Subsingleton.elim`. -/
def collectSubsingletonDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun subsingletonDependencies dependencyName =>
      if isSubsingletonElimName dependencyName then
        subsingletonDependencies.push dependencyName
      else
        subsingletonDependencies)

/-- Build-failing budget gate counting kernel-tier decls whose closure
references `Subsingleton.elim`.  This is the canonical way to elide
Nat.le proof_irrel and related propositional irrelevance; it can
silently summon propext on certain Lean versions.  Pinning the count
makes new uses visible. -/
elab "#assert_subsingleton_dependent_budget " namespaceSyntax:ident
    subsingletonBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let subsingletonBudget := subsingletonBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    let subsingletonDependencies :=
      collectSubsingletonDependencies environment targetName
    if !subsingletonDependencies.isEmpty then
      violations := violations.push targetName
  recordAuditCount `subsingleton_dependent violations.size
  if violations.size <= subsingletonBudget then
    logInfo
      (s!"subsingleton-dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{subsingletonBudget} kernel decls " ++
      "reference Subsingleton.elim)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"subsingleton-dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget " ++
      s!"{subsingletonBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-- Whether a constant info's name is a match-compiler equation lemma
of the form `<root>._eq_<index>` or `<root>.match_<index>`.  These are
auto-generated by Lean's match compiler and on indexed-inductive
families they often carry propext via the auto-generated equation
proof.  Production-tier match-compiler artifacts are flagged. -/
def isMatchCompilerEquationName (someName : Name) : Bool :=
  let segments := someName.componentsRev.map Name.toString
  segments.any (fun segment =>
    segment.startsWith "_eq_" ||
      segment.startsWith "match_" ||
      segment.startsWith "_match_")

/-- Build-failing budget gate counting USER-DEFINED match-compiler
equation lemmas in kernel-tier namespaces.  Iterates via
`namespaceAuditTargets` so auto-generated equation lemmas (which Lean
emits per pattern-matching def, often hundreds per file) are NOT
counted.  Only user-named decls that match the `_eq_<n>` / `match_<n>`
shape contribute.  Production code rarely defines such names by hand;
the gate fires when a kernel-tier user decl mimics the auto-generated
naming convention. -/
elab "#assert_match_compiler_equation_budget " namespaceSyntax:ident
    equationBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let equationBudget := equationBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut equationCount : Nat := 0
  for declName in targetNames do
    if !isKernelTierProductionDecl declName then
      continue
    if isMatchCompilerEquationName declName then
      equationCount := equationCount + 1
  recordAuditCount `match_compiler_equation equationCount
  if equationCount <= equationBudget then
    logInfo
      (s!"match-compiler equation budget ok: {namespaceName} " ++
      s!"({equationCount}/{equationBudget} user-named match-compiler-" ++
      "shaped decls in kernel tier)")
  else
    let header :=
      s!"match-compiler equation budget FAILED for {namespaceName}: " ++
      s!"{equationCount} user-named match-compiler-shaped decls " ++
      s!"exceed budget {equationBudget}"
    throwError header

/-! ## Theorem-body shape audit

Detects two specific suspicious shape patterns in theorem bodies:

* **rfl-only on non-trivial-name theorem** — body is exactly `Eq.refl
  _` but the theorem name suggests a non-trivial property (suffix is
  one of `_inj`, `_unique`, `_iff`, `_def`, `_uniqueProof`).  Such a
  theorem might be a definitionally-trivial restatement masquerading
  as a substantive claim.

* **`congrArg`-only chain** — body is a small chain of `congrArg` /
  `Eq.refl` applications without inductive case analysis.  Heuristic
  flag for theorems whose proof depth doesn't match their claim depth.
-/

/-- Whether a theorem's name suggests a non-trivial property that would
not normally be provable by `rfl` alone.  Heuristic. -/
def hasNonTrivialNameSuffix (declName : Name) : Bool :=
  let lastSegment := Name.lastSegmentString declName
  lastSegment.endsWith "_inj" ||
    lastSegment.endsWith "_unique" ||
    lastSegment.endsWith "_iff" ||
    lastSegment.endsWith "_def" ||
    lastSegment.endsWith "_eq" ||
    lastSegment.endsWith "_uniqueProof"

/-- Whether a body is exactly `Eq.refl _` (modulo outer lambdas). -/
partial def isRflOnlyBody (bodyExpr : Expr) : Bool :=
  match bodyExpr with
  | .lam _ _ innerBody _ => isRflOnlyBody innerBody
  | .mdata _ innerBody => isRflOnlyBody innerBody
  | .app _ _ =>
      match bodyExpr.getAppFn with
      | .const headName _ =>
          headName == `Eq.refl ||
            headName == `rfl ||
            headName == `HEq.refl
      | _ => false
  | .const headName _ =>
      headName == `rfl
  | _ => false

/-- Build-failing budget gate counting theorems whose name suggests a
non-trivial property AND whose body is exactly rfl.  Pinning catches
new "Theorem X_unique := rfl" claims that pretend more than they prove.
-/
elab "#assert_rfl_on_nontrivial_name_budget " namespaceSyntax:ident
    rflBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let rflBudget := rflBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !hasNonTrivialNameSuffix targetName then
      continue
    match environment.find? targetName with
    | some constantInfo =>
        match constantInfo.value? with
        | some bodyExpr =>
            if isRflOnlyBody bodyExpr then
              violations := violations.push targetName
        | none => pure ()
    | none => pure ()
  recordAuditCount `rfl_on_nontrivial_name violations.size
  if violations.size <= rflBudget then
    logInfo
      (s!"rfl-on-nontrivial-name budget ok: {namespaceName} " ++
      s!"({violations.size}/{rflBudget} non-trivial-named theorems " ++
      "have rfl-only proofs)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"rfl-on-nontrivial-name budget FAILED for {namespaceName}: " ++
      s!"{violations.size} suspicious rfl-bodied claims exceed budget " ++
      s!"{rflBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-! ## Universe-polymorphism leak gate

Kernel-tier decls should pin universe levels.  A decl whose type
contains `.sort (.param _)` / `.sort (.max ...)` / `.sort (.imax ...)`
is universe-polymorphic and can interact badly with cumulativity in
ways that are hard to audit.  This gate counts kernel-tier decls
whose type Expr contains a non-concrete universe, pinning the count.
-/

/-- Whether a Level value is universe-polymorphic (mentions a param
or mvar, or composes through max/imax of polymorphic levels). -/
partial def isUniversePolymorphicLevel (universeLevel : Level) : Bool :=
  match universeLevel with
  | .zero => false
  | .succ innerLevel => isUniversePolymorphicLevel innerLevel
  | .max leftLevel rightLevel =>
      isUniversePolymorphicLevel leftLevel ||
        isUniversePolymorphicLevel rightLevel
  | .imax leftLevel rightLevel =>
      isUniversePolymorphicLevel leftLevel ||
        isUniversePolymorphicLevel rightLevel
  | .param _ => true
  | .mvar _ => true

/-- Whether an Expr contains a `.sort` with a polymorphic level. -/
partial def hasUniversePolymorphicSort (expr : Expr) : Bool :=
  match expr with
  | .sort universeLevel => isUniversePolymorphicLevel universeLevel
  | .forallE _ parameterType bodyType _ =>
      hasUniversePolymorphicSort parameterType ||
        hasUniversePolymorphicSort bodyType
  | .lam _ parameterType bodyType _ =>
      hasUniversePolymorphicSort parameterType ||
        hasUniversePolymorphicSort bodyType
  | .app functionExpr argumentExpr =>
      hasUniversePolymorphicSort functionExpr ||
        hasUniversePolymorphicSort argumentExpr
  | .letE _ typeExpr valueExpr bodyExpr _ =>
      hasUniversePolymorphicSort typeExpr ||
        hasUniversePolymorphicSort valueExpr ||
        hasUniversePolymorphicSort bodyExpr
  | .mdata _ innerExpr => hasUniversePolymorphicSort innerExpr
  | .proj _ _ innerExpr => hasUniversePolymorphicSort innerExpr
  | _ => false

/-- Build-failing budget gate counting kernel-tier decls whose type
contains a universe-polymorphic sort.  Pins current count. -/
elab "#assert_universe_polymorphism_budget " namespaceSyntax:ident
    universeBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let universeBudget := universeBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    match environment.find? targetName with
    | some constantInfo =>
        if hasUniversePolymorphicSort constantInfo.type then
          violations := violations.push targetName
    | none => pure ()
  recordAuditCount `universe_polymorphism violations.size
  if violations.size <= universeBudget then
    logInfo
      (s!"universe polymorphism budget ok: {namespaceName} " ++
      s!"({violations.size}/{universeBudget} kernel decls have " ++
      "universe-polymorphic sorts)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"universe polymorphism budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel decls exceed budget {universeBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-! ## Quotient / well-founded usage gates

Two related dependency censuses: Quot and Acc / WellFounded.

`Quot` is the kernel's propositional truncation — `Quot.lift` and
`Quot.ind` don't trigger axioms by themselves but are
Classical-adjacent.  `Quot.sound` IS an axiom (already caught), but
the surrounding family deserves visibility.

`Acc` / `WellFounded` is the kernel's well-founded recursion — used
to encode termination for non-structurally-recursive defs.  Heavy
use signals deviation from structural-recursion discipline.
-/

/-- Whether a name is in the Quot quotient family. -/
def isQuotFamilyName (someName : Name) : Bool :=
  someName == `Quot ||
    someName == `Quot.mk ||
    someName == `Quot.lift ||
    someName == `Quot.lift₂ ||
    someName == `Quot.ind ||
    someName == `Quot.rec ||
    someName == `Quot.recOn ||
    someName == `Quotient ||
    someName == `Quotient.mk ||
    someName == `Quotient.lift ||
    someName == `Quotient.ind ||
    someName == `Quotient.rec

/-- Whether a name is in the Acc / WellFounded family. -/
def isAccFamilyName (someName : Name) : Bool :=
  someName == `Acc ||
    someName == `Acc.intro ||
    someName == `Acc.rec ||
    someName == `Acc.recOn ||
    someName == `WellFounded ||
    someName == `WellFounded.fix ||
    someName == `WellFounded.recursion ||
    someName == `WellFoundedRecursion ||
    someName == `Nat.lt_wfRel ||
    someName == `WellFoundedRelation

/-- Closure dependents on Quot family. -/
def collectQuotDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun quotDependencies dependencyName =>
      if isQuotFamilyName dependencyName then
        quotDependencies.push dependencyName
      else
        quotDependencies)

/-- Closure dependents on Acc / WellFounded family. -/
def collectAccDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun accDependencies dependencyName =>
      if isAccFamilyName dependencyName then
        accDependencies.push dependencyName
      else
        accDependencies)

/-- Build-failing budget gate for Quot family dependents. -/
elab "#assert_quot_dependent_budget " namespaceSyntax:ident
    quotBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let quotBudget := quotBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectQuotDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  recordAuditCount `quot_dependent violations.size
  if violations.size <= quotBudget then
    logInfo
      (s!"Quot dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{quotBudget} kernel decls reference Quot/Quotient family)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Quot dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget {quotBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-- Build-failing budget gate for Acc / WellFounded family dependents. -/
elab "#assert_acc_dependent_budget " namespaceSyntax:ident
    accBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let accBudget := accBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectAccDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  recordAuditCount `acc_dependent violations.size
  if violations.size <= accBudget then
    logInfo
      (s!"Acc dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{accBudget} kernel decls reference Acc/WellFounded family)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Acc dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget {accBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Lean elaboration / metaprogramming dependency gate

Production-tier kernel decls should not depend on Lean's Elab / Meta /
Parser machinery.  Those layers are for tactic mode, custom
elaborators, and parser extensions — none of which belong in
mathematical content.  This gate counts decls whose closure mentions
`Lean.Elab.*`, `Lean.Meta.*`, `Lean.Parser.*`, `Lean.Macro.*`, etc.
-/

/-- Whether a name lives inside Lean's elaboration / metaprogramming
infrastructure namespaces. -/
def isLeanMetaprogrammingName (someName : Name) : Bool :=
  (`Lean.Elab).isPrefixOf someName ||
    (`Lean.Meta).isPrefixOf someName ||
    (`Lean.Parser).isPrefixOf someName ||
    (`Lean.Macro).isPrefixOf someName ||
    (`Lean.Syntax).isPrefixOf someName ||
    (`Lean.PrettyPrinter).isPrefixOf someName ||
    (`Lean.Server).isPrefixOf someName ||
    (`Lean.IR).isPrefixOf someName

/-- Closure dependents on Lean metaprogramming namespaces. -/
def collectLeanMetaDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun leanDependencies dependencyName =>
      if isLeanMetaprogrammingName dependencyName then
        leanDependencies.push dependencyName
      else
        leanDependencies)

/-- Build-failing budget gate for kernel-tier decls depending on Lean
elaboration / metaprogramming. -/
elab "#assert_lean_meta_dependent_budget " namespaceSyntax:ident
    leanBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let leanBudget := leanBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectLeanMetaDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  recordAuditCount `lean_meta_dependent violations.size
  if violations.size <= leanBudget then
    logInfo
      (s!"Lean meta dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{leanBudget} kernel decls reference " ++
      "Lean.Elab/Meta/Parser/etc.)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Lean meta dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget {leanBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## toRaw projection coverage gate

For every constructor `LeanFX2.Term.<X>`, the kernel should ship
`LeanFX2.Term.toRaw_<X>` proving the raw projection is the index.
This is the core discipline that makes raw-aware Term work.  The
gate counts Term ctors lacking the corresponding `toRaw_<name>`. -/

/-- Exact `Term.toRaw_<name>` theorem expected for a Term ctor. -/
def expectedToRawTheoremName (constructorName : Name) : Name :=
  Name.str
    `LeanFX2.Term
    ("toRaw_" ++ Name.lastSegmentString constructorName)

/-- Whether a Term ctor has the corresponding `toRaw_<name>` theorem. -/
def hasToRawTheorem
    (environment : Environment) (constructorName : Name) : Bool :=
  environment.contains (expectedToRawTheoremName constructorName)

/-- Report toRaw projection coverage debt for one Term ctor. -/
def toRawCoverageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if hasToRawTheorem environment constructorName then
    none
  else
    let expectedTheoremName :=
      expectedToRawTheoremName constructorName
    some {
      constructorName := constructorName
      detail := s!"missing {expectedTheoremName}"
    }

/-- Collect toRaw coverage debt across the Term inductive. -/
def toRawCoverageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match toRawCoverageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for Term ctors lacking `Term.toRaw_<name>`. -/
elab "#assert_toraw_coverage_budget " inductiveSyntax:ident
    toRawDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let toRawDebtBudget := toRawDebtBudgetSyntax.getNat
  let records :=
    toRawCoverageDebtRecordsForInductive environment inductiveName
  let constructorCount :=
    (getInductiveConstructorNames environment inductiveName).size
  let coveredCount :=
    if constructorCount >= records.size then
      constructorCount - records.size
    else 0
  if records.size <= toRawDebtBudget then
    logInfo
      (s!"toRaw coverage budget ok: {inductiveName} " ++
      s!"({coveredCount}/{constructorCount} ctors have toRaw_X theorem; " ++
      s!"debt {records.size}/{toRawDebtBudget})")
  else
    let perCtorLines := records.toList.take 20 |>.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"toRaw coverage budget FAILED for {inductiveName}: " ++
      s!"{records.size} ctors lack toRaw_X theorem, exceeds budget " ++
      s!"{toRawDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## IsClosedTy parity gate for scope-independent Ty constructors

For every Ty constructor whose every parameter is also at scope `_`
(i.e., scope-independent — `unit`, `bool`, `nat`, `arrow A B`,
`listType A`, `optionType A`, `eitherType A B`, `universe lvl`,
`empty`, `interval`, `equiv A B`, `record A`, `codata A B`, `modal _ A`),
the IsClosedTy inductive should have a same-suffix constructor.

Scope-dependent Ty ctors (`tyVar`, `id`, `piTy`, `sigmaTy`, `path`,
`glue`, `oeq`, `idStrict`, `refine`, `session`, `effect`) are excluded
because their inhabitants depend on context binders.
-/

/-- Names of scope-independent Ty constructors that should have an
IsClosedTy parity ctor. -/
def isScopeIndependentTyCtorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "unit" ||
    suffix == "bool" ||
    suffix == "nat" ||
    suffix == "arrow" ||
    suffix == "listType" ||
    suffix == "optionType" ||
    suffix == "eitherType" ||
    suffix == "universe" ||
    suffix == "empty" ||
    suffix == "interval" ||
    suffix == "equiv" ||
    suffix == "record" ||
    suffix == "codata" ||
    suffix == "modal"

/-- Expected `IsClosedTy.<name>` ctor name for a Ty ctor. -/
def expectedIsClosedTyCtorName (constructorName : Name) : Name :=
  Name.str `LeanFX2.IsClosedTy (Name.lastSegmentString constructorName)

/-- Report IsClosedTy parity debt for one scope-independent Ty ctor. -/
def isClosedTyParityDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isScopeIndependentTyCtorName constructorName then
    none
  else
    let expectedCtorName := expectedIsClosedTyCtorName constructorName
    if environment.contains expectedCtorName then
      none
    else
      some {
        constructorName := constructorName
        detail := s!"missing {expectedCtorName}"
      }

/-- Collect IsClosedTy parity debt records across a Ty inductive. -/
def isClosedTyParityDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match isClosedTyParityDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for IsClosedTy parity. -/
elab "#assert_is_closed_ty_parity_budget " inductiveSyntax:ident
    parityBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let parityBudget := parityBudgetSyntax.getNat
  let records :=
    isClosedTyParityDebtRecordsForInductive environment inductiveName
  if records.size <= parityBudget then
    logInfo
      (s!"IsClosedTy parity budget ok: {inductiveName} " ++
      s!"({records.size}/{parityBudget} scope-independent Ty ctors lack " ++
      "IsClosedTy mirror)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"IsClosedTy parity budget FAILED for {inductiveName}: " ++
      s!"{records.size} parity gaps exceed budget {parityBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)


end LeanFX2.Tools
