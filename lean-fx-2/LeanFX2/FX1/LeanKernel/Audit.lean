prelude
import LeanFX2.FX1.LeanKernel.Soundness
/-! # FX1/LeanKernel/Audit

Lean kernel meta-verification audits — comprehensive `#print axioms`
cone closing **Day 8 / Phase 12.A.8** (`#1384 D8.10`).

## Day 8 acceptance — Outcome B (partial scope, zero axioms)

Day 8 ships the encoded Lean-kernel checker fragment at zero axioms across
ten of the thirteen Lean kernel `Expr` constructors:

* `sort` — universe sort formation (D8.1)
* `bvar` — bound-variable lookup via context HasTypeAt (D8.1)
* `const` — relational constant membership via Environment (D8.1)
* `forallE` — Pi formation with imax universe (D8.1)
* `lam` — lambda introduction against the inferred forall (D8.1)
* `app` — function application with Expr.instantiate codomain reduction (D8.6)
* `letE` — let introduction with Expr.instantiate body reduction (D8.7-EXTEND)
* `mdata` — transparent metadata wrapper (D8.7-EXTEND)
* `litNat` — natural-number literal pinned to canonical Nat constant (D8.7-EXTEND)
* `litStrAtom` — string-atom literal pinned to canonical String constant (D8.7-EXTEND)

Each arm composes through the executable bidirectional checker
(`Term.check`) and the soundness theorem (`check_sound`) connecting the
checker's `Option`-valued output to the relational `HasType` judgment.

Three constructors remain without HasType arms in this slice:

* `Expr.proj` — needs inductive-spec lookup + parameter-substituted field
  type computation; depends on the Inductive slice's reduction rules.
* `Expr.fvar` — needs an fvar-context separate from the bound-variable
  context, plus free-variable reindexing.
* `Expr.mvar` — Lean rejects mvars in fully-elaborated terms; the
  executable checker mirrors that policy by returning `Option.none`.

The relational typing has no rule for any of these three; the executable
checker rejects them.  This is **conservative** — every `check`-accepted
expression is witnessed by a `HasType` derivation, and the missing arms
cannot leak unsoundness because absence of a typing rule is monotone:
adding rules later can only enlarge the trusted set, never retract it.

Per Codex playbook outcomes (A=full, B=partial, C=blocked, D=abandoned),
this slice ships Outcome B with explicit forward path documented at the
matching deferred-constructors block in
`LeanFX2.FX1.LeanKernel.HasType` (lines 365-390).

## Where the strict gates live

The fail-fast comprehensive `#assert_no_axioms` cone lives in
`LeanFX2.Tools.AuditAll.AuditFX1LeanKernel_Other` (74 per-decl gates),
plus complementary census coverage in `AuditFX1LeanKernel_Env` (constant
declarations, environment lookup) and `AuditFX1LeanKernel_Expr` (Expr
inductive, renaming, substitution, beta/zeta/metadata Step, level
operations, name operations).  Build-time strict harness gates fire
inline; this file keeps the reviewer-facing `#print axioms` log.

## Reviewer-facing axiom log

Every line below must report "does not depend on any axioms".  If the
strict harness gate fails inline first, this list never prints.
-/

namespace LeanFX2
namespace FX1.LeanKernel

-- Encoded Lean-kernel relational typing judgement and its ten arms.
#print axioms LeanFX2.FX1.LeanKernel.HasType
#print axioms LeanFX2.FX1.LeanKernel.HasType.sort
#print axioms LeanFX2.FX1.LeanKernel.HasType.bvar
#print axioms LeanFX2.FX1.LeanKernel.HasType.const
#print axioms LeanFX2.FX1.LeanKernel.HasType.forallE
#print axioms LeanFX2.FX1.LeanKernel.HasType.lam
#print axioms LeanFX2.FX1.LeanKernel.HasType.app
#print axioms LeanFX2.FX1.LeanKernel.HasType.letE
#print axioms LeanFX2.FX1.LeanKernel.HasType.mdata
#print axioms LeanFX2.FX1.LeanKernel.HasType.litNat
#print axioms LeanFX2.FX1.LeanKernel.HasType.litStrAtom

-- Local context machinery underpinning bvar, lam, forallE, letE.
#print axioms LeanFX2.FX1.LeanKernel.Context
#print axioms LeanFX2.FX1.LeanKernel.Context.empty
#print axioms LeanFX2.FX1.LeanKernel.Context.extend
#print axioms LeanFX2.FX1.LeanKernel.Context.weaken
#print axioms LeanFX2.FX1.LeanKernel.Context.extendForBinder
#print axioms LeanFX2.FX1.LeanKernel.Context.HasTypeAt

-- Environment machinery underpinning const.
#print axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList
#print axioms LeanFX2.FX1.LeanKernel.Environment.HasConstant

-- Canonical primitive type names referenced by litNat / litStrAtom.
#print axioms LeanFX2.FX1.LeanKernel.Expr.natTypeName
#print axioms LeanFX2.FX1.LeanKernel.Expr.stringTypeName
#print axioms LeanFX2.FX1.LeanKernel.Expr.natType
#print axioms LeanFX2.FX1.LeanKernel.Expr.stringType

-- Executable bidirectional checker and its soundness theorem.
#print axioms LeanFX2.FX1.LeanKernel.check
#print axioms LeanFX2.FX1.LeanKernel.check_sound

end FX1.LeanKernel
end LeanFX2
