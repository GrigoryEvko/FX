prelude
import LeanFX2.FX1.Core.Expr

/-! # FX1/Core/Context

Root status: Root-FX1 syntax scaffold.

Local contexts for the minimal FX1 lambda-Pi core, plus the first syntactic
scope checker.  This is only de Bruijn well-scopedness with caller-supplied
constant visibility; typing and environment well-formedness remain later M3/M4
obligations.
-/

namespace LeanFX2.FX1

/-- Local FX1 context, storing binder type expressions from newest to oldest. -/
structure Context : Type where
  entries : List Expr

namespace Context

/-- The empty local context. -/
def empty : Context :=
  { entries := List.nil }

/-- Extend a context with one newest binder type. -/
def extend (context : Context) (typeExpr : Expr) : Context :=
  { entries := List.cons typeExpr context.entries }

/-- Count entries in a raw context-entry list. -/
def lengthInEntries : List Expr -> Nat
  | List.nil => 0
  | List.cons _ remainingEntries =>
      Nat.succ (Context.lengthInEntries remainingEntries)

/-- Number of binders in a context. -/
def length (context : Context) : Nat :=
  Context.lengthInEntries context.entries

/-- Lookup a de Bruijn index in a raw context-entry list. -/
def lookupInEntries? : List Expr -> Nat -> Option Expr
  | List.nil, _ => none
  | List.cons newestTypeExpr _, Nat.zero => some newestTypeExpr
  | List.cons _ remainingEntries, Nat.succ remainingIndex =>
      Context.lookupInEntries? remainingEntries remainingIndex

/-- Lookup a de Bruijn index in the local context. -/
def lookup? (context : Context) (index : Nat) : Option Expr :=
  Context.lookupInEntries? context.entries index

/-- Whether a de Bruijn index is bound by the context. -/
def hasIndex (context : Context) (index : Nat) : Bool :=
  match Context.lookup? context index with
  | some _ => true
  | none => false

end Context

namespace Expr

/-- Syntactic well-scopedness for FX1 expressions.

The caller supplies constant visibility because name equality and environment
well-formedness are intentionally not part of this first context slice.  Binder
types are checked in the current context, and binder bodies are checked in the
context extended by that binder type. -/
def isScopedIn
    (constantIsDeclared : Name -> Bool) :
    Context -> Expr -> Bool
  | context, Expr.bvar index => Context.hasIndex context index
  | _, Expr.sort _ => true
  | _, Expr.const constName => constantIsDeclared constName
  | context, Expr.pi domainExpr bodyExpr =>
      match Expr.isScopedIn constantIsDeclared context domainExpr with
      | true =>
          Expr.isScopedIn constantIsDeclared
            (Context.extend context domainExpr) bodyExpr
      | false => false
  | context, Expr.lam domainExpr bodyExpr =>
      match Expr.isScopedIn constantIsDeclared context domainExpr with
      | true =>
          Expr.isScopedIn constantIsDeclared
            (Context.extend context domainExpr) bodyExpr
      | false => false
  | context, Expr.app functionExpr argumentExpr =>
      match Expr.isScopedIn constantIsDeclared context functionExpr with
      | true => Expr.isScopedIn constantIsDeclared context argumentExpr
      | false => false

end Expr

end LeanFX2.FX1
