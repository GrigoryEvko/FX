# Open `sorry` tracker

Every `sorry` outside `FX/Kernel/**` and `FX/Metatheory/**` must be
listed here.  `FX/Kernel/**` and `FX/Metatheory/**` have a zero-sorry
invariant enforced by CI — they never appear in this file.

The count is reported in release notes.  It must never increase
between releases.

## Open

*(none — zero sorries anywhere in the FX tree as of Phase 2.2)*

| File  | Line | Owner | Reason | Target removal |
|-------|------|-------|--------|----------------|

As of the Phase 2.2 snapshot, `grep` confirms no `:= sorry`,
`by sorry`, or trailing-`sorry` tactic occurrence anywhere in
`FX/**/*.lean` — including the untrusted layers (Elab, Eval,
Syntax, Util, Cli) that this tracker would otherwise cover.
The `scripts/axiom-audit.sh` gate enforces zero sorry in
`FX/Kernel/**` and `FX/Metatheory/**`; the rest of the tree is
voluntarily sorry-free today but not audit-blocked.

The 24 source occurrences of the word "sorry" that `grep`
reports are keyword mentions — the `sorryKw` token in
`Token.lean`, the `sorryExpr` AST node in `Ast.lean`, the
`sorryDecl` parser form, and docstrings referencing the
mechanism — not `sorry` tactic invocations.

## Closed (for record)

*(none yet)*

---

## Policy

**Adding a sorry:**
1. The sorry must be outside `FX/Kernel/**` and `FX/Metatheory/**`.
2. Add a row to the "Open" table above with your info.
3. Estimate a target removal date (typically ≤ 3 months).
4. The PR description must explain what proof obligation the sorry
   stands for and why deferring is acceptable.

**Closing a sorry:**
1. Replace the `sorry` with a proof.
2. Move the row from "Open" to "Closed".
3. Note the PR number.

**Expiration:**
An open sorry past its target removal date generates a CI warning.
After 6 months overdue, it becomes a CI error.  Extend with an
updated target date or remove.
