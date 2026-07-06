6

A Substitution Algorithm for Multimode Type Theory: Technical Report

SF-VAR-ZERO

\[
\Theta : \operatorname{LockTele} (n \rightarrow m) \quad \mu : m \rightarrow n
\]

\[
\hat {\Gamma} \text {   sctx   } @ n \quad \alpha \in \mu \Rightarrow \text { locks } (\Theta)
\]

\[
\hat {\Gamma}. \mu . \Theta \vdash_ {\mathrm{sf}} \mathbf {v} _ {0} ^ {n} \text {var} @ m
\]

SF-VAR-SUC

\[
\Theta : \operatorname{LockTele} (n \rightarrow m)
\]

\[
\hat {\Gamma}. \Theta \vdash_ {\mathrm{sf}} v \text {var} @ m \quad \mu : o \rightarrow n
\]

\[
\hat {\Gamma}. \mu . \Theta \vdash_ {\mathrm{sf}} \operatorname{suc} (v) \text {var} @ m
\]

Figure 5 Definition of well-scoped SFMTT variables (identical to Figure 7 in the paper)

SF-EXPR-VAR

\[
\frac {\hat {\Gamma} \vdash_ {\mathrm{sf}} v \text {var} @ m}{\hat {\Gamma} \vdash_ {\mathrm{sf}} v \text {expr} @ m}
\]

SF-EXPR-BOOL

\[
\frac {\hat {\Gamma} \text {   sctx   } @ m}{\hat {\Gamma} \vdash_ {\text { sf }} \text {   Bool   expr   } @ m}
\]

SF-EXPR-TRUE

\[
\hat {\Gamma} \text {   sctx   } @ m
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} \text {   true   expr   } @ m
\]

SF-EXPR-FALSE

\[
\hat {\Gamma} \text {   sctx   } @ m
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} \text {   false   expr   } @ m
\]

SF-EXPR-IF

\[
\hat {\Gamma}. \mathbb {1} \vdash_ {\mathrm{sf}} A \text {   expr   } @ m
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} s, t, t ^ {\prime} \text {   expr   } @ m
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} \text {   if   } (A; s; t; t ^ {\prime}) \text {   expr   } @ m
\]

SF-EXPR-ARROW

\[
\mu : m \to n
\]

\[
\hat {\Gamma}. \widehat {\mathbf {a}} _ {\mu} \vdash_ {\mathrm{sf}} A \text {   expr   } @ m
\]

\[
\hat {\Gamma}. \mu \vdash_ {\mathrm{sf}} B \text {   expr   } @ n
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} (\mu \mid A) \rightarrow B \text {   expr   } @ n
\]

SF-EXPR-LAM

\[
\mu : m \to n
\]

\[
\hat {\Gamma}. \mu \vdash_ {\mathrm{sf}} t \text {   expr   } @ n
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} \lambda^ {\mu} (t) \text {   expr   } @ n
\]

SF-EXPR-APP

\[
\mu : m \to n
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} f \text {   expr   } @ n
\]

\[
\hat {\Gamma}. \widehat {\mathbf {a}} _ {\mu} \vdash_ {\mathrm{sf}} t \text {   expr   } @ m
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} \operatorname{app} _ {\mu} (f; t) \text {   expr   } @ n
\]

SF-EXPR-MOD-TY

\[
\frac {\mu : m \to n \quad \hat {\Gamma} . \widehat {\mathbf {a}} _ {\mu} \vdash_ {\mathrm{sf}} A \text {   expr   } @ m}{\hat {\Gamma} \vdash_ {\mathrm{sf}} \langle \mu | A \rangle \text {   expr   } @ n}
\]

SF-EXPR-MOD-TM

\[
\frac {\mu : m \to n \quad \hat {\Gamma} . \widehat {\mathbf {a}} _ {\mu} \vdash_ {\mathrm{sf}} t \text {   expr   } @ m}{\hat {\Gamma} \vdash_ {\mathrm{sf}} \text {   mod } _ {\mu} (t) \text {   expr   } @ n}
\]

SF-EXPR-MOD-ELIM

\[
\mu : m \to n
\]

\[
\nu : n \to o
\]

\[
\hat {\Gamma}. \widehat {\mathbf {a}} _ {\nu}. \widehat {\mathbf {a}} _ {\mu} \vdash_ {\mathrm{sf}} A \text {   expr   } @ m
\]

\[
\hat {\Gamma}. \widehat {\mathbf {a}} _ {\nu} \vdash_ {\mathrm{sf}} t \text {   expr   } @ n
\]

\[
\hat {\Gamma}. \nu \vdash_ {\mathrm{sf}} B \text {   expr   } @ o
\]

\[
\hat {\Gamma}. \nu \circ \mu \vdash_ {\mathrm{sf}} s \text {   expr   } @ o
\]

\[
\hat {\Gamma} \vdash_ {\mathrm{sf}} \operatorname{letmod} _ {\nu , \mu} (A; B; t; s) \text {   expr   } @ o
\]

Figure 6 Definition of SFMTT expressions using the judgement \(\hat{\Gamma} \vdash_{\mathrm{sf}} t \exp @ m\).

rule. However, we also need naturality with respect to  \( \mu \)  and  \( \nu \), so let  \( \alpha \in \mu \Rightarrow \mu' \)  and  \( \beta \in \nu \Rightarrow \nu' \)  and thus  \( \beta \star \alpha \in \nu \circ \mu \Rightarrow \nu' \circ \mu' \). Then we add a rule relating the key substitution for  \( \beta \star \alpha \)  to those for  \( \beta \)  and  \( \alpha \)  (WSMTT-EQ-SUB-KEY-COMPOSE-HORIZONTAL).

- The category laws (left and right unit, and associativity) turn into coherence requirements for the isomorphisms established in the previous two points. However, these are all proven by reflexivity for the identity 2-cell.

## 3 SFMTT: Full Description

### 3.1 Intrinsically Scoped Syntax for SFMTT

There are not many details regarding SFMTT that have not already been mentioned in the paper. We just include some definitions here for this report to be more or less self-contained and to be able to refer to them later.

As mentioned in the paper, SFMTT syntax is extrinsically typed but intrinsically scoped. We therefore use a notion of scoping context, whose definition is included in Figure 1. Accessible SFMTT variables are defined in Figure 5 and the full definition of SFMTT