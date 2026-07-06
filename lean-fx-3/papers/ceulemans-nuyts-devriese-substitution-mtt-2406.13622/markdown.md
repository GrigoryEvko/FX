arXiv:2406.13622v1 [cs.LO] 19 Jun 2024

# A Sound and Complete Substitution Algorithm for Multimode Type Theory: Technical Report

Joris Ceulemans \( ^{1} \)

DistriNet, KU Leuven, Belgium

Andreas Nuyts \( ^{2} \)

DistriNet, KU Leuven, Belgium

Dominique Devriese

DistriNet, KU Leuven, Belgium

## 1 Introduction

This is the technical report accompanying the paper “A Sound and Complete Substitution Algorithm for Multimode Type Theory” [1]. It contains a full definition of WSMTT in Section 2, including many rules for  \( \sigma \) -equivalence and a description of all rules that have been omitted. Furthermore, we present completeness and soundness proofs of the substitution algorithm in full detail. These can be found in Sections 4 and 5 respectively. In order to make this document relatively self-contained, we also include a description of SFMTT in Section 3.

## 2 WSMTT: Full Description & σ-equivalence

### 2.1 Extrinsically typed syntax

The definition of scoping contexts and lock telescopes is repeated in Figure 1. All WSMTT expression and substitution constructors that were already covered by the paper are included in Figure 2. The other WSMTT constructors for expressions can be found in Figure 3; the description of WSMTT substitutions was already complete in the paper.

The extra constructors for WSMTT expressions include a type of booleans (WSMTT-EXPR-BOOL) with corresponding constructors (WSMTT-EXPR-TRUE and WSMTT-EXPR-FALSE) and dependent eliminator (WSMTT-EXPR-IF). We see that when applying a (dependent)  \( \mu \) -modal function to an expression t, that argument expression t must be well-scoped in the locked

\( ^{1} \)  Joris Ceulemans held a PhD fellowship (1184122N) of the Research Foundation – Flanders (FWO) while working on this research. This research is partially funded by the Research Fund KU Leuven and by the Research Foundation - Flanders (FWO; G030320N).
\( ^{2} \)  Andreas nuyts holds a Postdoctoral fellowship (1247922N) of the Research Foundation – Flanders (FWO).

SCTX-EMPTY

· sctx @ m

SCTX-LOCK

![img-0.jpeg](img-0.jpeg)

SCTX-EXTEND

![img-1.jpeg](img-1.jpeg)

LOCKTELE-EMPTY

· : LockTele(m → m)

locks (·) = 1

LOCKTELE-LOCK

![img-2.jpeg](img-2.jpeg)

locks \((\Lambda : \widehat{\mathbf{a}}_{\mu}) = \text{locks}(\Lambda) \circ \mu\)

Figure 1 Definition of scoping contexts and lock telescopes. This figure is identical to Figure 3 in the paper.

2

A Substitution Algorithm for Multimode Type Theory: Technical Report

WSMTT-EXPR-ARROW

\[
\begin{array}{c c} \mu : m \to n & \hat {\Gamma}. \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} T   \mathsf {e x p r} @ m \\ & \hat {\Gamma}. \mu \vdash_ {\mathrm{ws}} S   \mathsf {e x p r} @ n \\ \hline \hat {\Gamma} \vdash_ {\mathrm{ws}} (\mu \mid T) \to S   \mathsf {e x p r} @ n \end{array}
\]

WSMTT-EXPR-LAM

\[
\frac {\mu : m \to n \quad \hat {\Gamma} . \mu \vdash_ {\mathrm{ws}} t   \mathsf {e x p r} @ n}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \lambda^ {\mu} (t)   \mathsf {e x p r} @ n}
\]

WSMTT-EXPR-VAR

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ n \quad \mu : m \to n}{\hat {\Gamma} . \mu . \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} \mathbf {v} _ {0} \mathsf {e x p r} @ m}
\]

WSMTT-EXPR-SUB

\[
\frac {\hat {\Delta} \vdash_ {\mathrm{ws}} t \operatorname{expr} @ m \quad \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \rightarrow \hat {\Delta}) @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} t [ \sigma ] _ {\mathrm{ws}} \operatorname{expr} @ m}
\]

WSMTT-SUB-EMPTY

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ m}{\vdash_ {\mathrm{ws}} ! \mathsf {s u b} (\hat {\Gamma} \to \cdot) @ m}
\]

WSMTT-SUB-ID

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ m}{\vdash_ {\mathrm{ws}} \mathsf {i d} \mathsf {s u b} (\hat {\Gamma} \to \hat {\Gamma}) @ m}
\]

WSMTT-SUB-WEAKEN

\[
\frac {\mu : m \to n \quad \hat {\Gamma} \mathsf {s c t x} @ n}{\vdash_ {\mathrm{ws}} \pi \mathsf {s u b} (\hat {\Gamma} . \mu \to \hat {\Gamma}) @ n}
\]

WSMTT-SUB-COMPOSE

\[
\frac {\vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Delta} \to \hat {\Xi}) @ m \quad \vdash_ {\mathrm{ws}} \tau \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ m}{\vdash_ {\mathrm{ws}} \sigma \circ \tau \operatorname{sub} (\hat {\Gamma} \to \hat {\Xi}) @ m}
\]

WSMTT-SUB-LOCK

\[
\frac {\vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n \quad \mu : m \to n}{\vdash_ {\mathrm{ws}} \sigma . \widehat {\mathbf {B}} _ {\mu} \operatorname{sub} (\hat {\Gamma} . \widehat {\mathbf {B}} _ {\mu} \to \hat {\Delta} . \widehat {\mathbf {B}} _ {\mu}) @ m}
\]

WSMTT-SUB-KEY

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ m \qquad \begin{array}{l} \Theta , \Psi : \mathsf {L o c k T e l e} (m \to n) \\ \alpha \in \mathsf {l o c k s} (\Theta) \Rightarrow \mathsf {l o c k s} (\Psi) \end{array} }{\vdash_ {\mathrm{ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi} \mathsf {s u b} (\hat {\Gamma}. \Psi \to \hat {\Gamma}. \Theta) @ n}
\]

WSMTT-SUB-EXTEND

\[
\begin{array}{c c} \mu : m \to n & \vdash_ {\mathrm{ws}} \sigma   \mathsf {s u b} (\hat {\Gamma} \to \hat {\Delta}) @ n \\ & \hat {\Gamma}. \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} t   \mathsf {e x p r} @ m \\ \hline \vdash_ {\mathrm{ws}} \sigma . t   \mathsf {s u b} (\hat {\Gamma} \to \hat {\Delta}. \mu) @ n \end{array}
\]

Figure 2 Definition of WSMTT expressions (partial) and substitutions (full). This figure is identical to Figure 4 in the paper.

WSMTT-EXPR-BOOL

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \mathsf {B o o l} \mathsf {e x p r} @ m}
\]

WSMTT-EXPR-TRUE

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \mathsf {t r u e} \mathsf {e x p r} @ m}
\]

WSMTT-EXPR-FALSE

\[
\frac {\hat {\Gamma} \mathsf {s c t x} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \mathsf {f a l s e} \mathsf {e x p r} @ m}
\]

WSMTT-EXPR-IF

\[
\begin{array}{c} \hat {\Gamma}. \mathbb {1} \vdash_ {\mathrm{ws}} A \text {expr} @ m \\ \hat {\Gamma} \vdash_ {\mathrm{ws}} s, t, t ^ {\prime} \text {expr} @ m \\ \hline \hat {\Gamma} \vdash_ {\mathrm{ws}} \text {if} (A; s; t; t ^ {\prime}) \text {expr} @ m \end{array}
\]

WSMTT-EXPR-APP

\[
\begin{array}{c c}\mu : m \rightarrow n&\hat {\Gamma} \vdash_ {\mathrm{ws}} f \text {expr} @ n\\\hline&\hat {\Gamma}. \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} t \text {expr} @ m\\\hline&\hat {\Gamma} \vdash_ {\mathrm{ws}} \mathsf {a p p} _ {\mu} (f; t) \text {expr} @ n\end{array}
\]

WSMTT-EXPR-MOD-TY

\[
\frac {\mu : m \to n \quad \hat {\Gamma} . \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} A \operatorname{expr} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \langle \mu | A \rangle \operatorname{expr} @ n}
\]

WSMTT-EXPR-MOD-TM

\[
\frac {\mu : m \to n \quad \hat {\Gamma} . \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} t \operatorname{expr} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \operatorname{mod} _ {\mu} (t) \operatorname{expr} @ n}
\]

WSMTT-EXPR-MOD-ELIM

\[
\begin{array}{c c c} \mu : m \to n & \hat {\Gamma}. \widehat {\mathbf {B}} _ {\mu}. \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} A   \text {expr} @ m & \hat {\Gamma}. \nu \vdash_ {\mathrm{ws}} B   \text {expr} @ o \\ \nu : n \to o & \hat {\Gamma}. \widehat {\mathbf {B}} _ {\mu} \vdash_ {\mathrm{ws}} t   \text {expr} @ n & \hat {\Gamma}. \nu \circ \mu \vdash_ {\mathrm{ws}} s   \text {expr} @ o \\ \hline & \hat {\Gamma} \vdash_ {\mathrm{ws}} \text {letmod} _ {\nu , \mu} (A; B; t; s)   \text {expr} @ o \end{array}
\]

Figure 3 Remaining constructors for WSMTT expressions, not covered in the paper

J. Ceulemans, A. Nuyts and D. Devriese

3

context $\hat{\Gamma}, \mathbf{\Theta}_{\mu}$ (WSMTT-EXPR-APP). Furthermore, there are the WSMTT versions of the formation (WSMTT-EXPR-MOD-TY) and introduction (WSMTT-EXPR-MOD-TM) for modal types rules from MTT. The modal eliminator (WSMTT-EXPR-MOD-ELIM) corresponds to the MTT expression constructor let, $\text{mod}_{\mu}(x) = t$ in $s$, which allows us to view a term $t$ of type $\langle \mu \mid A \rangle$ as if it were of the form $\text{mod}_{\mu}(x)$ when type checking the term $s$. We refer to [2] for more details on this modal eliminator, as its behaviour with respect to substitution is not special and it does otherwise not play an important role in this report.

We emphasize again that all expression and substitution constructors in WSMTT can be obtained by removing the typing information from the corresponding constructors in MTT.

## 2.2 $\sigma$-equivalence

To recall the notation, we make use of a judgement $\hat{\Gamma} \vdash_{\text{ws}} t \equiv^{\sigma} s \text{ expr } @m$ for $\sigma$-equivalence of WSMTT expressions and $\vdash_{\text{ws}} \sigma \equiv^{\sigma} \tau \text{ sub}(\hat{\Gamma} \to \hat{\Delta}) @m$ for $\sigma$-equivalence of WSMTT substitutions. Figure 6 in the paper only provides some of the rules for $\sigma$-equivalence. In this section we spell out the full definition, or at least give a description of what the full definition should look like. Most of the rules for $\sigma$-equivalence can be found in Figure 4. All rules fall into different classes and for each class we describe the rules that have been omitted:

- There are rules expressing that $\sigma$-equivalence of expressions and substitutions are equivalence relations (reflexivity, symmetry, transitivity). We show just the rule for reflexivity in Figure 4 (WSMTT-EQ-EXPR-REFL).

- Given a mode $m$, we have a category $\text{SCtx}_m$ of scoping contexts at $m$. Its objects are given by scoping contexts and morphisms by substitutions. In order to have a category, we add rules that establish the associativity of composition and the fact that id is a unit of $\circ$. We show just 1 rule in Figure 4, namely WSMTT-EQ-SUB-ID-RIGHT.

- There are rules that express the functoriality of explicit substitution in expressions, i.e. expressions involving the identity (WSMTT-EQ-EXPR-SUB-ID) and composite substitutions (WSMTT-EQ-EXPR-SUB-COMPOSE).

- For every expression and substitution constructor that takes some arguments, there are rules expressing that it preserves $\sigma$-equivalence. We show the rules for $\_ [\_]_{\text{ws}}$ (WSMTT-EQ-EXPR-CONG-SUB), $\lambda^{\mu} (\_)$ (WSMTT-EQ-EXPR-CONG-LAM), $\text{app}_{\mu} (\_; \_)$ (WSMTT-EQ-EXPR-CONG-APP), $\_ \circ \_$ (WSMTT-EQ-SUB-CONG-COMPOSE), $\_.\_$ (WSMTT-EQ-SUB-CONG-EXTEND) and $\_,\mathbf{\Theta}_{\mu}$ (WSMTT-EQ-SUB-CONG-LOCK).

- Furthermore, we have for every expression constructor a rule expressing how substitutions can be pushed through them. We explicitly show the rules for $\lambda^{\mu} (\_)$ (WSMTT-EQ-EXPR-LAM-SUB) and $\text{app}_{\mu} (\_; \_)$ (WSMTT-EQ-EXPR-APP-SUB). Note that we make use of a lifting operation on WSMTT substitutions which is defined as follows.

$$\sigma^{+} := (\sigma \circ \pi).\mathbf{v}_{0} \tag{1}$$

- The CwF rules governing the empty context (WSMTT-EQ-SUB-EMPTY-UNIQUE) and context extension (WSMTT-EQ-EXPR-EXTEND-VAR, WSMTT-EQ-SUB-EXTEND-WEAKEN and WSMTT-EQ-SUB-EXTEND-ETA) are also present, but the ones for context extension are adapted to our modal situation, taking into account that variables are annotated with a modality in the context and that the extension constructor for substitutions takes a term that lives in a locked context.

- We have two strict 2-categories in play: the mode theory $\mathcal{M}$ and Cat, the 2-category of categories. We add rules to ensure that the intrinsically scoped WSMTT syntax

4

A Substitution Algorithm for Multimode Type Theory: Technical Report

WSMTT-EQ-EXPR-BEFL

\[
\frac {\hat {\Gamma} \vdash_ {\mathrm{ws}} t \mathsf {e x p r} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} t \equiv^ {\sigma} t \mathsf {e x p r} @ m}
\]

WSMTT-EQ-SUB-ID-RIGHT

\[
\frac {\vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \rightarrow \hat {\Delta}) @ m}{\vdash_ {\mathrm{ws}} \sigma \circ \operatorname{id} \equiv^ {\sigma} \sigma \operatorname{sub} (\hat {\Gamma} \rightarrow \hat {\Delta}) @ m}
\]

WSMTT-EQ-EXPR-SUB-ID

\[
\frac {\hat {\Gamma} \vdash_ {\mathrm{ws}} t \mathsf {e x p r} @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} t [ \mathsf {i d} ] _ {\mathrm{ws}} \equiv^ {\sigma} t \mathsf {e x p r} @ m}
\]

WSMTT-EQ-EXPR-SUB-COMPOSE

\[
\frac {\hat {\Xi} \vdash_ {\mathrm{ws}} t \operatorname{expr} @ m \quad \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Delta} \rightarrow \hat {\Xi}) @ m \quad \vdash_ {\mathrm{ws}} \tau \operatorname{sub} (\hat {\Gamma} \rightarrow \hat {\Delta}) @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} t [ \sigma \circ \tau ] _ {\mathrm{ws}} \equiv^ {\sigma} t [ \sigma ] _ {\mathrm{ws}} [ \tau ] _ {\mathrm{ws}} \operatorname{expr} @ m}
\]

WSMTT-EQ-EXPR-CONG-SUB

\[
\frac {\hat {\Delta} \vdash_ {\mathrm{ws}} t _ {1} \equiv^ {\sigma} t _ {2} \mathsf {e x p r} @ m \quad \vdash_ {\mathrm{ws}} \sigma_ {1} \equiv^ {\sigma} \sigma_ {2} \mathsf {s u b} (\hat {\Gamma} \to \hat {\Delta}) @ m}{\hat {\Gamma} \vdash_ {\mathrm{ws}} t _ {1} [ \sigma_ {1} ] _ {\mathrm{ws}} \equiv^ {\sigma} t _ {2} [ \sigma_ {2} ] _ {\mathrm{ws}} \mathsf {e x p r} @ m}
\]

WSMTT-EQ-EXPR-CONG-LAM

\[
\begin{array}{c} \mu : m \to n \\ \hat {\Gamma}. \mu \vdash_ {\mathrm{ws}} t _ {1} \equiv^ {\sigma} t _ {2} \mathsf {e x p r} @ n \\ \hline \hat {\Gamma} \vdash_ {\mathrm{ws}} \lambda^ {\mu} (t _ {1}) \equiv^ {\sigma} \lambda^ {\mu} (t _ {2}) \mathsf {e x p r} @ n \end{array}
\]

WSMTT-EQ-SUB-CONG-COMPOSE

\[
\begin{array}{c} \vdash_ {\mathrm{ws}} \sigma_ {1} \equiv^ {\sigma} \sigma_ {2} \operatorname{sub} (\hat {\Delta} \to \hat {\Xi}) @ m \\ \vdash_ {\mathrm{ws}} \tau_ {1} \equiv^ {\sigma} \tau_ {2} \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ m \\ \hline \vdash_ {\mathrm{ws}} \sigma_ {1} \circ \tau_ {1} \equiv^ {\sigma} \sigma_ {2} \circ \tau_ {2} \operatorname{sub} (\hat {\Gamma} \to \hat {\Xi}) @ m \end{array}
\]

WSMTT-EQ-EXPR-CONG-APP

\[
\begin{array}{c c} \mu : m \to n & \hat {\Gamma} \vdash_ {\mathrm{ws}} f _ {1} \equiv^ {\sigma} f _ {2} \mathsf {e x p r} @ n \\ & \hat {\Gamma}. \widehat {\mathbf {e}} _ {\mu} \vdash_ {\mathrm{ws}} t _ {1} \equiv^ {\sigma} t _ {2} \mathsf {e x p r} @ m \\ \hline \hat {\Gamma} \vdash_ {\mathrm{ws}} \mathsf {a p p} _ {\mu} (f _ {1}; t _ {1}) \equiv^ {\sigma} \mathsf {a p p} _ {\mu} (f _ {2}; t _ {2}) \mathsf {e x p r} @ n \end{array}
\]

WSMTT-EQ-SUB-CONG-EXTEND

\[
\begin{array}{c c} \mu : m \to n & \vdash_ {\mathrm{ws}} \sigma_ {1} \equiv^ {\sigma} \sigma_ {2} \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n \\ & \hat {\Gamma}. \widehat {\mathbf {e}} _ {\mu} \vdash_ {\mathrm{ws}} t _ {1} \equiv^ {\sigma} t _ {2} \operatorname{expr} @ m \\ \hline \vdash_ {\mathrm{ws}} \sigma_ {1}. t _ {1} \equiv^ {\sigma} \sigma_ {2}. t _ {2} \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}. \mu) @ n \end{array}
\]

WSMTT-EQ-SUB-CONG-LOCK

\[
\frac {\mu : m \to n \quad \vdash_ {\mathrm{ws}} \sigma_ {1} \equiv^ {\sigma} \sigma_ {2} \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n}{\vdash_ {\mathrm{ws}} \sigma_ {1} . \widehat {\mathbf {e}} _ {\mu} \equiv^ {\sigma} \sigma_ {2} . \widehat {\mathbf {e}} _ {\mu} \operatorname{sub} (\hat {\Gamma} . \widehat {\mathbf {e}} _ {\mu} \to \hat {\Delta} . \widehat {\mathbf {e}} _ {\mu}) @ m}
\]

WSMTT-EQ-EXPR-LAM-SUB

\[
\frac {\mu : m \to n \quad \hat {\Delta} . \mu \vdash_ {\mathrm{ws}} t \operatorname{expr} @ n \quad \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \left(\lambda^ {\mu} (t)\right) [ \sigma ] _ {\mathrm{ws}} \equiv^ {\sigma} \lambda^ {\mu} \left(t [ \sigma^ {+} ] _ {\mathrm{ws}}\right) \operatorname{expr} @ n}
\]

WSMTT-EQ-EXPR-APP-SUB

\[
\frac {\mu : m \to n \quad \hat {\Delta} \vdash_ {\mathrm{ws}} f \mathsf {e x p r} @ n \quad \hat {\Delta} . \widehat {\mathbf {e}} _ {\mu} \vdash_ {\mathrm{ws}} t \mathsf {e x p r} @ m \quad \vdash_ {\mathrm{ws}} \sigma \mathsf {s u b} (\hat {\Gamma} \to \hat {\Delta}) @ n}{\hat {\Gamma} \vdash_ {\mathrm{ws}} \left(\mathsf {a p p} _ {\mu} (f ; t)\right) [ \sigma ] _ {\mathrm{ws}} \equiv^ {\sigma} \mathsf {a p p} _ {\mu} \left(f [ \sigma ] _ {\mathrm{ws}} ; t [ \sigma . \widehat {\mathbf {e}} _ {\mu} ] _ {\mathrm{ws}}\right) \mathsf {e x p r} @ n}
\]

WSMTT-EQ-SUB-EMPTY-UNIQUE

\[
\frac {\vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \to \cdot) @ m}{\vdash_ {\mathrm{ws}} \sigma \equiv^ {\sigma} ! \operatorname{sub} (\hat {\Gamma} \to \cdot) @ m}
\]

WSMTT-EQ-SUB-EXTEND-WEAKEN

\[
\begin{array}{c} \mu : m \to n \\ \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n \\ \hat {\Gamma}. \widehat {\mathbf {e}} _ {\mu} \vdash_ {\mathrm{ws}} t \operatorname{expr} @ m \\ \hline \vdash_ {\mathrm{ws}} \pi \circ (\sigma . t) \equiv^ {\sigma} \sigma \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n \end{array}
\]

WSMTT-EQ-EXPR-EXTEND-VAR

\[
\frac {\mu : m \to n \quad \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n \quad \hat {\Gamma} . \widehat {\mathbf {e}} _ {\mu} \vdash_ {\mathrm{ws}} t \operatorname{expr} @ m}{\hat {\Gamma} . \widehat {\mathbf {e}} _ {\mu} \vdash_ {\mathrm{ws}} \mathbf {v} _ {0} [ (\sigma . t) . \widehat {\mathbf {e}} _ {\mu} ] _ {\mathrm{ws}} \equiv^ {\sigma} t \operatorname{expr} @ m}
\]

WSMTT-EQ-SUB-EXTEND-ETA

\[
\begin{array}{c} \mu : m \to n \\ \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}. \mu) @ n \\ \hline \vdash_ {\mathrm{ws}} \sigma \equiv^ {\sigma} (\pi \circ \sigma). (\mathbf {v} _ {0} [ \sigma . \widehat {\mathbf {e}} _ {\mu} ] _ {\mathrm{ws}}) \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}. \mu) @ n \end{array}
\]

WSMTT-EQ-SUB-LOCK-ID

\[
\frac {\mu : m \to n \quad \hat {\Gamma} \mathsf {s c t x} @ n}{\vdash_ {\mathrm{ws}} \mathsf {i d} . \widehat {\mathbf {e}} _ {\mu} \equiv^ {\sigma} \mathsf {i d} \mathsf {s u b} (\hat {\Gamma} . \widehat {\mathbf {e}} _ {\mu} \to \hat {\Gamma} . \widehat {\mathbf {e}} _ {\mu}) @ m}
\]

WSMTT-EQ-SUB-LOCK-COMPOSE

\[
\frac {\mu : m \to n \quad \vdash_ {\mathrm{ws}} \sigma \operatorname{sub} (\hat {\Delta} \to \hat {\Xi}) @ n \quad \vdash_ {\mathrm{ws}} \tau \operatorname{sub} (\hat {\Gamma} \to \hat {\Delta}) @ n}{\vdash_ {\mathrm{ws}} (\sigma \circ \tau) . \widehat {\mathbf {e}} _ {\mu} \equiv^ {\sigma} (\sigma . \widehat {\mathbf {e}} _ {\mu}) \circ (\tau . \widehat {\mathbf {e}} _ {\mu}) \operatorname{sub} (\hat {\Gamma} . \widehat {\mathbf {e}} _ {\mu} \to \hat {\Xi} . \widehat {\mathbf {e}} _ {\mu}) @ m}
\]

Figure 4 Definition of \(\sigma\)-equivalence for WSMTT expressions and substitutions (see the overview for which rules are omitted, figure continues on the next page).

J. Ceulemans, A. Nuyts and D. Devriese

5

WSMTT-EQ-SUB-KEY-NATURAL

\[
\frac {\Lambda , \Theta : \text {LockTele} (m \to n) \qquad \alpha \in \text {locks} (\Lambda) \Rightarrow \text {locks} (\Theta) \qquad \vdash_ {\text {ws}} \sigma \text {sub} (\hat {\Gamma} \to \hat {\Delta}) @ m}{\vdash_ {\text {ws}} \mathbf {Q} _ {\hat {\Delta}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \circ (\sigma . \Theta) \equiv^ {\nu} (\sigma . \Lambda) \circ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \text {sub} (\hat {\Gamma} . \Theta \to \hat {\Delta} . \Lambda) @ n}
\]

WSMTT-EQ-SUB-KEY-UNIT

\[
\frac {\hat {\Gamma} \operatorname{sctx} @ m \quad \Lambda : \operatorname{LockTele} (m \to n)}{\vdash_ {\mathrm{ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {1 _ {\text {locks} (\Lambda)} \in \Lambda \Rightarrow \Lambda} \equiv^ {\nu} \operatorname{id} \operatorname{sub} (\hat {\Gamma} . \Lambda \to \hat {\Gamma} . \Lambda) @ n}
\]

WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL

\[
\begin{array}{c c} \hat {\Gamma} \text {sctx} @ m & \alpha \in \text {locks} (\Lambda) \Rightarrow \text {locks} (\Theta) \\ \Lambda , \Theta , \Psi : \text {LockTele} (m \to n) & \beta \in \text {locks} (\Theta) \Rightarrow \text {locks} (\Psi) \\ \hline \vdash_ {\text {ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \circ \alpha \in \Lambda \Rightarrow \Psi} \equiv^ {\nu} \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \circ \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Theta \Rightarrow \Psi} \text {sub} (\hat {\Gamma}. \Psi \to \hat {\Gamma}. \Lambda) @ n \end{array}
\]

WSMTT-EQ-SUB-KEY-COMPOSE-HORIZONTAL

\[
\hat {\Gamma} \operatorname{sctx} @ m \qquad \begin{array}{l l} \Theta_ {1}, \Theta_ {2}: \operatorname{LockTele} (n \to o) & \alpha \in \operatorname{locks} (\Theta_ {1}) \Rightarrow \operatorname{locks} (\Theta_ {2}) \\ \Lambda_ {1}, \Lambda_ {2}: \operatorname{LockTele} (m \to n) & \beta \in \operatorname{locks} (\Lambda_ {1}) \Rightarrow \operatorname{locks} (\Lambda_ {2}) \end{array}
\]

\[
\vdash_ {\mathrm{ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \star \alpha \in \Lambda_ {1} \cdot \Theta_ {1} \Rightarrow \Lambda_ {2} \cdot \Theta_ {2}} \equiv^ {\nu} (\mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Lambda_ {1} \Rightarrow \Lambda_ {2}} \cdot \Theta_ {1}) \circ \mathbf {Q} _ {\hat {\Gamma} \cdot \Lambda_ {2}} ^ {\alpha \in \Theta_ {1} \Rightarrow \Theta_ {2}} \operatorname{sub} (\hat {\Gamma} \cdot \Lambda_ {2} \cdot \Theta_ {2} \to \hat {\Gamma} \cdot \Lambda_ {1} \cdot \Theta_ {1}) @ o
\]

Figure 4 Definition of \(\sigma\)-equivalence for WSMTT expressions and substitutions (continued).

provides us with a pseudofunctor SSyn from  \( M^{coop} \)  to Cat that maps every mode m to the corresponding category  \( SCtx_{m} \)  of scoping contexts and substitutions:

A modality \(\mu : m \to n\) must then be sent to a functor \(\widehat{\mathbf{Q}}_{\mu} : \mathrm{SCtx}_n \to \mathrm{SCtx}_m\), whose object part (action on scoping contexts) is defined in Figure 1 (sCTX-LOCK), and whose morphism part (action on substitutions) is defined in Figure 2 (WSMTT-SUB-LOCK). We add rules expressing the functor laws for this functor: WSMTT-EQ-SUB-LOCK-ID expresses that \(\widehat{\mathbf{Q}}_{\mu}\) preserves the identity substitution and WSMTT-EQ-SUB-LOCK-COMPOSE expresses that it preserves composition of substitutions.
A 2-cell \(\alpha \in \mu \Rightarrow \nu\) must be sent to a natural transformation \(\mathbf{Q}_{\mathbf{x}}^{\alpha}:\mathbf{Q}_{\nu}\to \mathbf{Q}_{\mu}\) whose object part (action on scoping contexts) is defined in Figure 2 (WSMTT-SUB-KEY). We add a rule WSMTT-EQ-SUB-KEY-NATURAL expressing the naturality condition. However, we immediately express naturality not only for key substitutions between locks, but more generally for key substitutions between lock telescopes.
We add rules expressing that SSyn's action on Hom-categories is strictly functorial, i.e. that identity (WSMTT-EQ-SUB-KEY-UNIT) and composition (WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL) of 2-cells are preserved.
SSyn needs to respect identity up to isomorphism, i.e. \(\widehat{\mathbf{Q}}_{\mathbf{1}}\) needs to be naturally isomorphic to the identity functor. An invertible substitution \(\hat{\Gamma}.\widehat{\mathbf{Q}}_{\mathbf{1}} \cong \hat{\Gamma}\) is given by \(\mathbf{Q}_{\hat{\Gamma}}^{1_{1} \in \cdot \Rightarrow \widehat{\mathbf{Q}}_{\mathbf{1}}}\), and naturality follows from the existing naturality rule.
SSyn needs to respect composition up to isomorphism, i.e. the diagram

\[
\begin{array}{c} \operatorname{Hom} _ {\mathcal {M}} (n, o) \times \operatorname{Hom} _ {\mathcal {M}} (m, n) \xrightarrow {- 0 -} \operatorname{Hom} _ {\mathcal {M}} (m, o) \\ \Biggl \downarrow (\widehat {\mathbf {Q}} _ {r _ {2} (-)}, \widehat {\mathbf {Q}} _ {r _ {1} (-)}) \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ \mathrm{SCtx} _ {n}, \mathrm{SCtx} _ {m} ] \times [ \mathrm{SCtx} _ {o}, \mathrm{SCtx} _ {n} ] \xrightarrow {- 0 -} [ \mathrm{SCtx} _ {o}, \mathrm{SCtx} _ {m} ] \end{array}
\]

must commute up to natural isomorphism. For any composable pair of modalities \(\mu : m \to n\) and \(\nu : n \to o\), an invertible substitution \(\hat{\Gamma} \cdot \widehat{\mathbf{Q}}_{\circ \circ \mu} \cong \hat{\Gamma} \cdot \widehat{\mathbf{Q}}_{\nu} \cdot \widehat{\mathbf{Q}}_{\mu}\) is given by \(\mathbf{Q}_{\hat{\Gamma}}^{1_{1 \circ \mu} \in \widehat{\mathbf{Q}}_{\nu} \cdot \widehat{\mathbf{Q}}_{\mu} \Rightarrow \widehat{\mathbf{Q}}_{\circ \circ \mu}\) and naturality with respect to \(\hat{\Gamma}\) follows from the existing naturality

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

J. Ceulemans, A. Nuyts and D. Devriese

7

![img-3.jpeg](img-3.jpeg)

Figure 7 Definition of atomic SFMTT renamings and substitutions (identical to Figure 8 in the paper)

![img-4.jpeg](img-4.jpeg)

Figure 8 Definition of regular SFMTT renamings and substitutions (identical to Figure 9 in the paper)

expressions can be found in Figure 6. Note that all SFMTT constructors except SF-EXPR-VAR have a counterpart in WSMTT. Conversely, all WSMTT constructors except WSMTT-EXPR-VAR and WSMTT-EXPR-SUB have a counterpart in SFMTT. Atomic and regular SFMTT rensubs are defined in Figures 7 and 8.

We also recall some of the defined operations for atomic and regular SFMTT rensubs. First of all, there is a weakening atomic rensub

$$
\pi := \text{weaken}(\mathrm{id}^a) \tag{2}
$$

from $\hat{\Gamma} \cdot \mu$ to $\hat{\Gamma}$ for any scoping context $\hat{\Gamma}$ and modality $\mu$. Furthermore, given an atomic rensub $\sigma$ from $\hat{\Gamma}$ to $\hat{\Delta}$, we can construct a new, lifted atomic rensub

$$
\sigma^+ := \text{weaken}(\sigma) \cdot \mathbf{v}_0^{1_\mu} \tag{3}
$$

from $\hat{\Gamma} \cdot \mu$ to $\hat{\Delta} \cdot \mu$ (here $\mathbf{v}_0^{1_\mu}$ is interpreted as a variable in the case of renamings and as an expression in the case of substitutions). Finally, the lift and lock operations can be extended to regular rensubs by applying those operations to all constituent atomic rensubs. In other words, we have

$$
\begin{array}{l}
\mathrm{id}^+ := \mathrm{id} \\
(\sigma \circledast \tau)^+ := \sigma^+ \circledast \tau^+ \\
\mathrm{id} \cdot \widehat{\boldsymbol{\Omega}}_\mu := \mathrm{id} \\
(\sigma \circledast \tau) \cdot \widehat{\boldsymbol{\Omega}}_\mu := (\sigma \cdot \widehat{\boldsymbol{\Omega}}_\mu) \circledast (\tau \cdot \widehat{\boldsymbol{\Omega}}_\mu).
\end{array}
$$

8

A Substitution Algorithm for Multimode Type Theory: Technical Report

### 3.2 Applying SFMTT Substitutions

#### Atomic rensubs acting on non-variable expressions

All cases for applying an atomic rensub to an SFMTT expression that is not a variable are shown below. These also include the cases that were omitted in Section 3.2.1 in the paper.

\[
\text { Bool } [ \sigma ] _ {\text { aren / asub }} = \text { Bool } \tag {4}
\]

\[
\text { true } [ \sigma ] _ {\text { aren / asub }} = \text { true } \tag {5}
\]

\[
\text { false } [ \sigma ] _ {\text { aren / asub }} = \text { false } \tag {6}
\]

\[
\text { if } (A; s; t; t ^ {\prime}) [ \sigma ] _ {\text { aren / asub }} =
\]

\[
\text { if } \left(A \left[ \sigma^ {+} \right] _ {\text { aren / asub }}; s [ \sigma ] _ {\text { aren / asub }}; t [ \sigma ] _ {\text { aren / asub }}; t ^ {\prime} [ \sigma ] _ {\text { aren / asub }}\right) \tag {7}
\]

\[
\left((\mu \mid A) \rightarrow B\right) [ \sigma ] _ {\text {aren / asub}} = \left(\mu \mid A [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}\right)\rightarrow B [ \sigma^ {+} ] _ {\text {aren / asub}} \tag {8}
\]

\[
\left(\lambda^ {\mu} (t)\right) [ \sigma ] _ {\text {aren / asub}} = \lambda^ {\mu} \left(t [ \sigma^ {+} ] _ {\text {aren / asub}}\right) \tag {9}
\]

\[
\operatorname{app} _ {\mu} (f; t) [ \sigma ] _ {\text {aren / asub}} = \operatorname{app} _ {\mu} \left(f [ \sigma ] _ {\text {aren / asub}}; t [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}\right) \tag {10}
\]

\[
\langle \mu | A \rangle [ \sigma ] _ {\text {aren / asub}} = \left\langle \mu | A [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}} \right\rangle \tag {11}
\]

\[
\operatorname{mod} _ {\mu} (t) [ \sigma ] _ {\text {aren / asub}} = \operatorname{mod} _ {\mu} \left(t [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}\right) \tag {12}
\]

\[
\operatorname{letmod} _ {\nu , \mu} (A; B; t; s) [ \sigma ] _ {\text {aren / asub}} =
\]

\[
\operatorname{letmod} _ {\nu , \mu} \left(A [ \sigma . \widehat {\mathbf {u}} _ {\nu}. \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}; B [ \sigma^ {+} ] _ {\text {aren / asub}}; t [ \sigma . \widehat {\mathbf {u}} _ {\nu} ] _ {\text {aren / asub}}; \right.
\]

\[
s \left[ \sigma^ {+} \right] _ {\text {aren / asub}}) \tag {13}
\]

#### Atomic rensubs acting on variables

For easy reference in the proofs in the next sections, we recall the algorithm for applying an atomic rensub to a variable. First of all, for applying a 2-cell to a variable, we have the following:

\[
\mathbf {v} _ {0} ^ {\beta} [ \alpha ] _ {2 - \text { cell }} ^ {\Theta \Rightarrow \Psi} = \mathbf {v} _ {0} ^ {(1 _ {\text { locks } (\Lambda)} \star \alpha) \circ \beta} \tag {14}
\]

\[
\operatorname{suc} (v) [ \alpha ] _ {2 - \text { cell }} ^ {\Theta \Rightarrow \Psi} = \operatorname{suc} \left(v [ \alpha ] _ {2 - \text { cell }} ^ {\Theta \Rightarrow \Psi}\right). \tag {15}
\]

The algorithm for applying a renaming to a variable is given by

\[
v \left[ \mathrm{id} ^ {\mathrm{a}} \right] _ {\text {aren,var}} ^ {\Lambda} = v \tag {16}
\]

\[
v \left[ \text { weaken } (\sigma) \right] _ {\text { aren,var }} ^ {\Lambda} = \text { suc } \left(v [ \sigma ] _ {\text { aren,var }} ^ {\Lambda}\right) \tag {17}
\]

\[
v \left[ \sigma . \widehat {\mathbf {u}} _ {\mu} \right] _ {\text {aren,var}} ^ {\Lambda} = v \left[ \sigma \right] _ {\text {aren,var}} ^ {\widehat {\mathbf {u}} _ {\mu}. \Lambda} \tag {18}
\]

\[
v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Theta \Rightarrow \Psi} \right] _ {\text {aren,var}} ^ {\Lambda} = v \left[ \beta \star 1 _ {\text {locks} (\Lambda)} \right] _ {2 - \text {cell}} ^ {\Theta . \Lambda \Rightarrow \Psi . \Lambda} \tag {19}
\]

\[
\mathbf {v} _ {0} ^ {\alpha} [ \sigma . w ] _ {\text {aren,var}} ^ {\Lambda} = w [ \alpha ] _ {2 - \text {cell}} ^ {\widehat {\mathbf {u}} _ {\alpha} \Rightarrow \Lambda} \tag {20}
\]

\[
\operatorname{suc} (v) [ \sigma . w ] _ {\text {aren,var}} ^ {\Lambda} = v [ \sigma ] _ {\text {aren,var}} ^ {\Lambda}. \tag {21}
\]

J. Ceulemans, A. Nuyts and D. Devriese

9

For atomic substitutions we have

\[
v \left[ \mathrm{id} ^ {\mathrm{a}} \right] _ {\text {asub,var}} ^ {\Lambda} = v \tag {22}
\]

\[
v \left[ \text { weaken } (\sigma) \right] _ {\text { asub,var }} ^ {\Lambda} = \left(v \left[ \sigma \right] _ {\text { asub,var }} ^ {\Lambda}\right) \left[ \pi . \Lambda \right] _ {\text { aren }} \tag {23}
\]

\[
v \left[ \sigma . \widehat {\mathbf {m}} _ {\mu} \right] _ {\text {asub,var}} ^ {\Lambda} = v \left[ \sigma \right] _ {\text {asub,var}} ^ {\widehat {\mathbf {m}} _ {\mu} \cdot \Lambda} \tag {24}
\]

\[
v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Theta \Rightarrow \Psi} \right] _ {\text {asub,var}} ^ {\Lambda} = v \left[ \beta \star 1 _ {\text {locks} (\Lambda)} \right] _ {2 - \text {cell}} ^ {\Theta . \Lambda \Rightarrow \Psi . \Lambda} \tag {25}
\]

\[
\mathbf {v} _ {0} ^ {\alpha} [ \sigma . t ] _ {\text {asub,var}} ^ {\Lambda} = t \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {m}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}} \tag {26}
\]

\[
\operatorname{suc} (v) [ \sigma . t ] _ {\text {asub,var}} ^ {\Lambda} = v [ \sigma ] _ {\text {asub,var}} ^ {\Lambda}. \tag {27}
\]

### 3.3 Relating WSMTT and SFMTT

We present the full definitions of the translation function  \( [\_] \)  from WSMTT to SFMTT and the embedding function  \( \text{embed}(\_) \)  in the converse direction. All interesting cases have been covered in the paper, but we include the definition here for easy reference.

#### Translation from WSMTT to SFMTT

\[
[ [ (\mu \mid A) \rightarrow B ] ] = (\mu \mid [ [ A ] ]) \rightarrow [ [ B ] ] \quad [ [! ] ] = \mathrm{id} \circledast !
\]

\[
\llbracket \lambda^ {\mu} (t) \rrbracket = \lambda^ {\mu} (\llbracket t \rrbracket) \quad \llbracket \mathrm{id} \rrbracket = \mathrm{id}
\]

\[
\llbracket \mathbf {v} _ {0} \rrbracket = \mathbf {v} _ {0} ^ {1 _ {\alpha}} \quad \llbracket \pi \rrbracket = \mathrm{id} \circledast \pi
\]

\[
\llbracket t [ \sigma ] _ {\mathrm{ws}} \rrbracket = \llbracket t \rrbracket [ \llbracket \sigma \rrbracket ] _ {\text {sub}} \quad \llbracket \sigma \circ \tau \rrbracket = \llbracket \sigma \rrbracket + + \llbracket \tau \rrbracket
\]

\[
[ [ \text { Bool } ] ] = \text { Bool } \quad [ [ \sigma . \widehat {\mathbf {m}} _ {\mu} ] ] = [ [ \sigma ]. \widehat {\mathbf {m}} _ {\mu}
\]

\[
[ [ \text {true} ] ] = \text {true} \quad \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi} \right] = \mathrm{id} \circledast \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi}
\]

\[
[ [ \text {false} ] ] = \text {false} \quad [ [ \sigma . t ] ] = [ [ \sigma ] ] ^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}. [ [ t ] ])
\]

\[
[ [ \text { if } (A; s; t; t ^ {\prime}) ] ] = \text { if } ([ [ A ] ]; [ [ s ] ]; [ [ t ] ]; [ [ t ^ {\prime} ] ])
\]

\[
\llbracket \mathsf {a p p} _ {\mu} (f; t) \rrbracket = \mathsf {a p p} _ {\mu} ([ [ f ] ]; [ [ t ] ])
\]

\[
[ [ \langle \mu \mid A \rangle ] ] = \langle \mu \mid [ [ A ] ] \rangle
\]

\[
\llbracket \operatorname{mod} _ {\mu} (t) \rrbracket = \operatorname{mod} _ {\mu} ([ [ t ] ])
\]

\[
\llbracket \operatorname{letmod} _ {\nu , \mu} (A; B; t; s) \rrbracket = \operatorname{letmod} _ {\nu , \mu} ([ [ A ] ]; [ [ B ] ]; [ [ t ] ]; [ [ s ] ])
\]

#### Embedding of SFMTT into WSMTT

For expressions we have the following.

\[
\operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) = \mathbf {v} _ {0} \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {m}} _ {\mu} \Rightarrow \Theta} \right] _ {\mathrm{ws}}
\]

\[
\operatorname{embed} (\operatorname{suc} (v)) = \operatorname{embed} (v) [ \pi . \Theta ] _ {\mathrm{ws}}
\]

\[
\operatorname{embed} (\text { Bool }) = \text { Bool }
\]

\[
\text { embed(true) } = \text { true }
\]

\[
\text { embed(false) } = \text { false }
\]

\[
\operatorname{embed} (\text { if } (A; s; t; t ^ {\prime})) = \text { if } (\operatorname{embed} (A); \operatorname{embed} (s); \operatorname{embed} (t); \operatorname{embed} (t ^ {\prime}))
\]

10

A Substitution Algorithm for Multimode Type Theory: Technical Report

\(\operatorname{embed}((\mu \mid A) \to B) = (\mu \mid \operatorname{embed}(A)) \to \operatorname{embed}(B)\)

\(\operatorname{embed}(\lambda^{\mu}(t)) = \lambda^{\mu}(\operatorname{embed}(t))\)

\(\operatorname{embed}(\operatorname{app}_{\mu}(f; t)) = \operatorname{app}_{\mu}(\operatorname{embed}(f); \operatorname{embed}(t))\)

\(\operatorname{embed}(\langle \mu \mid A \rangle) = \langle \mu \mid \operatorname{embed}(A) \rangle\)

\(\operatorname{embed}(\operatorname{mod}_{\mu}(t)) = \operatorname{mod}_{\mu}(\operatorname{embed}(t))\)

\(\operatorname{embed}(\operatorname{letmod}_{\nu, \mu}(A; B; t; s)) = \operatorname{letmod}_{\nu, \mu}(\operatorname{embed}(A); \operatorname{embed}(B); \operatorname{embed}(t); \operatorname{embed}(s))\)

Embedding SFMTT rensubs (atomic and regular) to WSMTT substitutions is defined as follows.

\(\begin{array}{ll}\operatorname{embed}(!) = ! & \operatorname{embed}\left(\mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta}\right) = \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta}\\ \operatorname{embed}(\mathrm{id}^{\mathrm{a}}) = \mathrm{id} & \operatorname{embed}(\sigma .t) = \operatorname{embed}(\sigma). \operatorname{embed}(t)\\ \operatorname{embed}(\operatorname{weaken}(\sigma)) = \operatorname{embed}(\sigma)\circ \pi & \operatorname{embed}(\mathrm{id}) = \mathrm{id}\\ \operatorname{embed}(\sigma .\widehat{\mathbf{Q}}_{\mu}) = \operatorname{embed}(\sigma).\widehat{\mathbf{Q}}_{\mu} & \operatorname{embed}(\sigma \odot \tau) = \operatorname{embed}(\sigma)\circ \operatorname{embed}(\tau) \end{array}\)

## 4 Completeness

We want to prove the statement that our substitution algorithm is complete with respect to the notion of  \( \sigma \) -equivalence introduced in Figure 4. In other words, whenever two WSMTT expressions are  \( \sigma \) -equivalent our algorithm should produce the same result.

Theorem 1. If we can deduce \(\hat{\Gamma} \vdash_{\mathrm{ws}} t \equiv^{\sigma} s \exp @ m\), then we have that \([t] = [s]\).

Before we can prove this theorem, we need some technical machinery that will be developed in the next sections.

### 4.1 Observational Equivalence of SFMTT Substitutions

#### 4.1.1 Definition & Proof Technique (Part 1)

Recall that  \( \sigma \) -equivalence for WSMTT expressions is defined mutually recursively with  \( \sigma \) -equivalence for WSMTT substitutions (see Figure 4). Therefore, in order to prove Theorem 1, we need to first extend it so as to also make a claim about  \( \sigma \) -equivalent WSMTT substitutions. However, in SFMTT, syntactic equality of substitutions is not a good notion of equivalence. Instead, we will use the following:

▶ Definition 2 (Observational equivalence). We say that two SFMTT substitutions  \( \vdash_{sf} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  are observationally equivalent when  \( t [\sigma]_{sub} = t [\tau]_{sub} \)  for every expression  \( \hat{\Delta} \vdash_{sf} t \exp @ m \) . We will write this as  \( \sigma \approx^{obs} \tau \) .

Note that  \( \approx^{obs} \)  is clearly an equivalence relation. The requirement for two SFMTT substitutions to be observationally equivalent is quite strong. In order to prove this, we will make use of the technique outlined in Propositions 3 and 12. Both propositions refer to general scoping telescopes which may contain both variables and locks, see Figure 9 for their definition. We will refer to such scoping telescopes with the Greek letter  \( \Phi \) . They also act on SFMTT substitutions in the following way.

\(\sigma .\cdot = \sigma\)   
\(\sigma .(\Phi .\mu) = (\sigma .\Phi)^{+}\)   
\(\sigma .(\Phi .\widehat{\mathbf{Q}}_{\mu}) = (\sigma .\Phi).\widehat{\mathbf{Q}}_{\mu}\)

J. Ceulemans, A. Nuyts and D. Devriese

11

|  STELE-EMPTY | STELE-EXTEND | STELE-LOCK  |
| --- | --- | --- |
|  \( \cdot : \mathsf{sTele}(m \to m) \) | \( \Phi : \mathsf{sTele}(n \to m) \quad \mu : o \to m \) | \( \Phi : \mathsf{sTele}(n \to m) \quad \mu : o \to m \)  |
|  \( \hat{\Gamma} \cdot \cdot = \hat{\Gamma} \) | \( \Phi \cdot \mu : \mathsf{sTele}(n \to m) \) | \( \Phi \cdot \widehat{\mathbf{\Omega}}_{\mu} : \mathsf{sTele}(n \to o) \)  |
|   | \( \hat{\Gamma} \cdot (\Phi \cdot \mu) = (\hat{\Gamma} \cdot \Phi) \cdot \mu \) | \( \hat{\Gamma} \cdot (\Phi \cdot \widehat{\mathbf{\Omega}}_{\mu}) = (\hat{\Gamma} \cdot \Phi) \cdot \widehat{\mathbf{\Omega}}_{\mu} \)  |

Figure 9 Definition of scoping telescopes and how to append them to a scoping context (note that a scoping telescope \(\Phi : \mathsf{sTele}(n \to m)\) can be appended to a scoping context at mode \(n\) to obtain a scoping context at mode \(m\))

(Recall that the \(\widehat{\mathbf{\Omega}}_{\mu}\) and \(^+\) operations on SFMTT substitutions apply the corresponding operations to all atomic substitutions.) In other words, whenever \(\vdash_{\mathrm{sf}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) is an SFMTT substitution and \(\Phi : \mathsf{sTele}(m \to n)\) a scoping telescope, we get an SFMTT substitution \(\vdash_{\mathrm{sf}} \sigma \cdot \Phi \operatorname{sub}(\hat{\Gamma} \cdot \Phi \to \hat{\Delta} \cdot \Phi) @ n\).

▶ Proposition 3. Let  \( \vdash_{sf} \sigma, \tau \text{ sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  be two SFMTT substitutions and suppose that  \( v [\sigma \cdot \Phi]_{\text{sub}} = v [\tau \cdot \Phi]_{\text{sub}} \)  for every scoping telescope  \( \Phi : sTele(m \to n) \)  and every variable  \( \hat{\Delta} \cdot \Phi \vdash_{sf} v \text{ var } @ n \) . Then  \( \sigma \approx^{obs} \tau \) .

Proof. We will prove that \( t[\sigma \cdot \Phi]_{\mathrm{sub}} = t[\tau \cdot \Phi]_{\mathrm{sub}} \) for all \( \Phi : \mathsf{sTele}(m \to n) \) and all expressions \( \hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} t \exp @n \). The result then follows by taking \( \Phi \) to be the empty scoping telescope.

The proof proceeds by induction and case analysis on the expression \( t \). We will describe only a few cases since there is a lot of similarity.

CASE \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}v\operatorname{expr}@n\) for some \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}v\operatorname{var}@n\) (SF-EXPR-VAR)

In this case the assumptions of the proposition we are proving tell us exactly that \( v[\sigma, \Phi]_{\mathrm{sub}} = v[\tau, \Phi]_{\mathrm{sub}} \).

CASE \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}\lambda^{\mu}(t)\) expr @ \(n\) for some \(\hat{\Delta}.\Phi.\mu\vdash_{\mathrm{sf}}t\) expr @ \(n\) (SF-EXPR-LAM)

Recall that an SFMTT substitution is just a sequence of atomic SFMTT substitutions which are applied sequentially to an expression. Following Equation (9) each of these atomic substitutions will be pushed through the  \( \lambda^{\mu} \)  constructor, applying a lifting  \( (^{+}) \)  to that atomic substitution. Since the lifting of regular SFMTT substitutions applies the lifting to all its constituent atomic substitutions, we have that

\[
\left(\lambda^ {\mu} (t)\right) [ \sigma . \Phi ] _ {\mathrm{sub}} = \lambda^ {\mu} \left(t [ (\sigma . \Phi) ^ {+} ] _ {\mathrm{sub}}\right) = \lambda^ {\mu} \left(t [ \sigma . (\Phi . \mu) ] _ {\mathrm{sub}}\right),
\]

and similar for \(\tau\). We can now apply the induction hypothesis for the structurally smaller term \(t\) to obtain that \(t[\sigma, (\Phi, \mu)]_{\mathrm{sub}} = t[\tau, (\Phi, \mu)]_{\mathrm{sub}}\).

CASE \(\hat{\Delta}.\Phi\vdash_{\mathrm{sf}}\mathrm{mod}_{\mu}(t)\) expr @ \(n\) for some \(\hat{\Delta}.\Phi.\widehat{\mathbf{\Omega}}_{\mu}\vdash_{\mathrm{sf}}t\) expr @ \(o\) (SF-EXPR-MOD-TM)

We can follow a similar style of reasoning as in the previous case, taking into account that applying a lock to a regular SFMTT substitution applies that lock to all constituent atomic substitutions. Using Equation (12) for every atomic substitution, we then get that

\[
\left(\operatorname{mod} _ {\mu} (t)\right) [ \sigma . \Phi ] _ {\text {sub}} = \operatorname{mod} _ {\mu} \left(t [ (\sigma . \Phi). \widehat {\mathbf {\Omega}} _ {\mu} ] _ {\text {sub}}\right) = \operatorname{mod} _ {\mu} \left(t [ \sigma . (\Phi . \widehat {\mathbf {\Omega}} _ {\mu}) ] _ {\text {sub}}\right),
\]

and similar for \(\tau\). The induction hypothesis for \(t\) gives us that \(t[\sigma, (\Phi, \widehat{\mathbf{\Omega}}_{\mu})]_{\mathrm{sub}} = t[\tau, (\Phi, \widehat{\mathbf{\Omega}}_{\mu})]_{\mathrm{sub}}\).

#### 4.1.2 Mixed Sequences of Atomic Rensubs

Using Proposition 3 to prove observational equivalence is still far from trivial. Therefore, Proposition 12 will relax the requirement so that we only have to check the equality of

12

A Substitution Algorithm for Multimode Type Theory: Technical Report

|  SF-MIX-ID | SF-MIX-AREN | SF-MIX-ASUB  |
| --- | --- | --- |
|  \( \hat{\Gamma} \) sctx @ m | \( \vdash_{\text{sf}} \bar{\sigma} \) seq(\( \hat{\Delta} \to \hat{\Xi} \)) @ m | \( \vdash_{\text{sf}} \bar{\sigma} \) seq(\( \hat{\Delta} \to \hat{\Xi} \)) @ m  |
|  \( \vdash_{\text{sf}} \) id\( ^{\text{m}} \) seq(\( \hat{\Gamma} \to \hat{\Gamma} \)) @ m | \( \vdash_{\text{sf}} \tau \) aren(\( \hat{\Gamma} \to \hat{\Delta} \)) @ m | \( \vdash_{\text{sf}} \tau \) asub(\( \hat{\Gamma} \to \hat{\Delta} \)) @ m  |
|   | \( \vdash_{\text{sf}} \bar{\sigma} \) @aren \( \tau \) seq(\( \hat{\Gamma} \to \hat{\Xi} \)) @ m | \( \vdash_{\text{sf}} \bar{\sigma} \) @asub \( \tau \) seq(\( \hat{\Gamma} \to \hat{\Xi} \)) @ m  |

\[
\left(\mathrm{id} ^ {\mathrm{m}}\right) ^ {+} := \mathrm{id} ^ {\mathrm{m}} \quad \left(\bar {\sigma} @ _ {\text {aren}} \tau\right) ^ {+} := \bar {\sigma} ^ {+} @ _ {\text {aren}} \tau^ {+} \quad \left(\bar {\sigma} @ _ {\text {asub}} \tau\right) ^ {+} := \bar {\sigma} ^ {+} @ _ {\text {asub}} \tau^ {+}
\]

\[
\mathrm{id} ^ {\mathrm{m}}. \widehat {\mathbf {m}} _ {\mu} := \mathrm{id} ^ {\mathrm{m}} \quad \left(\bar {\sigma} @ _ {\text {aren}} \tau\right). \widehat {\mathbf {m}} _ {\mu} := \bar {\sigma}. \widehat {\mathbf {m}} _ {\mu} @ _ {\text {aren}} \tau . \widehat {\mathbf {m}} _ {\mu} \quad \left(\bar {\sigma} @ _ {\text {asub}} \tau\right). \widehat {\mathbf {m}} _ {\mu} := \bar {\sigma}. \widehat {\mathbf {m}} _ {\mu} @ _ {\text {asub}} \tau . \widehat {\mathbf {m}} _ {\mu}
\]

\[
t \left[ \mathrm{id} ^ {\mathrm{m}} \right] _ {\text {seq}} := t \quad t \left[ \bar {\sigma} @ _ {\text {aren}} \tau \right] _ {\text {seq}} := t \left[ \bar {\sigma} \right] _ {\text {seq}} \left[ \tau \right] _ {\text {aren}} \quad t \left[ \bar {\sigma} @ _ {\text {asub}} \tau \right] _ {\text {seq}} := t \left[ \bar {\sigma} \right] _ {\text {seq}} \left[ \tau \right] _ {\text {asub}}
\]

\[
\bar {\sigma} \cdot \cdot := \bar {\sigma} \quad \bar {\sigma} \cdot (\Phi \cdot \mu) := (\bar {\sigma} \cdot \Phi) ^ {+} \quad \bar {\sigma} \cdot (\Phi \cdot \widehat {\mathbf {m}} _ {\mu}) := (\bar {\sigma} \cdot \Phi) \cdot \widehat {\mathbf {m}} _ {\mu}
\]

Figure 10 Definition of mixed sequences of atomic rensubs and associated operations of lifting, locking and application to an SFMTT expression. We also show how to apply a scoping telescope to a mixed sequence.

substituted variables after extending the context with an arbitrary lock telescopes instead of a scoping telescope. However, in order to prove this proposition we will need some auxiliary results.

First of all, we will formulate a generalisation of Proposition 3 that applies to sequences consisting of both atomic renamings and atomic substitutions. This generalisation is needed in the proof of Proposition 12, but also in the completeness proof itself. We define such mixed sequences in Figure 10. That figure also contains definitions for the operations of lifting a sequence, applying a lock to a sequence, applying a sequence to an SFMTT expression, and applying a scoping telescope to a sequence. These operations just apply the corresponding operations to the constituent atomic renamings and substitutions. To distinguish a mixed sequence from atomic or regular rensubs, we will refer to such a sequence with an overlined Greek letter (so e.g. \(\bar{\sigma}\)).

▶ Proposition 4. Let  \( \vdash_{sf} \bar{\sigma}, \bar{\tau} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  be two mixed sequences of atomic renamings and substitutions and suppose that  \( v [\bar{\sigma}. \Phi]_{\operatorname{seq}} = v [\bar{\tau}. \Phi]_{\operatorname{seq}} \)  for every scoping telescope  \( \Phi : s\operatorname{Tele}(m \to n) \)  and every variable  \( \hat{\Delta}. \Phi \vdash_{sf} v \operatorname{var} @ n \) . Then  \( t [\bar{\sigma}]_{\operatorname{seq}} = t [\bar{\tau}]_{\operatorname{seq}} \)  for every SFMTT expression  \( \hat{\Delta} \vdash_{sf} t \operatorname{expr} @ m \) .

Proof. The reasoning is exactly the same as in the proof of Proposition 3.

#### 4.1.3 Action of Lifted Atomic Rensubs on Variables

\(\triangleright\) Lemma 5. Given an atomic renaming \(\vdash_{\mathrm{sf}} \sigma \operatorname{aren}(\hat{\Gamma} \to \hat{\Delta}) @ m\) and a lock telescope \(\Lambda: \operatorname{LockTele}(m \to n)\), we have that \(\mathbf{v}_0^\alpha [\sigma^+]_{\mathrm{aren}}^\Lambda = \mathbf{v}_0^\alpha\) and \(\operatorname{suc}(v) [\sigma^+]_{\mathrm{aren}}^\Lambda = \operatorname{suc}\left(v [\sigma]_{\mathrm{aren}}^\Lambda\right)\). Note that we will no longer include var in the subscript of \(v [\sigma]_{\mathrm{aren},\mathrm{var}}^\Lambda\) but just write \(v [\sigma]_{\mathrm{aren}}^\Lambda\).

Proof. Recall that \(\sigma^{+}\) is defined as \(\mathrm{weaken}(\sigma).\mathbf{v}_{0}^{1_{\mu}}\). We can then compute that

\[
\mathbf {v} _ {0} ^ {\alpha} \left[ \sigma^ {+} \right] _ {\text {aren}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {\alpha} \left[ \text {weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {aren}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \alpha ] _ {2 - \text {cell}} ^ {\widehat {\mathbf {m}} _ {\mu} \Rightarrow \Lambda},
\]

where the last step makes use of Equation (20). By the definition of \(\_ [\_]_{2 - \text{cell}}^{\Rightarrow}\) (see Equation (14)), this last expression is equal to \(\mathbf{v}_0^{(1_1\star \alpha)\circ 1_\mu}\). From the laws of a strict 2-category, it follows that \((1_1\star \alpha)\circ 1_\mu = \alpha\) so the variable we obtain is really \(\mathbf{v}_0^\alpha\).

J. Ceulemans, A. Nuyts and D. Devriese

13

In the case for \(\operatorname{suc}(v)\), we can compute that

\[
\begin{array}{l} \operatorname{suc} (v) \left[ \sigma^ {+} \right] _ {\text {aren}} ^ {\Lambda} = \operatorname{suc} (v) \left[ \operatorname{weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {aren}} ^ {\Lambda} \\ = v \left[ \text { weaken } (\sigma) \right] _ {\text { aren }} ^ {\Lambda} \quad \text {(Equation (21))} \\ = \operatorname{suc} \left(v [ \sigma ] _ {\text {aren}} ^ {\Lambda}\right). \tag {Equation(17)} \\ \end{array}
\]

Repeatedly applying Lemma 5 and realising that the lifting of a regular renaming consists of the liftings of its individual atomic renamings, one can see that the statement of Lemma 5 also holds for regular renamings.

For atomic substitutions we have the following result.

▶ Lemma 6. Given an atomic substitution  \( \vdash_{sf} \sigma \)  asub( \( \hat{\Gamma} \rightarrow \hat{\Delta} \) ) @ m and a lock telescope  \( \Lambda : \text{LockTele}(m \rightarrow n) \) , we have that  \( v_{0}^{\alpha} [\sigma^{+}]_{asub}^{\Lambda} = v_{0}^{\alpha} \)  and  \( \text{suc}(v) [\sigma^{+}]_{asub}^{\Lambda} = v [\sigma]_{asub}^{\Lambda} [\pi]_{aren}^{\Lambda} \)  for every  \( \hat{\Delta} \cdot \Lambda \vdash_{sf} v \)  var @ n.

Proof. For  \( v_{0}^{\alpha} \)  the computation proceeds as follows.

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \sigma^ {+} \right] _ {\text {asub}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {\alpha} \left[ \text {weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {asub}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ \mathbf {Q} _ {\hat {\Gamma}, \mu} ^ {\alpha \in \widehat {\mathbf {Q}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}} (Equation(26)) \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \alpha ] _ {2 - \text { cell }} ^ {\widehat {\mathbf {Q}} _ {\mu} \Rightarrow \Lambda} (Equation(19)) \\ = \mathbf {v} _ {0} ^ {(1 _ {1} * \alpha) \circ 1 _ {\mu}} (Equation(14)) \\ = \mathbf {v} _ {0} ^ {\alpha} \\ \end{array}
\]

For \(\operatorname{suc}(v)\) we have

\[
\begin{array}{l} \operatorname{suc} (v) \left[ \sigma^ {+} \right] _ {\text {asub}} ^ {\Lambda} = \operatorname{suc} (v) \left[ \text {weaken} (\sigma). \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text {asub}} ^ {\Lambda} \\ = v \left[ \text { weaken } (\sigma) \right] _ {\text { asub }} ^ {\Lambda} \tag {Equation(27)} \\ = v \left[ \sigma \right] _ {\text {asub}} ^ {\Lambda} \left[ \pi \right] _ {\text {aren}} ^ {\Lambda}. \tag {Equation(23)} \\ \end{array}
\]

#### 4.1.4 Lifted Atomic Rensubs and  \( \pi \)

▶ Lemma 7. Let \(\Phi : \mathsf{sTele}(m \to n)\) be a scoping telescope, \(\vdash_{\mathsf{sf}} \sigma \operatorname{aren}(\hat{\Gamma} \to \hat{\Delta}) @ m\) an atomic SFMTT renaming and \(\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \operatorname{expr} @ n\) an expression. Then \(t[\pi \cdot \Phi]_{\mathsf{aren}}[\sigma^{+} \cdot \Phi]_{\mathsf{aren}} = t[\sigma \cdot \Phi]_{\mathsf{aren}}[\pi \cdot \Phi]_{\mathsf{aren}}\).

Proof. We use Proposition 4 with the two sequences \(\bar{\sigma}\) and \(\bar{\tau}\) each consisting of the two atomic renamings on both sides of the lemma. In other words, we need to prove that \(v[\pi \cdot \Phi]_{\mathrm{aren}}[\sigma^{+}. \Phi]_{\mathrm{aren}} = v[\sigma \cdot \Phi]_{\mathrm{aren}}[\pi \cdot \Phi]_{\mathrm{aren}}\) for every variable \(\hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} v \operatorname{var} @ n\). We will do this by induction on the number of variables in \(\Phi\).

CASE \(\Phi = \Lambda\), so \(\Phi\) contains only locks.

Now we can compute that

\[
\begin{array}{l} v [ \pi . \Lambda ] _ {\text {aren}} [ \sigma^ {+}. \Lambda ] _ {\text {aren}} = v [ \pi ] _ {\text {aren}} ^ {\Lambda} [ \sigma^ {+} ] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} (v) \left[ \sigma^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} \left(v [ \sigma ] _ {\text {aren}} ^ {\Lambda}\right) \tag {Lemma5} \\ = v \left[ \sigma \right] _ {\text {aren}} ^ {\Lambda} \left[ \pi \right] _ {\text {aren}} ^ {\Lambda} \\ = v [ \sigma . \Lambda ] _ {\text {aren}} [ \pi . \Lambda ] _ {\text {aren}} \\ \end{array}
\]

14

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\Phi = \Phi^{\prime}\cdot \rho \cdot \Lambda\)

We now have to distinguish two cases for the variable \( v \).

CASE \(v = \mathbf{v}_0^\alpha\)

The computations go as follows.

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \left(\sigma^ {+}. \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   5 }) \\ \end{array}
\]

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   5 }) \\ \end{array}
\]

CASE \(v = \operatorname{suc}(v')\)

Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\pi . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ \left(\sigma^ {+}. \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \pi . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right) \left[ \left(\sigma^ {+}. \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \pi . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}} \left[ \sigma^ {+}. \Phi^ {\prime}. \Lambda \right] _ {\text {aren}}\right) \tag {Lemma5} \\ \end{array}
\]

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\sigma . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \left[ \left(\pi . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \sigma . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right) \left[ \left(\pi . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda} \tag {Lemma5} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \sigma . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}}\right). \tag {Lemma5} \\ \end{array}
\]

Hence the result directly follows from the induction hypothesis with scoping telescope  \( \Phi^{\prime}.\Lambda \)  (which has one variable less than  \( \Phi \) ).

▶ Corollary 8. Let \(\Phi_1: \mathsf{sTele}(m \to n)\) and \(\Phi_2: \mathsf{sTele}(n \to o)\) be two scoping telescopes, \(\vdash_{\mathsf{sf}} \sigma \mathsf{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) an atomic substitution and \(\hat{\Delta}. \Phi_1. \Phi_2 \vdash_{\mathsf{sf}} t \mathsf{expr} @ o\) an SFMTT expression. Then we have that \(t[\pi. \Phi_2]_{\mathsf{aren}}[\sigma. \Phi_1. \mu. \Phi_2]_{\mathsf{aren}} = t[\sigma. \Phi_1. \Phi_2]_{\mathsf{aren}}[\pi. \Phi_2]_{\mathsf{aren}}\).

Proof. This follows directly from Lemma 7 by taking \(\sigma\) to be \(\sigma \cdot \Phi_1\) and \(\Phi\) to be \(\Phi_2\), and realising that \(\sigma \cdot \Phi_1 \cdot \mu = (\sigma \cdot \Phi_1)^+\).

We also need a result like Lemma 7, but where \(\sigma\) is an atomic substitution instead of an atomic renaming.

▶ Lemma 9. Let \(\Phi : \mathsf{sTele}(m \to n)\) be a scoping telescope, \(\vdash_{\mathsf{sf}} \sigma \mathsf{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) an atomic SFMTT substitution and \(\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \mathsf{expr} @ n\) an expression. Then \(t[\pi \cdot \Phi]_{\mathsf{aren}}[\sigma^{+} \cdot \Phi]_{\mathsf{asub}} = t[\sigma \cdot \Phi]_{\mathsf{asub}}[\pi \cdot \Phi]_{\mathsf{aren}}\).

J. Ceulemans, A. Nuyts and D. Devriese

15

Proof. The proof is similar to that of Lemma 7. We make use of Proposition 4, and now we really have two sequences both consisting of an atomic renaming and an atomic substitution. Hence, we have to show that \( v[\pi \cdot \Phi]_{\mathrm{aren}}[\sigma^{+}\cdot \Phi]_{\mathrm{asub}} = v[\sigma \cdot \Phi]_{\mathrm{asub}}[\pi \cdot \Phi]_{\mathrm{aren}} \) for every variable \( \Delta \cdot \Phi \vdash_{\mathrm{st}} v \) var \( \otimes n \). We will do this by induction on the number of variables in the scoping telescope \( \Phi \).

CASE \(\Phi = \Lambda\), so \(\Phi\) contains no variables.

Now we can compute that

\[
\begin{array}{l} v [ \pi . \Lambda ] _ {\text { aren }} [ \sigma^ {+}. \Lambda ] _ {\text { asub }} = v [ \pi ] _ {\text { aren }} ^ {\Lambda} [ \sigma^ {+} ] _ {\text { asub }} ^ {\Lambda} \\ = \operatorname{suc} (v) [ \sigma^ {+} ] _ {\text { asub }} ^ {\Lambda} \\ = v [ \sigma ] _ {\text { asub }} ^ {\Lambda} [ \pi ] _ {\text { aren }} ^ {\Lambda} \tag {Lemma6} \\ = v [ \sigma . \Lambda ] _ {\text { asub }} [ \pi . \Lambda ] _ {\text { aren }}. \\ \end{array}
\]

CASE \(\Phi = \Phi^{\prime}\cdot \rho .\Lambda\)

We now have to distinguish two cases for the variable v.

CASE \(v = \mathbf{v}_0^\alpha\)

The computations go as follows.

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { asub }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \tag {Lemma5} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   6 }) \\ \end{array}
\]

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { asub }} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \tag {Lemma6} \\ = \mathbf {v} _ {0} ^ {\alpha} \quad (\text { Lemma   5 }) \\ \end{array}
\]

CASE \(v = \operatorname{suc}(v')\)

Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { aren }} \left[ \sigma^ {+}. \Phi^ {\prime}. \rho . \Lambda \right] _ {\text { asub }} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ (\pi . \Phi^ {\prime}) ^ {+} \right] _ {\text { aren }} ^ {\Lambda} \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text { asub }} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \pi . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right) \left[ (\sigma^ {+}. \Phi^ {\prime}) ^ {+} \right] _ {\text {asub}} ^ {\Lambda} \tag {Lemma5} \\ = v ^ {\prime} \left[ \pi . \Phi^ {\prime}. \Lambda \right] _ {\text {aren}} \left[ \sigma^ {+}. \Phi^ {\prime}. \Lambda \right] _ {\text {asub}} \left[ \pi . \Lambda \right] _ {\text {aren}} \tag {Lemma6} \\ \end{array}
\]

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {asub}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\sigma . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \\ = v ^ {\prime} \left[ \sigma . \Phi^ {\prime}. \Lambda \right] _ {\text {asub}} \left[ \pi . \Lambda \right] _ {\text {aren}} \left[ \pi . \Phi^ {\prime}. \rho . \Lambda \right] _ {\text {aren}} \tag {Lemma6} \\ \end{array}
\]

The induction hypothesis with scoping telescope \(\Phi'.\Lambda\) (which has one variable less than \(\Phi\)) gives us that \(v'\left[\pi.\Phi'.\Lambda\right]_{\mathrm{aren}}\left[\sigma^{+}.\Phi'.\Lambda\right]_{\mathrm{asub}} = v'\left[\sigma.\Phi'.\Lambda\right]_{\mathrm{asub}}\left[\pi.\Phi'.\Lambda\right]_{\mathrm{aren}}\). The result then follows from Corollary 8 with \(t = v'\left[\sigma.\Phi'.\Lambda\right]_{\mathrm{asub}}\), \(\sigma = \pi\), \(\Phi_1 = \Phi'\), \(\mu = \rho\) and \(\Phi_2 = \Lambda\).

◀

16

A Substitution Algorithm for Multimode Type Theory: Technical Report

Combining Lemmas 7 and 9, we get the following result.

▶ Lemma 10. Let \(\Phi : \mathsf{sTele}(m \to n)\) be a scoping telescope, \(\vdash_{\mathsf{sf}} \bar{\sigma} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m\) a mixed sequence of atomic renamings and substitution and \(\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \operatorname{expr} @ n\) an SFMTT expression. Then \(t[\pi \cdot \Phi]_{\text{aren}}[\bar{\sigma}^{+} \cdot \Phi]_{\text{seq}} = t[\bar{\sigma} \cdot \Phi]_{\text{seq}}[\pi \cdot \Phi]_{\text{aren}}\).

Proof. In Figure 10 we see that the lifting and lock operations on mixed sequences of atomic rensubs consist of applying these operations to all constituent atomic rensubs. From this we deduce that also applying a general scoping telescope \(\Phi\) to such a mixed sequence amounts to applying \(\Phi\) to every constituent atomic rensub. Hence the result follows by repeatedly using Lemmas 7 and 9 for every atomic rensub in \(\bar{\sigma}\).

#### 4.1.5 Proof Technique (Part 2)

Using the results from the previous sections, we can now relax the requirement from Proposition 4 so that we only need to check the equality of applying two mixed sequences to a variable after adding a lock telescope instead of a general scoping telescope.

▶ Proposition 11. If \(\vdash_{\mathrm{sf}} \bar{\sigma}, \bar{\tau} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m\) are two mixed sequences of SFMTT atomic rensubs such that \(v[\bar{\sigma} \cdot \Lambda]_{\mathrm{seq}} = v[\bar{\tau} \cdot \Lambda]_{\mathrm{seq}}\) for every lock telescope \(\Lambda: \operatorname{LockTele}(m \to n)\) and every variable \(\hat{\Delta} \cdot \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ n\), then \(t[\bar{\sigma}]_{\mathrm{seq}} = t[\bar{\tau}]_{\mathrm{seq}}\) for all expressions \(\hat{\Delta} \vdash_{\mathrm{sf}} t \operatorname{expr} @ m\).

Proof. We make use of Proposition 4, so we have to show that \( v[\bar{\sigma} \cdot \Phi]_{\mathrm{seq}} = v[\bar{\tau} \cdot \Phi]_{\mathrm{seq}} \) for every scoping telescope \( \Phi : \mathsf{sTele}(m \to n) \) and every variable \( \hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} v \operatorname{var} @ n \). We do this by induction on the number of variables in the scoping telescope \( \Phi \).

CASE \(\Phi = \Lambda\), so there are no variables in \(\Phi\).

The result is exactly the assumption of the proposition we are proving.

CASE \(\Phi = \Phi'\). \(\mu\). \(\Lambda\) with \(\Lambda\) a lock telescope

We distinguish between the two different cases for the variable v.

CASE \(v = \mathbf{v}_0^\alpha\)

For every atomic rensub \(\vdash_{\mathrm{sf}} \chi \operatorname{aren} / \operatorname{asub} (\hat{\Gamma} \to \hat{\Delta}) @ m\) we have that

\[
\mathbf {v} _ {0} ^ {\alpha} \left[ \chi . \Phi^ {\prime}. \mu . \Lambda \right] _ {\text {aren / asub}} = \mathbf {v} _ {0} ^ {\alpha} \left[ (\chi . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren / asub}} ^ {\Lambda} = \mathbf {v} _ {0} ^ {\alpha}. \quad (\text {Lemmas 5 and 6})
\]

By repeatedly applying this result it follows that the same is true for sequences of atomic rensubs. In particular, we can conclude that \(\mathbf{v}_0^\alpha [\bar{\sigma} \cdot \Phi'.\mu .\Lambda ]_{\mathrm{seq}} = \mathbf{v}_0^\alpha =\) \(\mathbf{v}_0^\alpha [\bar{\tau} \cdot \Phi'.\mu .\Lambda ]_{\mathrm{seq}}\)

CASE \(v = \operatorname{suc}(v')\)

For any sequence of atomic rensubs \(\vdash_{\mathrm{sf}} \bar{\chi} \operatorname{seq}(\hat{\Gamma} \to \hat{\Delta}) @ m\) we can compute as follows

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \bar {\chi}. \Phi^ {\prime}. \mu . \Lambda \right] _ {\text { seq }} = \operatorname{suc} \left(v ^ {\prime}\right) \left[ (\bar {\chi}. \Phi^ {\prime}) ^ {+}. \Lambda \right] _ {\text { seq }} \\ = v ^ {\prime} \left[ \pi . \Lambda \right] _ {\text {aren}} \left[ (\bar {\chi}. \Phi^ {\prime}) ^ {+}. \Lambda \right] _ {\text {seq}} \\ = v ^ {\prime} \left[ \bar {\chi}. \Phi^ {\prime}. \Lambda \right] _ {\text { seq }} \left[ \pi . \Lambda \right] _ {\text { aren }} \quad (\text { Lemma   10 }) \\ \end{array}
\]

By the induction hypothesis we know that \( v' \left[ \bar{\sigma} \cdot \Phi'. \Lambda \right]_{\mathrm{seq}} = v' \left[ \bar{\tau} \cdot \Phi'. \Lambda \right]_{\mathrm{seq}} \). Hence we can conclude that

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \bar {\sigma}. \Phi^ {\prime}. \mu . \Lambda \right] _ {\text { seq }} = v ^ {\prime} \left[ \bar {\sigma}. \Phi^ {\prime}. \Lambda \right] _ {\text { seq }} \left[ \pi . \Lambda \right] _ {\text { aren }} \\ = v ^ {\prime} \left[ \bar {\tau}. \Phi^ {\prime}. \Lambda \right] _ {\text { seq }} \left[ \pi . \Lambda \right] _ {\text { aren }} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \bar {\tau}. \Phi^ {\prime}. \mu . \Lambda \right] _ {\text { seq }}. \\ \end{array}
\]

◀

J. Ceulemans, A. Nuyts and D. Devriese

17

In particular, we have the following proof technique for observational equivalence of regular SFMTT substitutions.

▶ Proposition 12. Let $\vdash_{\mathrm{sf}} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m$ be two SFMTT substitutions and suppose that $v [\sigma . \Lambda]_{\mathrm{sub}} = v [\tau . \Lambda]_{\mathrm{sub}}$ for every lock telescope $\Lambda : \operatorname{LockTele}(m \to n)$ and every variable $\hat{\Delta} . \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ n$. Then $\sigma \approx^{\mathrm{obs}} \tau$.

Proof. Given the definition of observational equivalence for SFMTT substitutions, this follows immediately from Proposition 11 where both sequences consist of only atomic substitutions (so no renamings).$^{3}$

▶ Example 13. If we instantiate SFMTT on the trivial mode theory (by which we mean the terminal 2-category) then variables are non-modal De Bruijn indices and lock telescopes can be essentially ignored. In this setting, what Proposition 12 really says is that a substitution is uniquely determined, up to observational equivalence, by its action on De Bruijn indices. Since there exists exactly one De Bruijn index for every variable in the context, this means that we have an injection from substitutions, up to observational equivalence, to vectors of terms. In plain dependent type theory, substitutions are often defined as vectors of terms, or at least it is clear that they can be uniquely represented in this way. In other words, the aforementioned injection is actually a bijection.

Thus, it is natural to ask whether this idea carries over to general SFMTT. Could we define an SFMTT substitution $\vdash_{\mathrm{sf}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m$ as a thing that assigns, to every lock telescope $\Lambda : \operatorname{sTele}(m \to n)$ and every variable $\hat{\Delta} . \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ n$ a term $v [\sigma . \Lambda]_{\mathrm{sub}}$, perhaps satisfying some coherence conditions? Let us call such an assignment a substitution observation. Then Proposition 12 asserts that there is an injection from substitutions, up to observational equivalence, to substitution observations. We are asking if this injection is in fact a bijection.

The answer is no. Consider, as mode theory, the walking arrow, i.e. the 2-category with two modes $m$ and $n$, one modality $\mu : m \to n$, and only identity 2-cells. Then a substitution observation in a context of the form $\hat{\Delta} = (\cdot . \mathbb{1} . \widehat{\mathbf{\mu}}_{\mu})$ carries no information. Indeed, $\hat{\Delta}$ lives at mode $m$ and no lock telescope can get us back to $n$, which is where the only introduced variable lives. Thus, for any other context $\hat{\Gamma}$, there exists a unique substitution observation from $\hat{\Gamma}$ to $\hat{\Delta}$. However, if we and instantiate $\hat{\Gamma} = \cdot$, then there exists no substitution $\vdash_{\mathrm{sf}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m$. Indeed, since the only 2-cell with codomain $\mu$ is the identity, it is impossible to get rid of $\widehat{\mathbf{\mu}}_{\mu}$ in the domain of $\sigma$.

A cleaner argument can be given in the typed case. There, we could type $\hat{\Delta}$ as $\Delta = (\cdot . (\mathbb{1} \vdash \operatorname{Empty}) . \widehat{\mathbf{\mu}}_{\mu})$ and instantiate $\Gamma = (\cdot . \widehat{\mathbf{\mu}}_{\mu})$ and now $\widehat{\mathbf{\mu}}_{\mu}$ is no longer the problem, but we still cannot construct a substitution as there are no closed terms of the empty type Empty.

This situation is caused by an intentional underspecification of what $\widehat{\mathbf{\mu}}_{\mu}$ does. For a general model of WSMTT with said mode theory, it is not sound to allow mentions of the variable in context $\Delta$, and thus substitution observations to $\Delta$ are devoid of information. However, $\mu$ could be the identity modality, in which case a substitution from $\Gamma$ to $\Delta$ should really not exist, but there would be no qualms against mentioning the variable in context $\Delta$.

$^{3}$ Strictly speaking, we should define an embedding of regular SFMTT substitutions into mixed sequences of atomic rensubs and prove that their actions on SFMTT expressions correspond, but this is trivial.

18

A Substitution Algorithm for Multimode Type Theory: Technical Report

### 4.2 Preservation of Observational Equivalence of SFMTT Substitutions

Definition 2 tells us that two SFMTT substitutions are observationally equivalent if they yield equal results when applied to any expression. It is not immediately clear that this property is preserved by some of the operations that act on substitutions, such as \(\widehat{\mathbf{a}}_{\mu}\) or lifting. The following lemmas tell us that this is indeed the case.

▶ Lemma 14. Let \(\vdash_{\mathrm{sf}} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ n\) be two SFMTT substitutions and \(\mu : m \to n\) a modality. If \(\sigma \approx^{\mathrm{obs}} \tau\), then also \(\sigma \cdot \widehat{\mathbf{a}}_{\mu} \approx^{\mathrm{obs}} \tau \cdot \widehat{\mathbf{a}}_{\mu}\).

Proof. Take an arbitrary expression \(\hat{\Delta} \cdot \widehat{\mathbf{a}}_{\mu} \vdash_{\mathrm{sf}} t \exp @ m\). Then we can apply SF-EXPR-MOD-TM to see that \(\hat{\Delta} \vdash_{\mathrm{sf}} \operatorname{mod}_{\mu}(t) \exp @ n\). Hence, since \(\sigma \approx^{\mathrm{obs}} \tau\), the definition of observational equivalence tells us that \((\operatorname{mod}_{\mu}(t)) [\sigma]_{\mathrm{sub}} = (\operatorname{mod}_{\mu}(t)) [\tau]_{\mathrm{sub}}\). Since applying a lock to a regular SFMTT substitution amounts to applying the lock to all its constituent atomic substitutions, it follows that \((\operatorname{mod}_{\mu}(t)) [\sigma]_{\mathrm{sub}} = \operatorname{mod}_{\mu}(t [\sigma, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}})\) (and similarly for \(\tau\)). We therefore have that \(\operatorname{mod}_{\mu}(t [\sigma, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}}) = \operatorname{mod}_{\mu}(t [\tau, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}})\) and by injectivity of expression constructors it follows that \(t [\sigma, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}} = t [\tau, \widehat{\mathbf{a}}_{\mu}]_{\mathrm{sub}}\). As this holds for arbitrary \(t\), we have proven that \(\sigma \cdot \widehat{\mathbf{a}}_{\mu} \approx^{\mathrm{obs}} \tau \cdot \widehat{\mathbf{a}}_{\mu}\).

▶ Lemma 15. Let \(\vdash_{\mathrm{sf}} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) be two SFMTT substitutions. If \(\sigma \approx^{\mathrm{obs}} \tau\), then also \(\sigma^{+} \approx^{\mathrm{obs}} \tau^{+}\).

Proof. We can apply the same reasoning as in the proof of Lemma 14, but with the expression constructor \(\lambda^{\mu}(\_)\) instead of \(\mathrm{mod}_{\mu}(\_)\).

▶ Corollary 16. If  \( \vdash_{sf} \sigma, \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  are two SFMTT substitutions and  \( \Phi : s\text{Tele}(m \to n) \)  is a scoping telescope, then  \( \sigma \approx^{obs} \tau \)  implies  \( \sigma \cdot \Phi \approx^{obs} \tau \cdot \Phi \) .

We note that the converse of Proposition 3 immediately follows from Corollary 16. Furthermore, if we restrict the scoping telescopes in this corollary to lock telescopes, the converse of Proposition 12 can also be derived.

### 4.3 Relating WSMTT and SFMTT Lifting

▶ Lemma 17. Given a WSMTT substitution \(\vdash_{\mathrm{ws}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\), we have \([\sigma^{+}] \approx^{\mathrm{obs}} [\sigma]^{+}\).

Proof. First of all, we can calculate that

\[
\begin{array}{l} [ [ \sigma^ {+} ] ] = [ [ (\sigma \circ \pi). \mathbf {v} _ {0} ] ] \quad \text {(Definition of } ^ {+}, \text { Equation(1))} \\ = \llbracket \sigma \circ \pi \rrbracket^ {+} * (\mathrm{id} ^ {\mathrm{a}}. \llbracket \mathbf {v} _ {0} \rrbracket) \quad (\text {Definition of} [ \llbracket ]) \\ = \left(\llbracket \sigma \rrbracket + + \llbracket \pi \rrbracket\right) ^ {+} * \left(\mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}}\right) \quad (\text {Definition of} [ \llbracket ]) \\ = \llbracket \sigma \rrbracket^ {+} * \pi^ {+} * \left(\mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}}\right). \\ \end{array}
\]

The last step combines the definition of \(\llbracket \pi \rrbracket\) with the fact that lifting a regular substitution amounts to lifting all of its constituent substitutions. By the definition of \(\approx^{\mathrm{obs}}\) it now suffices to prove that \(t[\pi^{+}]_{\mathrm{asub}}\left[\mathrm{id}^{\mathrm{a}}.\mathbf{v}_{0}^{1_{\mu}}\right]_{\mathrm{asub}} = t\) for every expression \(\hat{\Gamma}.\mu \vdash_{\mathrm{sf}}t\) expr \(@ m\). For this we use Proposition 11, so we have to show that \(v[\pi^{+}.\Lambda ]_{\mathrm{asub}}\left[\left(\mathrm{id}^{\mathrm{a}}.\mathbf{v}_{0}^{1_{\mu}}\right).\Lambda \right]_{\mathrm{asub}} = v\) for every lock telescope \(\Lambda :\operatorname {LockTele}(m\to n)\) and every variable \(\hat{\Gamma}.\mu .\Lambda \vdash_{\mathrm{sf}}v\) var \(@ n\). We distinguish between two cases for the variable \(v\).

J. Ceulemans, A. Nuyts and D. Devriese

19

CASE \(v = \mathbf{v}_0^\alpha\)

We can now compute that

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi^ {+}. \Lambda \right] _ {\text { asub }} \left[ \left(\mathrm{id} ^ {2}. \mathbf {v} _ {0} ^ {1 _ {\mu}}\right). \Lambda \right] _ {\text { asub }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \pi^ {+} \right] _ {\text { asub }} ^ {\Lambda} \left[ \mathrm{id} ^ {2}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text { asub }} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \mathrm{id} ^ {2}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text { asub }} ^ {\Lambda} \tag {Lemma6} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \alpha ] _ {2 - \text { cell }} ^ {\mathbf {0} _ {\mu} \Rightarrow \Lambda} \quad (\text { Equations   (19)   and   (26)) } \\ = \mathbf {v} _ {0} ^ {\alpha}. \\ \end{array}
\]

CASE \(v = \operatorname{suc}(v')\)

Then we have that

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi^ {+}. \Lambda \right] _ {\text { asub }} \left[ \left(\mathrm{id} ^ {2}. \mathbf {v} _ {0} ^ {1 _ {\mu}}\right). \Lambda \right] _ {\text { asub }} \\ = v ^ {\prime} [ \pi ] _ {\text { asub }} ^ {\Lambda} [ \pi ] _ {\text { asub }} ^ {\Lambda} \left[ \mathrm{id} ^ {2}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text { asub }} ^ {\Lambda} \tag {Lemma6} \\ = \operatorname{suc} \left(\operatorname{suc} \left(v ^ {\prime}\right)\right) \left[ \mathrm{id} ^ {2}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \right] _ {\text { asub }} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \mathrm{id} ^ {2} \right] _ {\text { asub }} ^ {\Lambda} \quad (\text { Equation   (27) }) \\ = \operatorname{suc} \left(v ^ {\prime}\right). \\ \end{array}
\]

### 4.4 Properties of Key Renamings

In order to prove the completeness of the substitution algorithm, we need a counterpart in SFMTT for every rule in Figure 4 relating to key substitutions. That is exactly what will be covered in this section, but we start with two auxiliary results.

▶ Lemma 18. Let \(\Lambda : \text{LockTele}(m \to n)\) and \(\Theta, \Psi : \text{LockTele}(n \to o)\) and \(\Omega : \text{LockTele}(o \to p)\) be lock telescopes, \(\alpha \in \text{locks}(\Theta) \Rightarrow \text{locks}(\Psi)\) a 2-cell, and \(\hat{\Gamma}. \Lambda. \Theta. \Omega \vdash_{\text{sf}} v \text{ var } @p\) a variable. Then \(\text{suc}(v) \left[ \mathbf{Q}_{\hat{\Gamma}. \mu. \Lambda}^{\alpha \in \Theta \Rightarrow \Psi}. \Omega \right]_{\text{aren}} = \text{suc}\left(v \left[ \mathbf{Q}_{\hat{\Gamma}. \Lambda}^{\alpha \in \Theta \Rightarrow \Psi}. \Omega \right]_{\text{aren}}\right)\).

Proof. We can compute that

\[
\begin{array}{l} \operatorname{suc} (v) \left[ \mathbf {Q} _ {\hat {\Gamma}. \mu . \Lambda} ^ {\alpha \in \Theta \Rightarrow \Psi}. \Omega \right] _ {\text {aren}} = \operatorname{suc} (v) \left[ \mathbf {Q} _ {\hat {\Gamma}. \mu . \Lambda} ^ {\alpha \in \Theta \Rightarrow \Psi} \right] _ {\text {aren}} ^ {\Omega} \\ = \operatorname{suc} (v) \left[ \alpha * 1 _ {\text {locks} (\Omega)} \right] _ {2 - \text {cell}} ^ {\Theta . \Omega \Rightarrow \Psi . \Omega} \quad (\text {Equation (19)}) \\ = \operatorname{suc} \left(v \left[ \alpha * 1 _ {\text {locks} (\Omega)} \right] _ {2 - \text {cell}} ^ {\Theta . \Omega \Rightarrow \Psi . \Omega}\right) \quad (\text {Equation (15)}) \\ = \operatorname{suc} \left(v \left[ \mathbf {Q} _ {\hat {\Gamma}. \Lambda} ^ {\alpha \in \Theta \Rightarrow \Psi}. \Omega \right] _ {\text {aren}}\right) \tag {Equation(19)} \\ \end{array}
\]

▶ Lemma 19. Key renamings commute with  \( \pi \)  renamings. In other words, we have  \( t\left[\mathbf{Q}_{\hat{\Gamma}}^{\alpha\in\Lambda\Rightarrow\Theta}\right]_{\text{aren}}\left[\pi.\Theta\right]_{\text{aren}}=t\left[\pi.\Lambda\right]_{\text{aren}}\left[\mathbf{Q}_{\hat{\Gamma}.\mu}^{\alpha\in\Lambda\Rightarrow\Theta}\right]_{\text{aren}} \)  for every expression  \( \hat{\Gamma}.\Lambda\vdash_{sf}t\exp@m \) .

Proof. We use Proposition 11, so we take an arbitrary lock telescope \(\Psi\) and a variable

20

A Substitution Algorithm for Multimode Type Theory: Technical Report

\(\hat{\Gamma}.\Lambda.\Psi\vdash_{\mathrm{sf}}v\operatorname{var}\circledast n.\) Then we can compute that

\[
\begin{array}{l} v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} [ \pi . \Theta ] _ {\text {aren}} ^ {\Psi} = \operatorname{suc} \left(v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi}\right) \\ = \operatorname{suc} (v) \left[ \mathbf {Q} _ {\hat {\Gamma}, \mu} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \tag {Lemma18} \\ = v \left[ \pi . \Lambda \right] _ {\text {aren}} ^ {\Psi} \left[ \mathbf {Q} _ {\hat {\Gamma}, \mu} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi}. \\ \end{array}
\]

▶ Proposition 20. For every lock telescope \(\Lambda: \text{LockTele}(m \to n)\) and SFMTT expression \(\hat{\Gamma} \cdot \Lambda \vdash_{\text{sf}} t \text{ expr } @n\) we have that \(t \left[ \mathbf{Q}_{\hat{\Gamma}}^{1_{\text{locks}(\Lambda)} \in \Lambda \Rightarrow \Lambda} \right]_{\text{aren}} = t\).

Proof. We use Proposition 11, so we have to show that \( v \left[ \mathbf{Q}_{\hat{\Gamma}}^{1_{\mathrm{locks}(\Lambda)} \in \Lambda \Rightarrow \Lambda} \cdot \Theta \right]_{\mathrm{aren}} = v \) for all lock telescopes \( \Theta : \mathrm{LockTele}(n \to o) \) and variables \( \hat{\Gamma} \cdot \Lambda \cdot \Theta \vdash_{\mathrm{sf}} v \operatorname{var} @ o \). This proof proceeds by induction on the variable \( v \).

CASE \(v = \mathbf{v}_0^\alpha\) with \(\hat{\Gamma} = \hat{\Gamma}'\cdot \mu .\Psi\) We have

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \mu , \Psi} ^ {1 _ {\text { locks } (\Lambda)} \in \Lambda \Rightarrow \Lambda}. \Theta \right] _ {\text { aren }} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \mu , \Psi} ^ {1 _ {\text { locks } (\Lambda)} \in \Lambda \Rightarrow \Lambda} \right] _ {\text { aren }} ^ {\Theta} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ 1 _ {\text { locks } (\Lambda)} \star 1 _ {\text { locks } (\Theta)} \right] _ {2 - \text { cell }} ^ {\Lambda . \Theta \Rightarrow \Lambda . \Theta} \quad \tag {Equation(19)} \\ = \mathbf {v} _ {0} ^ {(1 _ {\text { locks } (\Psi)} \star (1 _ {\text { locks } (\Lambda)} \star 1 _ {\text { locks } (\Theta)})) \circ \alpha} \quad \tag {Equation(14)} \\ = \mathbf {v} _ {0} ^ {\alpha}. \quad (\text { Strict   2 - category   laws }) \\ \end{array}
\]

CASE \(v = \operatorname{suc}(v')\) with \(\hat{\Gamma} = \hat{\Gamma}'\cdot \mu .\Psi\) Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \mu , \Psi} ^ {1 _ {\text { locks } (\Lambda)} \in \Lambda \Rightarrow \Lambda}. \Theta \right] _ {\text { aren }} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \Psi} ^ {1 _ {\text { locks } (\Lambda)} \in \Lambda \Rightarrow \Lambda}. \Theta \right] _ {\text { aren }}\right) \tag {Lemma18} \\ = \operatorname{suc} \left(v ^ {\prime}\right). \quad (\text { Induction   hypothesis }) \\ \end{array}
\]

▶ Proposition 21. If \(\Lambda_1, \Lambda_2, \Lambda_3: \text{LockTele}(m \to n)\) are lock telescopes, \(\alpha \in \text{locks}(\Lambda_1) \Rightarrow \text{locks}(\Lambda_2)\) and \(\beta \in \text{locks}(\Lambda_2) \Rightarrow \text{locks}(\Lambda_3)\) are 2-cells and \(\hat{\Gamma} \cdot \Lambda_1 \vdash_{\text{sf}} t \text{ expr } @n\) is an expression, then \(t \left[ \mathbf{Q}_{\hat{\Gamma}}^{\beta \circ \alpha \in \Lambda_1 \Rightarrow \Lambda_3} \right]_{\text{aren}} = t \left[ \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda_1 \Rightarrow \Lambda_2} \right]_{\text{aren}} \left[ \mathbf{Q}_{\hat{\Gamma}}^{\beta \in \Lambda_2 \Rightarrow \Lambda_3} \right]_{\text{aren}}\).

Proof. The proof is similar to that of Proposition 20, so we use Proposition 11 and take an arbitrary lock telescope \(\Theta : \text{LockTele}(n \to o)\) and variable \(\hat{\Gamma} \cdot \Lambda_1 \cdot \Theta \vdash_{\text{sf}} v \text{ var } @o\). Then we prove that \(v \left[ \mathbf{Q}_{\hat{\Gamma}}^{\beta \circ \alpha \in \Lambda_1 \Rightarrow \Lambda_2} \right]_{\text{aren}}^{\Theta} = v \left[ \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda_1 \Rightarrow \Lambda_2} \right]_{\text{aren}}^{\Theta} \left[ \mathbf{Q}_{\hat{\Gamma}}^{\beta \in \Lambda_2 \Rightarrow \Lambda_3} \right]_{\text{aren}}^{\Theta}\) by induction on \(v\).

CASE \(v = \mathbf{v}_0^\gamma\) with \(\hat{\Gamma} = \hat{\Gamma}'\cdot \mu .\Psi\) and \(\gamma \in \mu \Rightarrow \mathrm{locks}(\Psi .\Lambda_1.\Theta)\)

J. Ceulemans, A. Nuyts and D. Devriese

21

Now we have

$$\begin{array}{l} \mathbf{v}_{0}^{\gamma}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \mu, \Psi}^{\beta \circ \alpha \in \Lambda_{1} \Rightarrow \Lambda_{3}}\right]_{\text {aren}}^{\Theta} \\ =\mathbf{v}_{0}^{\gamma}\left[(\beta \circ \alpha) \star 1_{\text {locks }(\Theta)}\right]_{2 - \text {cell}}^{\Lambda_{1}, \Theta \Rightarrow \Lambda_{3}, \Theta} \quad \text {(Equation (19))} \\ =\mathbf{v}_{0}^{\left(1_{\text {locks }(\Psi)} \star\left((\beta \circ \alpha) \star 1_{\text {locks }(\Theta)}\right)\right) \circ \gamma} \quad \text {(Equation (14))} \\ =\mathbf{v}_{0}^{\left(1_{\text {locks }(\Psi)} \star\left(\beta \star 1_{\text {locks }(\Theta)}\right)\right) \circ\left(1_{\text {locks }(\Psi)} \star\left(\alpha \star 1_{\text {locks }(\Theta)}\right)\right) \circ \gamma} \quad \text {(Strict 2-category laws)} \\ =\mathbf{v}_{0}^{\left(1_{\text {locks }(\Psi)} \star\left(\alpha \star 1_{\text {locks }(\Theta)}\right)\right) \circ \gamma}\left[\beta\right]_{2 - \text {cell}}^{\Lambda_{2}, \Theta \Rightarrow \Lambda_{3}, \Theta} \quad \text {(Equation (14))} \\ =\mathbf{v}_{0}^{\gamma}\left[\alpha\right]_{2 - \text {cell}}^{\Lambda_{1}, \Theta \Rightarrow \Lambda_{2}, \Theta}\left[\beta\right]_{2 - \text {cell}}^{\Lambda_{2}, \Theta \Rightarrow \Lambda_{3}, \Theta} \quad \text {(Equation (14))} \\ =\mathbf{v}_{0}^{\gamma}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\alpha \in \Lambda_{1} \Rightarrow \Lambda_{2}}\right]_{\text {aren}}^{\Theta}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\beta \in \Lambda_{2} \Rightarrow \Lambda_{3}}\right]_{\text {aren}}^{\Theta}. \quad \text {(Equation (19))} \end{array}$$

CASE $v = \operatorname{suc}(v')$ with $\hat{\Gamma} = \hat{\Gamma}' \cdot \mu \cdot \Psi$

Similarly as in the proof of Proposition 20 we compute

$$\begin{array}{l} \operatorname{suc}\left(v^{\prime}\right)\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \mu, \Psi}^{\beta \circ \alpha \in \Lambda_{1} \Rightarrow \Lambda_{3}}\right]_{\text {aren}}^{\Theta} \\ =\operatorname{suc}\left(v^{\prime}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \Psi}^{\beta \circ \alpha \in \Lambda_{1} \Rightarrow \Lambda_{3}}\right]_{\text {aren}}^{\Theta}\right) \quad \text {(Lemma 18)} \\ =\operatorname{suc}\left(v^{\prime}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \Psi}^{\alpha \in \Lambda_{1} \Rightarrow \Lambda_{2}}\right]_{\text {aren}}^{\Theta}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \Psi}^{\beta \in \Lambda_{2} \Rightarrow \Lambda_{3}}\right]_{\text {aren}}^{\Theta}\right) \quad \text {(Induction hypothesis)} \\ =\operatorname{suc}\left(v^{\prime}\right)\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \mu, \Psi}^{\alpha \in \Lambda_{1} \Rightarrow \Lambda_{2}}\right]_{\text {aren}}^{\Theta}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}^{\prime}, \mu, \Psi}^{\beta \in \Lambda_{2} \Rightarrow \Lambda_{3}}\right]_{\text {aren}}^{\Theta}. \quad \text {(Lemma 18)} \end{array}$$

▶ Proposition 22. Given lock telescopes $\Lambda_{1}, \Lambda_{2}: \operatorname{LockTele}(m \to n)$, $\Theta_{1}, \Theta_{2}: \operatorname{LockTele}(n \to o)$ and 2-cells $\beta \in \operatorname{locks}(\Lambda_{1}) \Rightarrow \operatorname{locks}(\Lambda_{2})$ and $\alpha \in \operatorname{locks}(\Theta_{1}) \Rightarrow \operatorname{locks}(\Theta_{2})$, the following two equations hold for any expression $\hat{\Gamma} \cdot \Lambda_{1} \cdot \Theta_{1} \vdash_{\mathrm{sf}} t \operatorname{expr} @ o$

$$\begin{array}{l} t\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\beta \star \alpha \in \Lambda_{1}, \Theta_{1} \Rightarrow \Lambda_{2}, \Theta_{2}}\right]_{\text {aren}}=t\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\beta \in \Lambda_{1} \Rightarrow \Lambda_{2}} \cdot \Theta_{1}\right]_{\text {aren}}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}, \Lambda_{2}}^{\alpha \in \Theta_{1} \Rightarrow \Theta_{2}}\right]_{\text {aren}} \\ =t\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}, \Lambda_{1}}^{\alpha \in \Theta_{1} \Rightarrow \Theta_{2}}\right]_{\text {aren}}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\beta \in \Lambda_{1} \Rightarrow \Lambda_{2}} \cdot \Theta_{2}\right]_{\text {aren}}. \end{array}$$

Proof. We only prove the first equality, the second one can be proved similarly. Making use of Proposition 11, we introduce a lock telescope $\Psi: \operatorname{LockTele}(o \to p)$ and a variable $\hat{\Gamma} \cdot \Lambda_{1} \cdot \Theta_{1} \cdot \Psi \vdash_{\mathrm{sf}} v \operatorname{var} @ p$, and then we need to show that $v\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\beta \star \alpha \in \Lambda_{1}, \Theta_{1} \Rightarrow \Lambda_{2}, \Theta_{2}}\right]_{\text {aren}}^{\Psi}=t\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}}^{\beta \in \Lambda_{1} \Rightarrow \Lambda_{2}} \cdot \Theta_{1}\right]_{\text {aren}}^{\Psi}\left[\boldsymbol{\mathcal{Q}}_{\hat{\Gamma}, \Lambda_{2}}^{\alpha \in \Theta_{1} \Rightarrow \Theta_{2}}\right]_{\text {aren}}^{\Psi}$. This proof proceeds by induction on $v$.

CASE $v = \mathbf{v}_{0}^{\gamma}$ with $\hat{\Gamma} = \hat{\Gamma}' \cdot \mu \cdot \Omega$ and $\gamma \in \mu \Rightarrow \operatorname{locks}(\Omega \cdot \Lambda_{1} \cdot \Theta_{1} \cdot \Psi)$

22

A Substitution Algorithm for Multimode Type Theory: Technical Report

Now we compute that

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\gamma} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma} ^ {\prime}, \mu , \Omega} ^ {\beta \star \alpha \in \Lambda_ {1}, \Theta_ {1} \Rightarrow \Lambda_ {2}, \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi} \\ = \mathbf {v} _ {0} ^ {\gamma} \left[ (\beta \star \alpha) \star 1 _ {\text {locks} (\Psi)} \right] _ {2 - \text {cell}} ^ {\Lambda_ {1}, \Theta_ {1}, \Psi \Rightarrow \Lambda_ {2}, \Theta_ {2}, \Psi} (Equation(19)) \\ = \mathbf {v} _ {0} ^ {\left(1 _ {\text {locks} (\Omega)} \star (\beta \star \alpha) \star 1 _ {\text {locks} (\Psi)}\right) \circ \gamma} (Equation(14)) \\ = \mathbf {v} _ {0} ^ {\left(1 _ {\text {locks} (\Omega)} \star \left(1 _ {\text {locks} (\Lambda_ {2})} \star \alpha\right) \star 1 _ {\text {locks} (\Psi)}\right) \circ \left(1 _ {\text {locks} (\Omega)} \star \left(\beta \star 1 _ {\text {locks} (\Theta_ {1})}\right) \star 1 _ {\text {locks} (\Psi)}\right) \circ \gamma} (Strict2-category laws) \\ = \mathbf {v} _ {0} ^ {\left(1 _ {\text {locks} (\Omega , \Lambda_ {2})} \star (\alpha \star 1 _ {\text {locks} (\Psi)})) \circ (1 _ {\text {locks} (\Omega)} \star (\beta \star 1 _ {\text {locks} (\Theta_ {1}, \Psi)})) \circ \gamma \right.} (Strict2-category laws) \\ = \mathbf {v} _ {0} ^ {\gamma} \left[ \beta \star 1 _ {\text {locks} (\Theta_ {1}, \Psi)} \right] _ {2 - \text {cell}} ^ {\Lambda_ {1}, \Theta_ {1}, \Psi \Rightarrow \Lambda_ {2}, \Theta_ {1}, \Psi} \left[ \alpha \star 1 _ {\text {locks} (\Psi)} \right] _ {2 - \text {cell}} ^ {\Theta_ {1}, \Psi \Rightarrow \Theta_ {2}, \Psi} (Equation(14)) \\ = \mathbf {v} _ {0} ^ {\gamma} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}} ^ {\beta \in \Lambda_ {1} \Rightarrow \Lambda_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Theta_ {1}, \Psi} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}, \Lambda_ {2}} ^ {\alpha \in \Theta_ {1} \Rightarrow \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi} (Equation(19)) \\ = \mathbf {v} _ {0} ^ {\gamma} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}} ^ {\beta \in \Lambda_ {1} \Rightarrow \Lambda_ {2}}, \Theta_ {1} \end{array} \right] _ {\text {aren}} ^ {\Psi} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}, \Lambda_ {2}} ^ {\alpha \in \Theta_ {1} \Rightarrow \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi} \\ \end{array}
\]

CASE \( v = \operatorname{suc}(v') \) with \( \hat{\Gamma} = \hat{\Gamma}' \cdot \mu \cdot \Omega \)

In this case we have

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma} ^ {\prime}, \mu , \Omega} ^ {\beta \star \alpha \in \Lambda_ {1}, \Theta_ {1} \Rightarrow \Lambda_ {2}, \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma} ^ {\prime}, \Omega} ^ {\beta \star \alpha \in \Lambda_ {1}, \Theta_ {1} \Rightarrow \Lambda_ {2}, \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi}\right) (Lemma18) \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}} ^ {\beta \in \Lambda_ {1} \Rightarrow \Lambda_ {2}}, \Theta_ {1} \end{array} \right] _ {\text {aren}} ^ {\Psi} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}, \Lambda_ {2}} ^ {\alpha \in \Theta_ {1} \Rightarrow \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi}\right) (Inductionhypothesis) \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}} ^ {\beta \in \Lambda_ {1} \Rightarrow \Lambda_ {2}}, \Theta_ {1} \end{array} \right] _ {\text {aren}} ^ {\Psi} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}, \Lambda_ {2}} ^ {\alpha \in \Theta_ {1} \Rightarrow \Theta_ {2}} \end{array} \right] _ {\text {aren}} ^ {\Psi}. (Lemma18) \\ \end{array}
\]

▶ Proposition 23. Key renamings are natural. In other words, given lock telescopes \(\Lambda, \Theta: \text{LockTele}(m \to n)\), a 2-cell \(\alpha \in \text{locks}(\Lambda) \Rightarrow \text{locks}(\Theta)\), a substitution \(\vdash_{\text{sf}} \sigma \text{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) and an expression \(\hat{\Delta}. \Lambda \vdash_{\text{sf}} t \text{expr} @ n\), we have that \(t \left[ \begin{array}{c} \mathbf{Q}_{\hat{\Delta}}^{\alpha \in \Lambda \Rightarrow \Theta} \\ \end{array} \right]_{\text{aren}} [\sigma. \Theta]_{\text{sub}} = t [\sigma. \Lambda]_{\text{sub}} \left[ \begin{array}{c} \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta} \\ \end{array} \right]_{\text{aren}}\).

Proof. It suffices to prove this lemma for an atomic substitution \(\sigma\), for which we use Proposition 11. Hence for an arbitrary lock telescope \(\Psi: \text{LockTele}(n \to o)\) and variable \(\hat{\Delta}. \Lambda. \Psi \vdash_{\text{sf}} v \text{ var } @o\) we show that \(v \left[ \begin{array}{c} \mathbf{Q}_{\hat{\Delta}}^{\alpha \in \Lambda \Rightarrow \Theta} \\ \end{array} \right]_{\text{aren}}^{\Psi} [\sigma]_{\text{asub}}^{\Theta. \Psi} = v [\sigma]_{\text{asub}}^{\Lambda. \Psi} \left[ \begin{array}{c} \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta} \\ \end{array} \right]_{\text{aren}}^{\Psi}\). We do this by induction on \(\sigma\).

CASE \(\sigma = !\) (SF-ARENSUB-EMPTY)

Now \(\hat{\Delta}\) is the empty scoping context. Since there are no variables in \(\cdot, \Lambda, \Psi\), this case is trivial.

CASE \(\sigma = \mathrm{id}^{\mathrm{a}}\) (SF-ARENSUB-ID)

Since the action of  \( id^{a} \)  on variables is the identity, this case is also trivial.

CASE \(\sigma = \text{weaken}(\sigma')\) with \(\hat{\Gamma} = \hat{\Gamma}'\). \(\mu\) and \(\vdash_{\text{sf}} \sigma'\) asub(\(\hat{\Gamma}' \to \hat{\Delta}\)) @ \(m\) (SF-ARENSUB-WEAKEN)

J. Ceulemans, A. Nuyts and D. Devriese

23

We have

\[
\begin{array}{l} v \left[ \mathbf {Q} _ {\tilde {\Delta}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} [ \text {weaken} (\sigma^ {\prime}) ] _ {\text {asub}} ^ {\Theta , \Psi} \\ = v \left[ \mathbf {Q} _ {\tilde {\Delta}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\Theta , \Psi} \left[ \pi \right] _ {\text {aren}} ^ {\Theta , \Psi} (Equation(23)) \\ = v \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\Lambda , \Psi} \left[ \mathbf {Q} _ {\Gamma^ {\prime}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \pi \right] _ {\text {aren}} ^ {\Theta , \Psi} (Inductionhypothesis) \\ = v \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\Lambda , \Psi} [ \pi ] _ {\text {aren}} ^ {\Lambda , \Psi} \left[ \mathbf {Q} _ {\Gamma^ {\prime}, \mu} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} (Lemma19) \\ = v \left[ \text { weaken } (\sigma^ {\prime}) \right] _ {\text { asub }} ^ {\Lambda , \Psi} \left[ \mathbf {Q} _ {\Gamma^ {\prime}, \mu} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text { aren }} ^ {\Psi}. (Equation(23)) \\ \end{array}
\]

CASE \(\sigma = \sigma'\). \(\widehat{\mathbf{B}}_{\mu}\) (SF-ARENSUB-LOCK)

We compute that

\[
\begin{array}{l} v \left[ \mathbf {Q} _ {\tilde {\Delta}, \mathbf {B} _ {\mu}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime}, \mathbf {B} _ {\mu} \right] _ {\text {asub}} ^ {\Theta , \Psi} \\ = v \left[ \mathbf {Q} _ {\tilde {\Delta}} ^ {1 _ {\mu} \in \mathbf {B} _ {\mu} \Rightarrow \mathbf {B} _ {\mu}}. \Lambda \right] _ {\text {aren}} ^ {\Psi} \left[ \mathbf {Q} _ {\tilde {\Delta}, \mathbf {B} _ {\mu}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime}, \mathbf {B} _ {\mu} \right] _ {\text {asub}} ^ {\Theta , \Psi} \\ (Proposition20) \\ = v \left[ \mathbf {Q} _ {\tilde {\Delta}} ^ {1 _ {\mu} * \alpha \in \mathbf {B} _ {\mu}. \Lambda \Rightarrow \mathbf {B} _ {\mu}. \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\mathbf {B} _ {\mu}. \Theta . \Psi} (Proposition22andEquation(24)) \\ = v \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\boldsymbol {\Theta} _ {\mu}, \Lambda , \Psi} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {1 _ {\mu} * \alpha \in \boldsymbol {\Theta} _ {\mu}, \Lambda \Rightarrow \boldsymbol {\Theta} _ {\mu}, \Theta} \right] _ {\text {aren}} ^ {\Psi} (Inductionhypothesis) \\ = v \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\boldsymbol {\Theta} _ {\mu}, \Lambda , \Psi} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} (Propositions20and22) \\ = v \left[ \sigma^ {\prime}. \widehat {\mathbf {B}} _ {\mu} \right] _ {\text {asub}} ^ {\Lambda , \Psi} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi}. (Equation(24)) \\ \end{array}
\]

CASE \(\sigma = \mathbf{Q}_{\tilde{\Gamma}}^{\beta \in \Upsilon \Rightarrow \Omega}\) (SF-ARENSUB-KEY)

This case follows directly from Proposition 22.

CASE \(\sigma = \sigma'.t\) with \(\tilde{\Delta} = \tilde{\Delta}'\). \(\mu\) (SF-ASUB-EXTEND)

We distinguish two cases for the variable v.

CASE \( v = \mathbf{v}_0^\beta \) with \( \beta \in \mu \Rightarrow \text{locks}(\Lambda, \Psi) \)

Now we have

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\beta} \left[ \mathbf {Q} _ {\tilde {\Delta} ^ {\prime}, \mu} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime}, t \right] _ {\text {asub}} ^ {\Theta , \Psi} \\ = \mathbf {v} _ {0} ^ {\left(\alpha * 1 _ {\text {locks} (\Psi)}\right) \circ \beta} \left[ \sigma^ {\prime}, t \right] _ {\text {asub}} ^ {\Theta , \Psi} (Equations(14)and(19)) \\ = t \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {(\alpha * 1 _ {\text {locks} (\Psi)}) \circ \beta \in \mathbf {B} _ {\mu} \Rightarrow \Theta . \Psi} \right] _ {\text {aren}} (Equation(26)) \\ = t \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\beta \in \mathbf {B} _ {\mu} \Rightarrow \Lambda , \Psi} \right] _ {\text {aren}} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha * 1 _ {\text {locks} (\Psi)} \in \Lambda , \Psi \Rightarrow \Theta , \Psi} \right] _ {\text {aren}} (Proposition21) \\ = t \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\beta \in \mathbf {B} _ {\mu} \Rightarrow \Lambda , \Psi} \right] _ {\text {aren}} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} (Propositions20and22) \\ = \mathbf {v} _ {0} ^ {\beta} \left[ \sigma^ {\prime}, t \right] _ {\text {aren}} ^ {\Lambda , \Psi} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi}. (Equation(26)) \\ \end{array}
\]

24

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \( v = \operatorname{suc}(v') \)

In this case we get that

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \mathbf {Q} _ {\tilde {\Delta} ^ {\prime}, \mu} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime}. t \right] _ {\text {asub}} ^ {\Theta . \Psi} \\ = \operatorname{suc} \left(v ^ {\prime} \left[ \mathbf {Q} _ {\tilde {\Delta} ^ {\prime}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi}\right) \left[ \sigma^ {\prime}. t \right] _ {\text {asub}} ^ {\Theta . \Psi} (Lemma18) \\ = v ^ {\prime} \left[ \mathbf {Q} _ {\tilde {\Delta} ^ {\prime}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\Theta . \Psi} (Equation(27)) \\ = v ^ {\prime} \left[ \sigma^ {\prime} \right] _ {\text {asub}} ^ {\Lambda . \Psi} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi} (Inductionhypothesis) \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma^ {\prime}. t \right] _ {\text {asub}} ^ {\Lambda . \Psi} \left[ \mathbf {Q} _ {\tilde {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi}. (Equation(27)) \\ \end{array}
\]

### 4.5 Proof of Theorem 1

We can now prove a more general result that includes substitutions (and which can hence be proved by induction) and of which Theorem 1 is a consequence.

Theorem 24 (Completeness). Given two \(\sigma\)-equivalent WSMTT expressions \(\hat{\Gamma} \vdash_{\mathrm{ws}} t \equiv^{\sigma} s \exp @ m\), we have that \([t] = [s]\). Furthermore, given two \(\sigma\)-equivalent WSMTT substitutions \(\vdash_{\mathrm{ws}} \sigma \equiv^{\sigma} \tau \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\), we have that \([\sigma] \approx^{\mathrm{obs}} [\tau]\).

Proof. We proceed by induction on a derivation of the  \( \sigma \) -equivalence judgement. To do this, we discuss all the rules from Figure 4 and provide an outline of the argument for all the rules that are omitted in that figure.

For the rules expressing that \(\sigma\)-equivalence is an equivalence relation (e.g. WSMTT-EQ-EXPR-REFL), we immediately get the desired result since equality of SFMTT expressions and \(\approx^{\mathrm{obs}}\) are also equivalence relations.
CASE \(\vdash_{\mathrm{ws}}\sigma \circ \mathrm{id}\equiv^{\sigma}\sigma \operatorname {sub}(\hat{\Gamma}\to \hat{\Delta})@m\) (WSMTT-EQ-SUB-ID-RIGHT)

We have that \(\llbracket \sigma \circ \mathrm{id}\rrbracket = \llbracket \sigma \rrbracket + + \llbracket \mathrm{id}\rrbracket\) which is equal to \(\llbracket \sigma \rrbracket\) since \(\llbracket \mathrm{id}\rrbracket\) is the empty list of atomic substitutions (see the definition of \(\llbracket \_ \rrbracket\) in Section 3.3). This immediately proves that \(\llbracket \sigma \circ \mathrm{id}\rrbracket \approx^{\mathrm{obs}}\llbracket \sigma \rrbracket\). The other two category laws follow similarly from the monoid laws of list concatenation.

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} t[\mathrm{id}]_{\mathrm{ws}} \equiv^{\sigma} t \exp @ m\) (WSMTT-EQ-EXPR-SUB-ID)

The definition of \(\llbracket \_ \rrbracket\) tells us that \(\llbracket t[\mathrm{id}]_{\mathrm{ws}}\rrbracket = \llbracket t\rrbracket [\llbracket \mathrm{id}\rrbracket]_{\mathrm{sub}}\). Since \(\llbracket \mathrm{id}\rrbracket\) is the empty list of atomic substitutions, we can directly see that this expression is equal to \(\llbracket t\rrbracket\).

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} t[\sigma \circ \tau]_{\mathrm{ws}} \equiv^{\sigma} t[\sigma]_{\mathrm{ws}}[\tau]_{\mathrm{ws}} \exp @ m\) (WSMTT-EQ-EXPR-SUB-COMPOSE)

For the left-hand side we get that \(\llbracket t[\sigma \circ \tau]_{\mathrm{ws}}\rrbracket = \llbracket t\rrbracket [\llbracket \sigma \rrbracket + + \llbracket \tau \rrbracket]_{\mathrm{sub}}\), whereas for the right-hand side we have \(\llbracket t[\sigma]_{\mathrm{ws}}[\tau]_{\mathrm{ws}}\rrbracket = \llbracket t\rrbracket [\llbracket \sigma \rrbracket]_{\mathrm{sub}}[\llbracket \tau \rrbracket]_{\mathrm{sub}}\). Since applying a regular substitution to an SFMTT expression amounts to applying all constituent atomic substitutions, both expressions are equal.

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} t_1 [\sigma_1]_{\mathrm{ws}} \equiv^{\sigma} t_2 [\sigma_2]_{\mathrm{ws}} \exp @ m\) (WSMTT-EQ-EXPR-CONG-SUB)

J. Ceulemans, A. Nuyts and D. Devriese

25

CASE \(\vdash_{\mathrm{ws}}\sigma_1\circ \tau_1\equiv^{\sigma}\sigma_{2}\circ \tau_{2}\operatorname {sub}(\hat{\Gamma}\to \hat{\Xi})@m\) (WSMTT-EQ-SUB-CONG-COMPOSE)

We know from the premises that \(\vdash_{\mathrm{ws}}\sigma_1\equiv^{\sigma}\sigma_{2}\operatorname {sub}(\hat{\Delta}\to \hat{\Xi})@m\) and \(\vdash_{\mathrm{ws}}\tau_1\equiv^{\sigma}\tau_{2}\operatorname {sub}(\hat{\Gamma}\rightarrow\) \(\hat{\Delta})@m\) and hence via the induction hypothesis \([\sigma_1]\approx^{\mathrm{obs}}[\sigma_2]\) and \([\tau_1]\approx^{\mathrm{obs}}[\tau_2]\). For an arbitrary expression \(\hat{\Xi}\vdash_{\mathrm{sf}}t\exp @m\) we then have that

\[
\begin{array}{l} t \left[ \llbracket \sigma_ {1} \circ \tau_ {1} \rrbracket \right] _ {\text { sub }} = t \left[ \llbracket \sigma_ {1} \rrbracket + + \llbracket \tau_ {1} \rrbracket \right] _ {\text { sub }} \quad (\text { Definition   of } [ [ \_ ] ]) \\ = t \left[ \llbracket \sigma_ {1} \rrbracket \right] _ {\text { sub }} \left[ \llbracket \tau_ {1} \rrbracket \right] _ {\text { sub }} \\ = t \left[ \llbracket \sigma_ {2} \rrbracket \right] _ {\text { sub }} \left[ \llbracket \tau_ {1} \rrbracket \right] _ {\text { sub }} \quad (\text { Definition   of } \sigma_ {1} \approx^ {\mathrm{obs}} \sigma_ {2}) \\ = t \left[ \llbracket \sigma_ {2} \rrbracket \right] _ {\text { sub }} \left[ \llbracket \tau_ {2} \rrbracket \right] _ {\text { sub }} \quad (\text { Definition   of } \tau_ {1} \approx^ {\text { obs }} \tau_ {2}) \\ = t \left[ \llbracket \sigma_ {2} \circ \tau_ {2} \rrbracket \right] _ {\text { sub }}, \\ \end{array}
\]

which proves that \(\llbracket \sigma_1\circ \tau_1\rrbracket \approx^{\mathrm{obs}}\llbracket \sigma_2\circ \tau_2\rrbracket .\)

CASE \(\vdash_{\mathrm{ws}}\sigma_1.t_1\equiv^\sigma \sigma_2.t_2\) sub \((\hat{\Gamma}\to \hat{\Delta}.\mu)\) @ \(n\) (WSMTT-EQ-SUB-CONG-EXTEND)

The premises tell us that \(\vdash_{\mathrm{ws}}\sigma_1\equiv^\sigma \sigma_2\) sub \((\hat{\Gamma}\to \hat{\Delta})@\mathfrak{n}\) and \(\hat{\Gamma}.\widehat{\mathbf{\Omega}}_{\mu}\vdash_{\mathrm{ws}}t_{1}\equiv^{\sigma}t_{2}\exp @m\) and hence by the induction hypothesis \([\sigma_1]\approx^{\mathrm{obs}}[\sigma_2]\) and \([t_1] = [t_2]\). Lemma 15 then gives us that \([\sigma_1]^+ \approx^{\mathrm{obs}}[\sigma_2]^+\) from which it follows that

\[
\begin{array}{l} [ \sigma_ {1}. t _ {1} ] = [ \sigma_ {1} ] ^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, [ t _ {1} ]) \quad (\text { Definition   of } [ [ \_ ] ]) \\ \approx^ {\mathrm{obs}} \llbracket \sigma_ {2} \rrbracket^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, \llbracket t _ {1} \rrbracket) \quad \left(\llbracket \sigma_ {1} \rrbracket^ {+} \approx^ {\mathrm{obs}} \llbracket \sigma_ {2} \rrbracket^ {+}\right) \\ = \llbracket \sigma_ {2} \rrbracket^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, \llbracket t _ {2} \rrbracket) \\ = \llbracket \sigma_ {2}. t _ {2} \rrbracket . \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}\sigma_1.\widehat{\mathbf{\Omega}}_\mu \equiv^\sigma \sigma_2.\widehat{\mathbf{\Omega}}_\mu \operatorname {sub}(\hat{\Gamma}.\widehat{\mathbf{\Omega}}_\mu \to \hat{\Delta}.\widehat{\mathbf{\Omega}}_\mu)\) @ \(m\) (WSMTT-EQ-SUB-CONG-LOCK)

From the premise we know that \(\vdash_{\mathrm{ws}}\sigma_1\equiv^\sigma \sigma_2\) sub \((\hat{\Gamma}\to \hat{\Delta})@\mathfrak{n}\) and hence via induction \([\sigma_1]\approx^{\mathrm{obs}}[\sigma_2]\). We can then use Lemma 14 to see that \([\sigma_1.\widehat{\mathbf{\Omega}}_\mu ] = [\sigma_1].\widehat{\mathbf{\Omega}}_\mu\) is observationally equivalent to \([\sigma_2.\widehat{\mathbf{\Omega}}_\mu ] = [\sigma_2].\widehat{\mathbf{\Omega}}_\mu\).

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} (\lambda^{\mu}(t)) [\sigma]_{\mathrm{ws}} \equiv^{\sigma} \lambda^{\mu}(t [\sigma^{+}]_{\mathrm{ws}}) \exp @ n\) (WSMTT-EQ-EXPR-LAM-SUB)

Since all atomic SFMTT substitutions can be pushed through \(\lambda^{\mu}(\_)\) (see Equation (9)) and the lifting of a regular substitution consists of the lifted atomic substitutions, we have (also making use of the definition of \([\_]\))

\[
\llbracket (\lambda^ {\mu} (t)) [ \sigma ] _ {\mathrm{ws}} \rrbracket = \llbracket \lambda^ {\mu} (t) \rrbracket [ [ \sigma ] ] _ {\mathrm{sub}} = \lambda^ {\mu} ([ [ t ] ]) [ [ \sigma ] ] _ {\mathrm{sub}} = \lambda^ {\mu} ([ [ t ] ] [ [ \sigma ] ] ^ {+} ] _ {\mathrm{sub}}).
\]

On the other hand we know that \(\llbracket \lambda^{\mu}(t[\sigma^{+}]_{\mathrm{ws}})\rrbracket = \lambda^{\mu}([t][[\sigma^{+}]]_{\mathrm{sub}})\). We conclude that both expressions are indeed equal because \(\llbracket \sigma^{+}\rrbracket \approx^{\mathrm{obs}}[\sigma]^{+}\) by Lemma 17.

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} (\mathsf{app}_{\mu}(f; t)) [\sigma]_{\mathrm{ws}} \equiv^{\sigma} \mathsf{app}_{\mu}(f[\sigma]_{\mathrm{ws}}; t[\sigma. \widehat{\mathbf{\Omega}}_{\mu}]_{\mathrm{ws}}) \exp @ n\) (WSMTT-EQ-EXPR-APP-SUB)

We have

\[
\begin{array}{l} \llbracket \left(\mathsf {a p p} _ {\mu} (f; t)\right) [ \sigma ] _ {\mathrm{ws}} \rrbracket \\ = \left(\mathsf {a p p} _ {\mu} ([ [ f ] ]; [ [ t ] ])\right) [ [ \sigma ] ] _ {\text {sub}} \quad \text {(Definition of} [ [ \_ ] ]) \\ = \mathsf {a p p} _ {\mu} ([ [ f ] ] [ [ \sigma ] ] _ {\text {sub}}; [ [ t ] ] [ [ \sigma ] ]. \widehat {\boldsymbol {\Omega}} ] _ {\text {sub}}) \quad (\text {Repeated use of Equation (10)}) \\ \end{array}
\]

and

\[
\llbracket \mathsf {a p p} _ {\mu} \left(f [ \sigma ] _ {\mathrm{ws}}; t [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}}\right) \rrbracket = \mathsf {a p p} _ {\mu} \left(\llbracket f \rrbracket [ [ \sigma ] ] _ {\mathrm{sub}}; \llbracket t \rrbracket [ [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] ] _ {\mathrm{sub}}\right).
\]

The result follows immediately since \(\llbracket \sigma .\widehat{\mathbf{\Omega}}_{\mu}\rrbracket = \llbracket \sigma \rrbracket .\widehat{\mathbf{\Omega}}_{\mu}\).

The cases for pushing substitutions through all other expression constructors are proved similarly.

26

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\vdash_{\mathrm{ws}}\sigma \equiv^{\sigma}!\operatorname {sub}(\hat{\Gamma}\to \cdot)\) @ \(m\) (WSMTT-EQ-SUB-EMPTY-UNIQUE)

We use Proposition 12 to prove that \(\llbracket \sigma \rrbracket \approx^{\mathrm{obs}} [\llbracket !\rrbracket]\). The condition of that proposition is immediately satisfied since there are no variables in the scoping context \(\cdot, \Lambda\) for any lock telescope \(\Lambda\).

CASE \(\hat{\Gamma}.\widehat{\mathbf{B}}_{\mu}\vdash_{\mathrm{ws}}\mathbf{v}_{0}[(\sigma .t).\widehat{\mathbf{B}}_{\mu}]_{\mathrm{ws}}\equiv^{\sigma}t\exp @m\) (WSMTT-EQ-EXPR-EXTEND-VAR)

We compute (using among others the definition of  \( \llbracket\ldots\rrbracket \) )

\[
\begin{array}{l} \llbracket \mathbf {v} _ {0} [ (\sigma . t). \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}} \rrbracket \\ = \llbracket \mathbf {v} _ {0} \rrbracket \left[ \llbracket (\sigma . t). \widehat {\boldsymbol {\Omega}} _ {\mu} \rrbracket \right] _ {\text {sub}} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] ^ {+}. \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \left[ (\mathrm{id} ^ {a}. [ [ t ] ]). \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {asub}} \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} [ \mathrm{id} ^ {a}. [ [ t ] ] ] _ {\text {asub}} ^ {\widehat {\boldsymbol {\Omega}} _ {\mu}} \quad (\text {Repeated application of Lemma 6}) \\ = [ [ t ] ] \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {1 _ {\mu} \in \hat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \hat {\boldsymbol {\Omega}} _ {\mu}} \right] _ {\text {aren}} \quad (\text {Equation (26)}) \\ = [ [ t ] ]. \quad (\text { Proposition   20 }) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}\pi \circ (\sigma .t)\equiv^{\sigma}\sigma \operatorname {sub}(\hat{\Gamma}\to \hat{\Delta})@\mathfrak{n}\) (WSMTT-EQ-SUB-EXTEND-WEAKEN)

We have that \( ^{4} \)

\[
[ \pi \circ (\sigma . t) ] = [ \pi ] + + [ \sigma . t ] = \pi * [ \sigma ] ^ {+} * (\mathrm{id} ^ {a}. [ [ t ] ]).
\]

Since \( s[\pi]_{\mathrm{asub}} = s[\pi]_{\mathrm{aren}} \) (which is easy to prove using Proposition 11), we get that

\[
\begin{array}{l} s \left[ \llbracket \pi \circ (\sigma . t) \rrbracket \right] _ {\text {sub}} = s [ \pi ] _ {\text {asub}} \left[ \llbracket \sigma \rrbracket^ {+} \right] _ {\text {asub}} [ \mathrm{id} ^ {a}. [ [ t ] ] ] _ {\text {asub}} \\ = s \left[ [ [ \sigma ] ] \right] _ {\text {asub}} [ \pi ] _ {\text {asub}} \left[ \mathrm{id} ^ {a}. [ [ t ] ] \right] _ {\text {asub}} \tag {Lemma9} \\ \end{array}
\]

for all expressions \(s\). It therefore suffices to show that \(s'\) \([\pi]_{\mathrm{asub}}[\mathrm{id}^{\mathrm{a}}.[\![t]\!]_{\mathrm{asub}} = s'\) for every \(s'\). We do this using Proposition 11, so we take an arbitrary lock telescope \(\Lambda : \mathsf{LockTele}(n \to o)\) and variable \(\hat{\Gamma}. \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ o\). We can then compute that

\[
\begin{array}{l} v \left[ \pi \right] _ {\text {asub}} ^ {\Lambda} \left[ \mathrm{id} ^ {a}. [ [ t ] ] \right] _ {\text {asub}} ^ {\Lambda} = v \left[ \pi \right] _ {\text {aren}} ^ {\Lambda} \left[ \mathrm{id} ^ {a}. [ [ t ] ] \right] _ {\text {asub}} ^ {\Lambda} \\ = \operatorname{suc} (v) [ \mathrm{id} ^ {a}. [ [ t ] ] ] _ {\text {asub}} ^ {\Lambda} \\ = v \left[ \mathrm{id} ^ {a} \right] _ {\text {asub}} ^ {\Lambda} = v. \quad (\text {Equations (22) and (27)}) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}\sigma \equiv^{\sigma}(\pi \circ \sigma).(\mathbf{v}_{0}[\sigma .\widehat{\boldsymbol{\Omega}}_{\mu}]_{\mathrm{ws}})\operatorname {sub}(\hat{\Gamma}\to \hat{\Delta}.\mu)\) @ \(n\) (WSMTT-EQ-SUB-EXTEND-ETA)

We have that

\[
\begin{array}{l} \llbracket (\pi \circ \sigma). (\mathbf {v} _ {0} [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}}) \rrbracket = \llbracket \pi \circ \sigma \rrbracket^ {+} * (\mathrm{id} ^ {a}. \llbracket \mathbf {v} _ {0} [ \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\mathrm{ws}} \rrbracket) \\ = \left(\llbracket \pi \rrbracket + + \llbracket \sigma \rrbracket\right) ^ {+} * \left(\mathrm{id} ^ {a}. \llbracket \mathbf {v} _ {0} \rrbracket \left[ \llbracket \sigma . \widehat {\boldsymbol {\Omega}} _ {\mu} \rrbracket \right] _ {\text {sub}}\right) \\ = \pi^ {+} * [ [ \sigma ] ] ^ {+} * \left(\mathrm{id} ^ {a}. \mathbf {v} _ {0} ^ {1 _ {\mu}} [ [ [ \sigma ] ]. \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\text {sub}}\right). \\ \end{array}
\]

We now use Proposition 11, so for any lock telescope \(\Lambda : \mathsf{LockTele}(n \to o)\) and variable \(\hat{\Delta} \cdot \mu \cdot \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ o\), we need to show that

\[
v \left[ \pi^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {a}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ]. \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} = v \left[ [ [ \sigma ] ]. \Lambda \right] _ {\text {sub}}.
\]

We distinguish two cases for \( v \).

\( ^{4} \)  Note that  \( \otimes \)  actually takes a regular substitution as left argument and an atomic substitution as right argument. We slightly abuse this notation by putting an atomic substitution to the left of the right-hand side of the following equation.

J. Ceulemans, A. Nuyts and D. Devriese

27

= CASE  \( v = v_{0}^{\alpha} \)  with  \( \alpha \in \mu \Rightarrow \text{locks}(\Lambda) \) .

Then we get that

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 6}) \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 6, repeated}) \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \left[ \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}} \quad (\text {Equation (26)}) \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Delta} \mu} ^ {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \\ \end{array} \right] _ {\text {aren}} [ [ [ \sigma ] ] \cdot \Lambda ] _ {\text {sub}} \quad (\text {Proposition 23}) \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ [ [ \sigma ] ] \cdot \Lambda \right] _ {\text {sub}}. \\ \end{array}
\]

= CASE  \( v = \text{suc}(v') \)  with  \( \hat{\Delta} \cdot \Lambda \vdash_{sf} v' \text{ var } @ o \)

Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \\ = v ^ {\prime} [ \pi ] _ {\text {asub}} ^ {\Lambda} [ \pi ] _ {\text {aren}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} [ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 6}) \\ = \operatorname{suc} \left(v ^ {\prime}\right) [ \pi ] _ {\text {aren}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} [ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ [ [ \sigma ] ] \cdot \Lambda \right] _ {\text {sub}} \left[ \pi \right] _ {\text {aren}} ^ {\Lambda} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 9}) \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ [ [ \sigma ] ] \cdot \Lambda \right] _ {\text {sub}}, \\ \end{array}
\]

where the last equation is proved as in the case of WSMTT-EQ-SUB-EXTEND-WEAKEN.

CASE \(\vdash_{\mathrm{ws}}\mathrm{id}.\widehat{\boldsymbol{\Omega}}_{\mu}\equiv^{\sigma}\mathrm{id}\mathrm{sub}(\hat{\Gamma}.\widehat{\boldsymbol{\Omega}}_{\mu}\to \hat{\Gamma}.\widehat{\boldsymbol{\Omega}}_{\mu})@m\) (WSMTT-EQ-SUB-LOCK-ID)

The translations of both sides of this equivalence are the empty sequence of atomic SFMTT substitutions, so this case is trivial.

CASE \(\vdash_{\mathrm{ws}} (\sigma \circ \tau) \cdot \widehat{\boldsymbol{\Omega}}_{\mu} \equiv^{\sigma} (\sigma \cdot \widehat{\boldsymbol{\Omega}}_{\mu}) \circ (\tau \cdot \widehat{\boldsymbol{\Omega}}_{\mu}) \operatorname{sub}(\hat{\Gamma} \cdot \widehat{\boldsymbol{\Omega}}_{\mu} \to \widehat{\Xi} \cdot \widehat{\boldsymbol{\Omega}}_{\mu}) @ m\) (WSMTT-EQ-SUB-LOCK-COMPOSE)

Again this case is trivial since a lock is applied to every atomic substitution in a sequence and hence it distributes over sequence concatenation.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Delta}}^{\alpha \in \Lambda \Rightarrow \Theta} \circ (\sigma \cdot \Theta) \equiv^{\sigma} (\sigma \cdot \Lambda) \circ \mathcal{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta} \operatorname{sub}(\hat{\Gamma} \cdot \Theta \to \hat{\Delta} \cdot \Lambda) @ n\) (WSMTT-EQ-SUB-KEY-NATURAL)

This is a direct consequence of Proposition 23.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Gamma}}^{1_{\mathrm{locks}(\Lambda)} \in \Lambda \Rightarrow \Lambda} \equiv^{\sigma} \mathrm{id} \operatorname{sub}(\hat{\Gamma} \cdot \Lambda \to \hat{\Gamma} \cdot \Lambda) @ n\) (WSMTT-EQ-SUB-KEY-UNIT)

Applying an SFMTT key substitution is exactly the same as applying the corresponding key renaming (which can be easily proved using Proposition 11), so this case follows immediately from Proposition 20.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Gamma}}^{\beta \circ \alpha \in \Lambda \Rightarrow \Psi} \equiv^{\sigma} \mathcal{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta} \circ \mathcal{Q}_{\hat{\Gamma}}^{\beta \in \Theta \Rightarrow \Psi} \operatorname{sub}(\hat{\Gamma} \cdot \Psi \to \hat{\Gamma} \cdot \Lambda) @ n\) (WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL)

In the same way, the result in this case is proved by Proposition 21.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Gamma}}^{\beta \circ \alpha \in \Lambda_1 \cdot \Theta_1 \Rightarrow \Lambda_2 \cdot \Theta_2} \equiv^{\sigma} (\mathcal{Q}_{\hat{\Gamma}}^{\beta \in \Lambda_1 \Rightarrow \Lambda_2 \cdot \Theta_1}) \circ \mathcal{Q}_{\hat{\Gamma} \cdot \Lambda_2}^{\alpha \in \Theta_1 \Rightarrow \Theta_2} \operatorname{sub}(\hat{\Gamma} \cdot \Lambda_2 \cdot \Theta_2 \to \hat{\Gamma} \cdot \Lambda_1 \cdot \Theta_1) @ o\) (WSMTT-EQ-SUB-KEY-COMPOSE-HORIZONTAL)

This is a direct consequence of Proposition 22.

◀

28

A Substitution Algorithm for Multimode Type Theory: Technical Report

## 5 Soundness

We want to prove the soundness of our substitution algorithm with respect to the notion of  \( \sigma \) -equivalence introduced in Figure 4. In other words, whenever we compute all substitutions away in a WSMTT expression t, the result should be  \( \sigma \) -equivalent to the expression t we started from.

Theorem 25. Let \(\hat{\Gamma} \vdash_{\mathrm{ws}} t \exp @ m\) be a WSMTT expression. Then we have that \(\hat{\Gamma} \vdash_{\mathrm{ws}} \operatorname{embed}([t]) \equiv^{\sigma} t \exp @ m\).

The proof of this theorem appears at the end of this section.

### 5.1 Embedding of SFMTT into WSMTT

Note that in Section 3.3 we first defined an embedding of SFMTT expressions to WSMTT and then an embedding for atomic and regular rensubs. This is unlike the translation function from WSMTT to SFMTT, which is defined mutually recursively for expressions and substitutions. The reason for this is that SFMTT substitutions do not occur in the syntax of SFMTT expressions. However, the proof of Theorem 25 is easier to formulate if we do have an embedding of rensubs at our disposal. In particular, the core result for proving soundness will be Proposition 34.

In this section on the soundness proof, we will extensively use the fact that composition of WSMTT substitutions is associative and that id is its unit, all up to  \( \sigma \) -equivalence. Moreover, congruence rules with respect to WSMTT  \( \sigma \) -equivalence will also regularly be used. We will not explicitly mention the use of any of these rules from Figure 4.

▶ Example 26 (Embedding does not preserve observational equivalence). Given that we have introduced the notion of observational equivalence for SFMTT substitutions in Section 4.1, it is natural to ask whether  \( \sigma \approx^{obs} \tau \)  implies  \( \text{embed}(\sigma) \equiv^{\sigma} \text{embed}(\tau) \) . The answer is no, and we can give a counterexample similar to Example 13. Again, let the mode theory be the walking arrow. Let  \( \hat{\Gamma} = (\cdot \widehat{\mathbf{B}}_{\mu}) \)  and  \( \hat{\Delta} = (\cdot \mathbb{1} \widehat{\mathbf{B}}_{\mu}) \) . As argued in Example 13, all substitutions to  \( \hat{\Delta} \)  are observationally equivalent. However, the embeddings of  \( \vdash_{sf} (!true \widehat{\mathbf{B}}_{\mu}), (!false \widehat{\mathbf{B}}_{\mu}) \)  asub( \( \hat{\Gamma} \to \hat{\Delta} \) ) @ m are not  \( \sigma \) -equivalent.

▶ Lemma 27. For an SFMTT renaming or substitution  \( \vdash_{sf} \sigma \operatorname{ren}/\operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m \)  we have that  \( \vdash_{ws} \operatorname{embed}(\sigma^{+}) \equiv^{\sigma} \operatorname{embed}(\sigma)^{+} \operatorname{sub}(\hat{\Gamma}. \mu \to \hat{\Delta}. \mu) @ m \) .

Proof. Since  \( id^{+} \equiv^{\sigma} id \)  and  \( (\sigma \circ \tau)^{+} \equiv^{\sigma} \sigma^{+} \circ \tau^{+} \)  (which can be proved using WSMTT-EQ-SUB-EXTEND-WEAKEN, WSMTT-EQ-SUB-EXTEND-ETA and WSMTT-EQ-EXPR-EXTEND-VAR), it suffices to prove this for an atomic rensub  \( \sigma \) . Then we have that

\(\begin{array}{ll}\mathsf{embed}(\sigma^{+})\\ = \mathsf{embed}\Big(\mathsf{weaken}(\sigma).\mathbf{v}_{0}^{1_{\mu}}\Big) & (\text{SFMTT definition of }^{+},(3))\\ = (\mathsf{embed}(\sigma)\circ \pi).\Big(\mathbf{v}_{0}\left[\mathbf{a}_{\hat{\Gamma},\mu}^{1_{\mu}\in \hat{\mathbf{B}}_{\mu}\Rightarrow \hat{\mathbf{B}}_{\mu}}\right]_{\mathrm{ws}}\Big) & (\text{Definition of embed} (\_))\\ \equiv^{\sigma}(\mathsf{embed}(\sigma)\circ \pi).\mathbf{v}_{0} & (\text{WSMTT-EQ-SUB-KEY-UNIT})\\ = \mathsf{embed}(\sigma)^{+}. & (\text{WSMTT definition of }^{+},(1)) \end{array}\)

J. Ceulemans, A. Nuyts and D. Devriese

29

## 5.2 Embedding and Renaming/Substitution

The core property for proving the soundness theorem is Proposition 34, which states that $\mathsf{embed}(t[\sigma]_{\mathsf{sub}}) \equiv^{\sigma} \mathsf{embed}(t)[\mathsf{embed}(\sigma)]_{\mathsf{ws}}$ for every $t$ and $\sigma$. In order to prove such a result, we will adopt a similar technique as in Section 4.1 for proving observational equivalence of SFMTT substitutions. First we show that it is sufficient to prove the result for variables after adding an arbitrary scoping telescope $\Phi$ to $\sigma$ (Lemma 28). Then we prove that actually the scoping telescope $\Phi$ only needs to be a lock telescope (Lemmas 29 and 31).

$\triangleright$ **Lemma 28.** *Let $\vdash_{\mathsf{sf}} \sigma \operatorname{aren} / \operatorname{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m$ be an atomic SFMTT rensub and assume that $\hat{\Gamma} \cdot \Phi \vdash_{\mathsf{ws}} \mathsf{embed}\left(v[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \equiv^{\sigma} \mathsf{embed}(v)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \operatorname{expr} @ n$ for any scoping telescope $\Phi : \mathsf{sTele}(m \to n)$ and variable $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} v \operatorname{var} @ n$. Then we have that $\hat{\Gamma} \vdash_{\mathsf{ws}} \mathsf{embed}\left(t[\sigma]_{\operatorname{aren} / \operatorname{asub}}\right) \equiv^{\sigma} \mathsf{embed}(t)[\mathsf{embed}(\sigma)]_{\mathsf{ws}} \operatorname{expr} @ m$ for all expressions $\hat{\Delta} \vdash_{\mathsf{sf}} t \operatorname{expr} @ m$.*

**Proof.** We will prove the more general result that $\hat{\Gamma} \cdot \Phi \vdash_{\mathsf{ws}} \mathsf{embed}\left(t[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \equiv^{\sigma} \mathsf{embed}(t)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \operatorname{expr} @ n$ for all scoping telescopes $\Phi : \mathsf{sTele}(m \to n)$ and expressions $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \operatorname{expr} @ n$. This proof proceeds by induction on $t$. We only show the cases for variables, lambda abstraction and the modal term constructor. The other cases can be proved similarly.

$\triangleright$ CASE $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} v \operatorname{expr} @ n$ (SF-EXPR-VAR)
The result is exactly what we assumed in the lemma.

$\triangleright$ CASE $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} \lambda^{\mu}(t) \operatorname{expr} @ n$ (SF-EXPR-LAM)
We have that

$$
\begin{array}{l}
\mathsf{embed}\left(\left(\lambda^{\mu}(t)\right)[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \\
= \mathsf{embed}\left(\lambda^{\mu}\left(t\left[(\sigma \cdot \Phi)^{+}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Equation (9))} \\
= \lambda^{\mu}\left(\mathsf{embed}\left(t\left[(\sigma \cdot \Phi)^{+}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\equiv^{\sigma} \lambda^{\mu}\left(\mathsf{embed}(t)\left[\mathsf{embed}\left((\sigma \cdot \Phi)^{+}\right)\right]_{\mathsf{ws}}\right) \quad \text{(Induction hypothesis)} \\
\equiv^{\sigma} \lambda^{\mu}\left(\mathsf{embed}(t)\left[\left(\mathsf{embed}(\sigma \cdot \Phi)\right)^{+}\right]_{\mathsf{ws}}\right) \quad \text{(Lemma 27)} \\
\equiv^{\sigma}\left(\lambda^{\mu}(\mathsf{embed}(t))\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \quad \text{(WSMTT-EQ-EXPR-LAM-SUB)} \\
= \mathsf{embed}\left(\lambda^{\mu}(t)\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}}. \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\end{array}
$$

Note that we can indeed apply the induction hypothesis where it is indicated since $(\sigma \cdot \Phi)^{+} = \sigma \cdot (\Phi \cdot \mu)$.

$\triangleright$ CASE $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} \mathsf{mod}_{\mu}(t) \operatorname{expr} @ n$ (SF-EXPR-MOD-TM)

Now we can compute that

$$
\begin{array}{l}
\mathsf{embed}\left(\left(\mathsf{mod}_{\mu}(t)\right)[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \\
= \mathsf{embed}\left(\mathsf{mod}_{\mu}\left(t\left[(\sigma \cdot \Phi) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Equation (12))} \\
= \mathsf{mod}_{\mu}\left(\mathsf{embed}\left(t\left[(\sigma \cdot \Phi) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\equiv^{\sigma} \mathsf{mod}_{\mu}\left(\mathsf{embed}(t)\left[\mathsf{embed}\left((\sigma \cdot \Phi) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right)\right]_{\mathsf{ws}}\right) \quad \text{(Induction hypothesis)} \\
= \mathsf{mod}_{\mu}\left(\mathsf{embed}(t)\left[\left(\mathsf{embed}(\sigma \cdot \Phi)\right) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right]_{\mathsf{ws}}\right) \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\equiv^{\sigma}\left(\mathsf{mod}_{\mu}\left(\mathsf{embed}(t)\right)\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}}. \quad \text{(WSMTT-EQ-EXPR-MOD-TM-SUB)} \\
= \mathsf{embed}\left(\mathsf{mod}_{\mu}(t)\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\end{array}
$$

30

A Substitution Algorithm for Multimode Type Theory: Technical Report

Again we can apply the induction hypothesis because  \( (\sigma \cdot \Phi) \cdot \widehat{\mathbf{a}}_{\mu} = \sigma \cdot (\Phi \cdot \widehat{\mathbf{a}}_{\mu}) \) . The rule WSMTT-EQ-EXPR-MOD-TM-SUB is not included in Figure 4, but it is similar to WSMTT-EQ-EXPR-LAM-SUB.

▶ Lemma 29. Let  \( \vdash_{sf} \sigma \)  aren( \( \hat{\Gamma} \rightarrow \hat{\Delta} \) ) @ m be an atomic SFMTT renaming and assume that  \( \hat{\Gamma} \cdot \Lambda \vdash_{ws} \)  embed(v [ \( \sigma \cdot \Lambda \) ] \( _{aren} \) )  \( \equiv^{\sigma} \)  embed(v) [embed( \( \sigma \cdot \Lambda \) )] \( _{ws} \)  expr @ n for every lock telescope  \( \Lambda : sTele(m \rightarrow n) \)  and variable  \( \hat{\Delta} \cdot \Lambda \vdash_{sf} v \)  var @ n. Then we have that  \( \hat{\Gamma} \vdash_{ws} \)  embed(t [ \( \sigma \) ] \( _{aren} \) )  \( \equiv^{\sigma} \)  embed(t) [embed( \( \sigma \) )] \( _{ws} \)  expr @ m for all expressions  \( \hat{\Delta} \vdash_{sf} t \)  expr @ m.

Proof. By making use of Lemma 28, we have to show that \(\hat{\Gamma} \cdot \Phi \vdash_{\mathrm{ws}} \operatorname{embed}(v[\sigma \cdot \Phi]_{\mathrm{aren}}) \equiv^{\sigma} \operatorname{embed}(v)[\operatorname{embed}(\sigma \cdot \Phi)]_{\mathrm{ws}} \exp @ n\) for all \(\Phi : s\mathrm{Tele}(m \to n)\) and \(\hat{\Delta} \cdot \Phi \vdash_{\mathrm{sf}} v \operatorname{var} @ n\). We do this by induction on the number of variables in \(\Phi\).

CASE \(\Phi = \Lambda\), so \(\Phi\) has no variables

The result is exactly what we assume in this lemma.

CASE \(\Phi = \Phi^{\prime}\cdot \mu \cdot \Lambda\)

Now we distinguish between two cases for the variable \( v \).

CASE \( v = \mathbf{v}_0^\alpha \) with \( \alpha \in \mu \Rightarrow \text{locks}(\Lambda) \)

For the left-hand side, we have that

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} [ \sigma . \Phi^ {\prime}. \mu . \Lambda ] _ {\text {aren}}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text {aren}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) \quad (\text { Lemma   5 }) \\ = \mathbf {v} _ {0} \left[ \underset {\hat {\Gamma}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}}. \quad (\text {Definition of embed} (\_)) \\ \end{array}
\]

On the other hand, we have

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) \left[ \operatorname{embed} \left(\sigma . \Phi^ {\prime}. \mu . \Lambda\right) \right] _ {\mathrm{ws}} \\ = \mathbf {v} _ {0} \left[ \underset {\hat {\Delta}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \left[ \operatorname{embed} \left(\left(\sigma . \Phi^ {\prime}\right) ^ {+}. \Lambda\right) \right] _ {\mathrm{ws}} \quad (\text {Definition of embed} (\mathbf {v} _ {0} ^ {\alpha})) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ \underset {\hat {\Delta}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \left[ (\operatorname{embed} (\sigma . \Phi^ {\prime})) ^ {+}. \Lambda \right] _ {\mathrm{ws}} \quad (\text {Lemma 27}) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ (\operatorname{embed} (\sigma . \Phi^ {\prime})) ^ {+}. \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\mathrm{ws}} \left[ \underset {\hat {\Gamma}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \quad \left(\text {WSMTT - EQ - SUB - KEY - NATURAL}\right) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ \underset {\hat {\Gamma}. \Phi^ {\prime}. \mu} {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}}. \quad (\text {WSMTT - EQ - EXPR - EXTEND - VAR}) \\ \end{array}
\]

CASE \( v = \operatorname{suc}(v') \) with \( \hat{\Delta} \cdot \Phi' \cdot \Lambda \vdash_{\mathrm{sf}} v' \operatorname{var} @ n \)

Now we see that

\[
\begin{array}{l} \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \mu . \Lambda \right] _ {\text {aren}}\right) \\ = \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ \left(\sigma . \Phi^ {\prime}\right) ^ {+} \right] _ {\text {aren}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime} \left[ \sigma . \Phi^ {\prime} \right] _ {\text {aren}} ^ {\Lambda}\right)\right) \tag {Lemma5} \\ = \operatorname{embed} \left(v ^ {\prime} [ \sigma . \Phi^ {\prime}. \Lambda ] _ {\text {aren}}\right) [ \pi . \Lambda ] _ {\mathrm{ws}} \quad (\text {Definition of embed} (\_)) \\ \equiv^ {\sigma} \operatorname{embed} \left(v ^ {\prime}\right) \left[ \operatorname{embed} \left(\sigma . \Phi^ {\prime}. \Lambda\right) \right] _ {\mathrm{ws}} [ \pi . \Lambda ] _ {\mathrm{ws}}. \quad (\text {Induction hypothesis}) \\ \end{array}
\]

J. Ceulemans, A. Nuyts and D. Devriese

31

Furthermore, we have

$$\begin{array}{l} \operatorname{embed}(\operatorname{suc}\left(v^{\prime}\right))\left[\operatorname{embed}(\sigma \cdot \Phi^{\prime} \cdot \mu \cdot \Lambda)\right]_{\mathrm{ws}} \\ =\operatorname{embed}\left(v^{\prime}\right)\left[\pi \cdot \Lambda\right]_{\mathrm{ws}}\left[\left(\operatorname{embed}(\sigma \cdot \Phi^{\prime})\right)^{+} \cdot \Lambda\right]_{\mathrm{ws}} \quad\left(\text { Definition of } \operatorname{embed}(\operatorname{suc}\left(v^{\prime}\right))\right) \\ \equiv^{\sigma} \operatorname{embed}\left(v^{\prime}\right)\left[\left(\pi \circ\left(\operatorname{embed}(\sigma \cdot \Phi^{\prime})\right)^{+}\right) \cdot \Lambda\right]_{\mathrm{ws}} \quad(*) \\ \equiv^{\sigma} \operatorname{embed}\left(v^{\prime}\right)\left[\left(\operatorname{embed}(\sigma \cdot \Phi^{\prime}) \circ \pi\right) \cdot \Lambda\right]_{\mathrm{ws}} \quad\left(\text { WSMTT-EQ-SUB-EXTEND-WEAKEN }\right) \\ \equiv^{\sigma} \operatorname{embed}\left(v^{\prime}\right)\left[\operatorname{embed}(\sigma \cdot \Phi^{\prime} \cdot \Lambda)\right]_{\mathrm{ws}}\left[\pi \cdot \Lambda\right]_{\mathrm{ws}} . \quad(*) \end{array}$$

The steps marked with (*) make use of WSMTT-EQ-EXPR-SUB-COMPOSE and WSMTT-EQ-SUB-LOCK-COMPOSE.

▶ Lemma 30. Up to σ-equivalence, applying a weakening renaming commutes with the embedding function. In other words, for every lock telescope Λ : LockTele(m → n) and SFMTT expression Γ̂ . Λ ⊢_sf t expr @ n, we have that Γ̂ . μ . Λ ⊢_ws embed(t [π . Λ]_aren) ≡^σ embed(t) [π . Λ]_ws ≡^σ embed(t) [embed(π . Λ)]_ws expr @ n.

Proof. We first prove the second σ-equivalence by computing the following.

$$\begin{array}{l} \operatorname{embed}(\pi \cdot \Lambda)=\operatorname{embed}(\pi) \cdot \Lambda=\operatorname{embed}(\operatorname{weaken}(\operatorname{id}^{\mathrm{a}})) \cdot \Lambda \\ =\left(\operatorname{embed}(\operatorname{id}^{\mathrm{a}}) \circ \pi\right) \cdot \Lambda=(\operatorname{id} \circ \pi) \cdot \Lambda \\ \equiv^{\sigma} \pi \cdot \Lambda \quad\left(\text { WSMTT-EQ-SUB-ID-LEFT }\right) \end{array}$$

The rule WSMTT-EQ-SUB-ID-LEFT is not included in Figure 4, but it is similar to WSMTT-EQ-SUB-ID-RIGHT.

To prove the other σ-equivalence we use Lemma 29, so we take an arbitrary lock telescope Θ : LockTele(n → o) and a variable Γ̂ . Λ . Θ ⊢_sf v var @ o and then show that embed(v [π . Λ . Θ]_aren) = embed(v) [embed(π . Λ . Θ)]_ws. This can be easily proved by expanding the definition of embed(_) as follows.

$$\begin{array}{l} \operatorname{embed}\left(v[\pi]_{\text {aren }}^{\Lambda \cdot \Theta}\right)=\operatorname{embed}(\operatorname{suc}(v)) \\ =\operatorname{embed}(v)[\pi \cdot \Lambda \cdot \Theta]_{\mathrm{ws}} \\ \equiv^{\sigma} \operatorname{embed}(v)\left[\operatorname{embed}(\pi \cdot \Lambda \cdot \Theta)\right]_{\mathrm{ws}} \end{array}$$

Using Lemma 30, we can now prove a result similar to Lemma 29 but for substitutions instead of renamings.

▶ Lemma 31. Let ⊢_sf σ asub(Γ̂ → Δ̂) @ m be an atomic SFMTT substitution and assume that Γ̂ . Λ ⊢_ws embed(v [σ . Λ]_asub) ≡^σ embed(v) [embed(σ . Λ)]_ws expr @ n for every lock telescope Λ : sTele(m → n) and variable Δ̂ . Λ ⊢_sf v var @ n. Then we have that Γ̂ ⊢_ws embed(t [σ]_asub) ≡^σ embed(t) [embed(σ)]_ws expr @ m for all expressions Δ̂ ⊢_sf t expr @ m.

Proof. The proof is very similar to that of Lemma 29. Again we make use of Lemma 28, so we take an arbitrary Φ : sTele(m → n) and Δ̂ . Φ ⊢_sf v var @ n and show that Γ̂ . Φ ⊢_ws embed(v [σ . Φ]_asub) ≡^σ embed(v) [embed(σ . Φ)]_ws expr @ n by induction on the number of variables in Φ.

- CASE Φ = Λ, so Φ contains no variables
The result we need to show is exactly the assumption in the lemma.
- CASE Φ = Φ' . μ . Λ

We proceed by case distinction for the variable v.

32

A Substitution Algorithm for Multimode Type Theory: Technical Report

- CASE \( v = \mathbf{v}_0^\alpha \) with \( \alpha \in \mu \Rightarrow \text{locks}(\Lambda) \)

For the left-hand side, we get

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} [ \sigma . \Phi^ {\prime}. \mu . \Lambda ] _ {\text {asub}}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text {asub}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) \quad (\text { Lemma   6 }) \\ = \mathbf {v} _ {0} \left[ \boldsymbol {\alpha} _ {\hat {\Gamma}. \Phi^ {\prime}. \mu} ^ {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}}. \quad (\text {Definition of embed} (\mathbf {v} _ {0} ^ {\alpha})) \\ \end{array}
\]

The right-hand side can be computed in exactly the same way as in the proof of Lemma 29.

- CASE \( v = \operatorname{suc}(v') \) with \( \hat{\Delta} \cdot \Phi' \cdot \Lambda \vdash_{\mathrm{sf}} v' \operatorname{var} @ n \)

The left-hand side now becomes

\[
\begin{array}{l} \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ \sigma . \Phi^ {\prime}. \mu . \Lambda \right] _ {\text {asub}}\right) \\ = \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ (\sigma . \Phi^ {\prime}) ^ {+} \right] _ {\text {asub}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(v ^ {\prime} [ \sigma . \Phi^ {\prime} ] _ {\text {asub}} ^ {\Lambda} [ \pi ] _ {\text {aren}} ^ {\Lambda}\right) \quad (\text {Lemma 6}) \\ \equiv^ {\sigma} \operatorname{embed} \left(v ^ {\prime} [ \sigma . \Phi^ {\prime} ] _ {\text {asub}} ^ {\Lambda}\right) [ \pi . \Lambda ] _ {\mathrm{ws}} \quad (\text {Lemma 30}) \\ \equiv^ {\sigma} \operatorname{embed} (v ^ {\prime}) [ \operatorname{embed} (\sigma . \Phi^ {\prime}. \Lambda) ] _ {\mathrm{ws}} [ \pi . \Lambda ] _ {\mathrm{ws}}. \quad \text {(Induction hypothesis)} \\ \end{array}
\]

Again, the right-hand side can be computed in entirely the same way as in the proof of Lemma 29.

▶ Lemma 32. Given lock telescopes \(\Lambda, \Theta: \text{LockTele}(m \to n)\) and a 2-cell \(\alpha \in \text{locks}(\Lambda) \Rightarrow \text{locks}(\Theta)\), we have that

\[
\hat {\Gamma}. \Theta . \Psi \vdash_ {\mathrm{ws}} \operatorname{embed} \left(t \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi \right] _ {\text {aren}}\right) \equiv^ {\sigma} \operatorname{embed} (t) \left[ \operatorname{embed} \left(\mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi\right) \right] _ {\mathrm{ws}} \exp^ {\circledast_ {0}}
\]

for all lock telescopes \(\Psi : \text{LockTele}(n \to o)\) and expressions \(\hat{\Gamma} \cdot \Lambda \cdot \Psi \vdash_{\text{sf}} t \exp @_o\).

Proof. We again use Lemma 29, so we take a lock telescope \(\Upsilon : \text{LockTele}(o \to p)\) and a variable \(\hat{\Gamma} \cdot \Lambda \cdot \Psi \cdot \Upsilon \vdash_{\text{sf}} v \text{ var } @p\). We then distinguish between two cases for \(v\).

CASE \( v = \mathbf{v}_0^\beta \) with \( \hat{\Gamma} = \hat{\Gamma}' \cdot \mu \cdot \Omega \) and \( \beta \in \mu \Rightarrow \text{locks}(\Omega \cdot \Lambda \cdot \Psi \cdot \Upsilon) \)

Now we can compute that

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\beta} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu . \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi . \Upsilon}\right) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {(1 _ {\Omega} * (\alpha * 1 _ {(\Psi . \Upsilon)})) \circ \beta}\right) \quad (\text {Equations (14) and (19)}) \\ = \mathbf {v} _ {0} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu} ^ {(1 _ {\Omega} * (\alpha * 1 _ {(\Psi . \Upsilon)})) \circ \beta \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Omega . \Theta . \Psi . \Upsilon} \right] _ {\mathrm{ws}} \quad (\text {Definition of embed} (\_) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu} ^ {\beta \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Omega . \Lambda . \Psi . \Upsilon} \right] _ {\mathrm{ws}} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu} ^ {1 _ {\Omega} \in \Omega \Rightarrow \Omega}. \Lambda . \Psi . \Upsilon \right] _ {\mathrm{ws}} \\ \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu . \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi . \Upsilon \right] _ {\mathrm{ws}} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu . \Omega . \Theta} ^ {1 (\Psi . \Upsilon) \in \Psi . \Upsilon \Rightarrow \Psi . \Upsilon} \right] _ {\mathrm{ws}} (*) \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu} ^ {\beta \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Omega . \Lambda . \Psi . \Upsilon} \right] _ {\mathrm{ws}} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu . \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi . \Upsilon \right] _ {\mathrm{ws}} \quad (\text {WSMTT - EQ - SUB - KEY - UNIT}) \\ = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\beta}\right) \left[ \operatorname{embed} \left(\mathbf {Q} _ {\hat {\Gamma} ^ {\prime}. \mu . \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi . \Upsilon\right) \right] _ {\mathrm{ws}}. \quad (\text {Definition of embed} (\_) \\ \end{array}
\]

J. Ceulemans, A. Nuyts and D. Devriese

33

In the step marked by (*) we use of the rules WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL and WSMTT-EQ-SUB-KEY-COMPOSE-HORIZONTAL from Figure 4.

CASE \( v = \operatorname{suc}(v') \) with \( \hat{\Gamma} = \hat{\Gamma}' \cdot \mu \cdot \Omega \) and \( \hat{\Gamma}' \cdot \Omega \cdot \Lambda \cdot \Psi \cdot \Upsilon \vdash_{\mathrm{sf}} v' \operatorname{var} @ p \)

In this case we have that

\[
\begin{array}{l} \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \mu , \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi , \Upsilon}\right) \\ = \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi , \Upsilon}\right)\right) \quad (\text {Equations (15) and (19)}) \\ = \operatorname{embed} \left(v ^ {\prime} \left[ \mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta} \right] _ {\text {aren}} ^ {\Psi , \Upsilon}\right) [ \pi . \Omega . \Theta . \Psi . \Upsilon ] _ {\mathrm{ws}} \quad (\text {Definition of embed} (\_)) \\ \equiv^ {\sigma} \operatorname{embed} (v ^ {\prime}) \left[ \operatorname{embed} \left(\mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi . \Upsilon\right) \right] _ {\mathrm{ws}} [ \pi . \Omega . \Theta . \Psi . \Upsilon ] _ {\mathrm{ws}} \\ (\text { Induction   hypothesis }) \\ \equiv^ {\sigma} \operatorname{embed} (v ^ {\prime}) [ \pi . \Omega . \Lambda . \Psi . \Upsilon ] _ {\mathrm{ws}} \left[ \operatorname{embed} \left(\mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi . \Upsilon\right) \right] _ {\mathrm{ws}} \\ (\text { WSMTT - EQ - SUB - KEY - NATURAL }) \\ = \operatorname{embed} (\operatorname{suc} (v ^ {\prime})) \left[ \operatorname{embed} \left(\mathbf {Q} _ {\hat {\Gamma} ^ {\prime}, \Omega} ^ {\alpha \in \Lambda \Rightarrow \Theta}. \Psi . \Upsilon\right) \right] _ {\mathrm{ws}}. \quad (\text {Definition of embed} (\_)) \\ \end{array}
\]

We can now prove that the condition in Lemma 31 is actually always satisfied.

▶ Lemma 33. Given an atomic SFMTT substitution \(\vdash_{\mathrm{sf}} \sigma \operatorname{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m\), a lock telescope \(\Lambda: \operatorname{LockTele}(m \to n)\) and a variable \(\hat{\Delta}. \Lambda \vdash_{\mathrm{sf}} v \operatorname{var} @ n\), then we have that \(\hat{\Gamma}. \Lambda \vdash_{\mathrm{ws}} \operatorname{embed}\left(v [\sigma]_{\operatorname{asub}}^{\Lambda}\right) \equiv^{\sigma} \operatorname{embed}(v) [\operatorname{embed}(\sigma. \Lambda)]_{\mathrm{ws}} \operatorname{expr} @ n\).

Proof. This proof proceeds by induction on the atomic substitution  \( \sigma \) .

CASE \(\vdash_{\mathrm{sf}}!\) asub(Γ → ·) @ m (SF-ARENSUB-EMPTY)

In this case there can be no variable in the scoping context \(\cdot\). \(\Lambda\), so the statement we have to prove is vacuously true.

CASE \(\vdash_{\mathrm{sf}} \mathrm{id}^{\mathrm{a}} \operatorname{asub}(\hat{\Gamma} \to \hat{\Gamma}) @ m\) (SF-ARENSUB-ID)

Now \(\operatorname{embed}\left(v\left[\mathrm{id}^{\mathrm{a}}\right]_{\mathrm{asub}}^{\Lambda}\right) = \operatorname{embed}(v)\) and on the other hand

\[
\begin{array}{l} \operatorname{embed} (v) \left[ \operatorname{embed} \left(\mathrm{id} ^ {\mathrm{a}}. \Lambda\right) \right] _ {\mathrm{ws}} = \operatorname{embed} (v) [ \mathrm{id}. \Lambda ] _ {\mathrm{ws}} \quad (\text { Definition   of   } \operatorname{embed} (\underline {{\quad}})) \\ \equiv^ {\sigma} \operatorname{embed} (v) [ \mathrm{id} ] _ {\mathrm{ws}} \quad (\text { WSMTT - EQ - SUB - LOCK - ID }) \\ \equiv^ {\sigma} \operatorname{embed} (v). \quad \left(\text { WSMTT - EQ - EXPR - SUB - ID }\right) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{sf}} \text{ weaken}(\sigma) \text{ asub}(\hat{\Gamma} \cdot \mu \to \hat{\Delta}) @ m\) (SF-ARENSUB-WEAKEN)

In this case we can compute

\[
\begin{array}{l} \operatorname{embed} \left(v [ \text { weaken } (\sigma) ] _ {\text { asub }} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(v [ \sigma ] _ {\text { asub }} ^ {\Lambda} [ \pi . \Lambda ] _ {\text { aren }}\right) \tag {Equation(23)} \\ \equiv^ {\sigma} \operatorname{embed} \left(v [ \sigma ] _ {\text {asub}} ^ {\Lambda}\right) [ \operatorname{embed} (\pi . \Lambda) ] _ {\mathrm{ws}} \quad (\text {Lemma 30}) \\ \equiv^ {\sigma} \operatorname{embed} (v) [ \operatorname{embed} (\sigma . \Lambda) ] _ {\mathrm{ws}} [ \operatorname{embed} (\pi . \Lambda) ] _ {\mathrm{ws}} \quad (\text { Induction   hypothesis }) \\ \equiv^ {\sigma} \operatorname{embed} (v) \left[ (\operatorname{embed} (\sigma) \circ \pi). \Lambda \right] _ {\mathrm{ws}} \quad (*) \\ = \operatorname{embed} (v) [ \operatorname{embed} (\text { weaken } (\sigma). \Lambda) ] _ {\mathrm{ws}}. \quad \left(\text { Definition   of   } \operatorname{embed} (\underline {{\quad}})\right) \\ \end{array}
\]

In the step marked with (*) we made use of WSMTT-EQ-EXPR-SUB-COMPOSE and WSMTT-EQ-SUB-LOCK-COMPOSE.

34

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\vdash_{\mathrm{sf}} \sigma \cdot \widehat{\mathbf{a}}_{\mu} \operatorname{asub}(\hat{\Gamma} \cdot \widehat{\mathbf{a}}_{\mu} \to \hat{\Delta} \cdot \widehat{\mathbf{a}}_{\mu}) @ m\) (SF-ARENSUB-LOCK)

Then we have that

\[
\begin{array}{l} \operatorname{embed} \left(v [ \sigma . \widehat {\mathbf {a}} _ {\mu} ] _ {\text {asub}} ^ {\Lambda}\right) = \operatorname{embed} \left(v [ \sigma ] _ {\text {asub}} ^ {\widehat {\mathbf {a}} _ {\mu} \cdot \Lambda}\right) \tag {Equation(24)} \\ = \operatorname{embed} (v) [ \operatorname{embed} (\sigma . \widehat {\mathbf {a}} _ {\mu}. \Lambda) ] _ {\mathrm{ws}}. \quad (\text { Induction   hypothesis }) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{sf}} \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Theta \Rightarrow \Psi} \operatorname{asub}(\hat{\Gamma} \cdot \Psi \to \hat{\Gamma} \cdot \Theta) @ n\) (SF-ARENSUB-KEY)

In this case the result is a direct consequence of Lemma 32 because \( v \left[ \mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Theta \Rightarrow \Psi} \right]_{\mathrm{asub}}^{\Lambda} = \)

\[
v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi} \right] _ {\text {aren}} ^ {\Lambda}.
\]

CASE \(\vdash_{\mathrm{sf}} \sigma.t \operatorname{asub}(\hat{\Gamma} \to \hat{\Delta}.\mu) @ n\) (SF-ASUB-EXTEND)

Now we distinguish between two cases for the variable v.

CASE \(v = \mathbf{v}_0^\alpha\)

On the one hand, by Equation (26) we have that

\[
\operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha} [ \sigma . t ] _ {\text {asub}} ^ {\Lambda}\right) = \operatorname{embed} \left(t \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {a}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}}\right).
\]

On the other hand, we can compute

\[
\begin{array}{l} \operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) [ \operatorname{embed} ((\sigma . t). \Lambda) ] _ {\mathrm{ws}} \\ = \mathbf {v} _ {0} \left[ \mathbf {Q} _ {\hat {\Delta}} ^ {\alpha \in \widehat {\mathbf {a}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \left[ (\operatorname{embed} (\sigma). \operatorname{embed} (t)). \Lambda \right] _ {\mathrm{ws}} \\ \equiv^ {\sigma} \mathbf {v} _ {0} \left[ (\operatorname{embed} (\sigma). \operatorname{embed} (t)). \widehat {\mathbf {a}} _ {\mu} \right] _ {\mathrm{ws}} \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {a}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}} \\ \equiv^ {\sigma} \operatorname{embed} (t) \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {a}} _ {\mu} \Rightarrow \Lambda} \right] _ {\mathrm{ws}}. \quad \left(\text { WSMTT - EQ - SUB - KEY - NATURAL }\right) \\ \end{array}
\]

Combining these two computations, the result follows from Lemma 32.

CASE \(v = \operatorname{suc}(v')\)

The left-hand side now reduces to

\[
\begin{array}{l} \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right) [ \sigma . t ] _ {\text {asub}} ^ {\Lambda}\right) \\ = \operatorname{embed} \left(v ^ {\prime} [ \sigma ] _ {\text {asub}} ^ {\Lambda}\right) \tag {Equation(27)} \\ \equiv^ {\sigma} \operatorname{embed} (v ^ {\prime}) [ \operatorname{embed} (\sigma . \Lambda) ] _ {\mathrm{ws}}. \quad \text {(Induction hypothesis)} \\ \end{array}
\]

For the right-hand side, we have

\[
\begin{array}{l} \operatorname{embed} \left(\operatorname{suc} \left(v ^ {\prime}\right)\right) [ \operatorname{embed} ((\sigma . t). \Lambda) ] _ {\mathrm{ws}} \\ = \operatorname{embed} (v ^ {\prime}) [ \pi . \Lambda ] _ {\mathrm{ws}} [ (\operatorname{embed} (\sigma). \operatorname{embed} (t)). \Lambda ] _ {\mathrm{ws}} \quad (\text { Definition   of   embed } (\underline {{\quad}})) \\ \equiv^ {\sigma} \operatorname{embed} (v ^ {\prime}) \left[ (\pi \circ (\operatorname{embed} (\sigma). \operatorname{embed} (t))) \cdot \Lambda \right] _ {\mathrm{ws}} \\ \equiv^ {\sigma} \operatorname{embed} (v ^ {\prime}) [ \operatorname{embed} (\sigma . \Lambda) ] _ {\mathrm{ws}}. \\ \end{array}
\]

In the last two steps we made use of WSMTT-EQ-EXPR-SUB-COMPOSE, WSMTT-EQ-SUB-LOCK-COMPOSE and WSMTT-EQ-SUB-EXTEND-WEAKEN.

◀

J. Ceulemans, A. Nuyts and D. Devriese

35

▶ Proposition 34. Given an SFMTT expression \(\hat{\Delta} \vdash_{\mathrm{sf}} t \exp @ m\) and a substitution \(\vdash_{\mathrm{sf}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\), we have that \(\hat{\Gamma} \vdash_{\mathrm{ws}} \operatorname{embed}(t [\sigma]_{\mathrm{sub}}) \equiv^{\sigma} \operatorname{embed}(t) [\operatorname{embed}(\sigma)]_{\mathrm{ws}} \exp @ m\).

Proof. Because of the rules WSMTT-EQ-EXPR-SUB-ID and WSMTT-EQ-EXPR-SUB-COMPOSE, it suffices to prove this result for an atomic substitution  \( \sigma \) . This follows directly by combining Lemmas 31 and 33.

### 5.3 Proof of Theorem 25

Just like the completeness theorem, we will prove a more general statement than Theorem 25 that also takes substitution into account.

Theorem 35 (Soundness). For every WSMTT expression \(\hat{\Gamma} \vdash_{\mathrm{ws}} t \exp @ m\) we have \(\hat{\Gamma} \vdash_{\mathrm{ws}} \operatorname{embed}([t]) \equiv^{\sigma} t \exp @ m\) and for every WSMTT substitution \(\vdash_{\mathrm{ws}} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\) we have \(\vdash_{\mathrm{ws}} \operatorname{embed}([\sigma]) \equiv^{\sigma} \sigma \operatorname{sub}(\hat{\Gamma} \to \hat{\Delta}) @ m\).

Proof. The proof proceeds by induction on the expression t and the substitution  \( \sigma \) . All cases for the expression constructors that are shared between SFMTT and WSMTT are trivial from the induction hypotheses, but we show two of them (WSMTT-EXPR-ARROW and WSMTT-EXPR-LAM) as illustration. In particular, all constructors from Figure 2 are covered below.

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} (\mu \vdash T) \to S \exp @ n\) (WSMTT-EXPR-ARROW)

By definition of  \( [\_] \)  and embed(_) we have that

\[
\operatorname{embed} ([ [ (\mu \vdash T) \rightarrow S ] ]) = (\mu \vdash \operatorname{embed} ([ [ T ] ])) \rightarrow \operatorname{embed} ([ [ S ] ]).
\]

Hence the result follows from the induction hypothesis applied to the subexpressions \( T \) and \( S \).

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} \lambda^{\mu}(t) \exp @ n\) (WSMTT-EXPR-LAM)

Again, by expanding the definitions of  \( [\_] \)  and  \( \text{embed}(\_) \) , we get  \( \text{embed}([\lambda^{\mu}(t)]) = \lambda^{\mu}(\text{embed}([t])) \) , so that the result follows from the induction hypothesis applied to the subexpression t.

CASE \(\hat{\Gamma} \cdot \mu \cdot \widehat{\mathbf{B}}_{\mu} \vdash_{\mathrm{ws}} \mathbf{v}_0 \exp @ m\) (WSMTT-EXPR-VAR)

Now we have that

\[
\operatorname{embed} \left(\llbracket \mathbf {v} _ {0} \rrbracket\right) = \operatorname{embed} \left(\mathbf {v} _ {0} ^ {1 _ {\mu}}\right) = \mathbf {v} _ {0} \left[ \begin{array}{c} \mathbf {a} _ {\hat {\Gamma}, \mu} ^ {1 _ {\mu} \in \hat {\mathbf {B}} _ {\mu} \Rightarrow \hat {\mathbf {B}} _ {\mu}} \end{array} \right] _ {\mathrm{ws}}.
\]

This last expression is indeed \(\sigma\)-equivalent to \(\mathbf{v}_0\) because of WSMTT-EQ-SUB-KEY-UNIT and WSMTT-EQ-EXPR-SUB-ID.

CASE \(\hat{\Gamma} \vdash_{\mathrm{ws}} t[\sigma]_{\mathrm{ws}} \exp @ m\) (WSMTT-EXPR-SUB)

In this case we have

\[
\begin{array}{l} \operatorname{embed} \left(\llbracket t [ \sigma ] _ {\mathrm{ws}} \rrbracket\right) = \operatorname{embed} \left(\llbracket t \rrbracket [ [ [ \sigma ] ] _ {\mathrm{sub}}\right) \quad (\text { Definition   of } [ [ \_ ] ]) \\ \equiv^ {\sigma} \operatorname{embed} ([ [ t ] ]) [ \operatorname{embed} ([ [ \sigma ] ]) ] _ {\mathrm{ws}} \quad (\text { Proposition   34 }) \\ \equiv^ {\sigma} t [ \operatorname{embed} ([ [ \sigma ] ]) ] _ {\mathrm{ws}} \quad (\text { Induction   hypothesis   for } t) \\ \equiv^ {\sigma} t [ \sigma ] _ {\mathrm{ws}}. \quad (\text { Induction   hypothesis   for } \sigma) \\ \end{array}
\]

CASE \(\vdash_{\mathrm{ws}}!\operatorname {sub}(\hat{\Gamma}\to \cdot)\) @ \(m\) (WSMTT-SUB-EMPTY)

Since embed([!]) is a WSMTT substitution from \(\hat{\Gamma}\) to the empty scoping context \(\cdot\), the result follows immediately from WSMTT-EQ-SUB-EMPTY-UNIQUE.

36

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\vdash_{\mathrm{ws}}\) id sub(Γ → Γ) @ m (WSMTT-SUB-ID)

By the definition of translation and embedding, we immediately have embed([id]) = id.

CASE \(\vdash_{\mathrm{ws}}\pi \operatorname {sub}(\hat{\Gamma}.\mu \to \hat{\Gamma})@n\) (WSMTT-SUB-WEAKEN)

Now we have that

\[
\operatorname{embed} ([ \pi ]) = \operatorname{embed} (\mathrm{id} \circledast \text { weaken } (\mathrm{id} ^ {\mathrm{a}})) \quad \text {(Definition of [\_ ] and Equation (2))}
\]

\[
= \mathrm{id} \circ (\mathrm{id} \circ \pi). \quad \text {(Definition of embed} (\_))
\]

This last substitution is indeed \(\sigma\)-equivalent to \(\pi\) by WSMTT-EQ-SUB-ID-LEFT.

CASE \(\vdash_{\mathrm{ws}}\sigma \circ \tau \operatorname {sub}(\hat{\Gamma}\to \hat{\Xi})@m\) (WSMTT-SUB-COMPOSE)

Now we compute that  \( \text{embed}([\sigma \circ \tau]) = \text{embed}([\sigma] + [\tau]) \) . Since the embedding of a sequence of atomic SFMTT substitutions is the composition of the embedding of these atomic substitutions and since WSMTT substitution composition is associative up to  \( \sigma \) -equivalence, we have that  \( \text{embed}([\sigma] + [\tau]) \equiv^{\sigma} \text{embed}([\sigma]) \circ \text{embed}([\tau]) \) . From this the result follows via the induction hypothesis applied to  \( \sigma \)  and  \( \tau \) .

CASE \(\vdash_{\mathrm{ws}}\sigma .\widehat{\mathbf{\Omega}}_{\mu}\operatorname {sub}(\hat{\Gamma}.\widehat{\mathbf{\Omega}}_{\mu}\to \hat{\Delta}.\widehat{\mathbf{\Omega}}_{\mu})@m\) (WSMTT-SUB-LOCK)

In this case we get that  \( \text{embed}([\sigma, \widehat{\mathbf{\Omega}}_{\mu}]) = \text{embed}([\sigma], \widehat{\mathbf{\Omega}}_{\mu}) \equiv^{\sigma} \text{embed}([\sigma]) \cdot \widehat{\mathbf{\Omega}}_{\mu} \) , where the last equivalence follows from WSMTT-EQ-SUB-LOCK-ID and WSMTT-EQ-SUB-LOCK-COMPOSE. The desired result is then a consequence of the induction hypothesis applied to  \( \sigma \) .

CASE \(\vdash_{\mathrm{ws}}\mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Theta \Rightarrow \Psi}\operatorname {sub}(\hat{\Gamma}.\Psi \to \hat{\Gamma}.\Theta)\) @ \(n\) (WSMTT-SUB-KEY)

We can now compute that

\[
\operatorname{embed} \left(\llbracket \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi} \rrbracket\right) = \operatorname{embed} \left(\mathrm{id} \circledast \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi}\right) \quad (\text { Definition   of } [ \_ ])
\]

\[
= \mathrm{id} \circ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi}, \quad (\text { Definition   of   embed } (\_))
\]

which is indeed \(\sigma\)-equivalent to \(\mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Theta \Rightarrow \Psi}\) because of WSMTT-EQ-SUB-ID-LEFT

CASE \(\vdash_{\mathrm{ws}}\sigma .t\) sub(Γ → Δ.μ) @ n (WSMTT-SUB-EXTEND)

Expanding the definitions of  \( [\_] \)  and embed( \( \_ \) ), we have that

\[
\operatorname{embed} ([ \sigma . t ]) = \operatorname{embed} \left(\llbracket \sigma \rrbracket^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, [ [ t ] ])\right) = \operatorname{embed} \left(\llbracket \sigma \rrbracket^ {+}\right) \circ (\mathrm{id.embed} ([ [ t ] ])).
\]

By Lemma 27 we know that \(\mathsf{embed}\left(\llbracket \sigma \rrbracket^{+}\right) \equiv^{\sigma} \mathsf{embed}(\llbracket \sigma \rrbracket)^{+}\) and combining this with the induction hypothesis for \(\sigma\) and \(t\), we get that

\[
\operatorname{embed} ([ \sigma . t ]) \equiv^ {\sigma} \sigma^ {+} \circ (\mathrm{id}. t).
\]

This last substitution can be proven \(\sigma\)-equivalent to \(\sigma.t\) by the rules WSMTT-EQ-SUB-EXTEND-ETA, WSMTT-EQ-SUB-EXTEND-WEAKEN and WSMTT-EQ-EXPR-EXTEND-VAR.

## References

1 Joris Ceulemans, Andreas Nuyts, and Dominique Devriese. A sound and complete substitution algorithm for multimode type theory. In Delia Kesner, Eduardo Hermo Reyes, and Benno van den Berg, editors, 29th International Conference on Types for Proofs and Programs (TYPES 2023), volume 303 of LIPIcs, 2024. to appear.

2 Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. Multimodal Dependent Type Theory. Logical Methods in Computer Science, Volume 17, Issue 3, July 2021. URL: https://lmcs.episciences.org/7713, doi:10.46298/lmcs-17(3:11)2021.