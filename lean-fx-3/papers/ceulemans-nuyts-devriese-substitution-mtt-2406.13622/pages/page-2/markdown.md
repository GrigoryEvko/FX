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