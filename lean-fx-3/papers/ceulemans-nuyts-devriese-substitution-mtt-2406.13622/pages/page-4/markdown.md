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