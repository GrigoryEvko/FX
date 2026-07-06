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