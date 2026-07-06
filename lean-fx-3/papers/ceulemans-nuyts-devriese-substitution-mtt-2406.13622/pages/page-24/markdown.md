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