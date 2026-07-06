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