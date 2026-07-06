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