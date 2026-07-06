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