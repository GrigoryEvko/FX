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