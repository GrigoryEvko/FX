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