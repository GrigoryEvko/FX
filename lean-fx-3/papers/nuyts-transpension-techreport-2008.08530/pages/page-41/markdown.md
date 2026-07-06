where every statement holds if the mentioned functors exist.

Proof. It is evident from the definitions that the given diagram commutes. Then by applying \(\sqcup^{*}\), we find the that \(\Omega^{\sigma}|G^{\Psi_2|*} = G^{\Psi_1|*}\Omega^{G_1\sigma|}\). The rest of the table then follows by lemma 2.1.2.

Remark 6.2.2. • If \(\sigma = \pi : \Psi.A \to \Psi\), then this says something about weakening and the \(\Sigma\)- and \(\Pi\)-types over \(A\).

- If \( G_{!} \) moreover happens to be a CwF morphism, then this relates weakening and the \( \Sigma \)- and \( \Pi \)-types over \( A \) to those over \( G_{!}A \).
- If \(\sqcup \times U\) is a cartesian multiplier and we take \(\sigma = \pi_1: \Psi \times \mathbf{y}U \to \Psi\), then by theorem 4.1.11, this says something about \(\exists_{\mathbf{y}U}^{\Psi|} \dashv \exists_{\mathbf{y}U}^{\Psi|} \dashv \forall_{\mathbf{y}U}^{\Psi|} \dashv \emptyset_{\mathbf{y}U}^{\Psi|}\).

### 6.3 Multiplier and substitution

If, in section 6.2, we take \(G\) equal to some multiplier \(\sqcup \ltimes U:\mathcal{W}\to \mathcal{V}\), then we have

\[
G ^ {/ \Psi} = \exists_ {U} ^ {/ \Psi}, \quad G _ {!} = \sqcup \ltimes \mathbf {y} U, \quad G _ {!} ^ {\Psi |} = \exists_ {\mathbf {y} U} ^ {\Psi |}, \quad G ^ {\Psi | *} = \forall_ {\mathbf {y} U} ^ {\Psi |}, \quad G _ {*} ^ {\Psi |} = \emptyset_ {\mathbf {y} U} ^ {\Psi |}. \tag {53}
\]

This immediately yields the general case of the following theorem:

Theorem 6.3.1. Assume a multiplier \(\sqcup \ltimes U:\mathcal{W}\to \mathcal{V}\) and a morphism \(\sigma :\Psi_1\to \Psi_2\) in \(\widehat{\mathcal{W}}\). Write \(\tau = \sigma \ltimes \mathbf{y}U\). Then we have:

|   | \( \exists \) | \( \bot \) | \( \forall \) | \( \emptyset \)  |
| --- | --- | --- | --- | --- |
|  \( \Sigma \) | \( \Sigma^{\sigma}|\exists_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{1} \exists_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\tau}| \) | \( \Sigma^{\tau}|\exists_{\mathbf{y}U}^{\Psi_1}| \cong \exists_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\sigma}| \) | \( \Sigma^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_1}| \triangleright_{1} \forall_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\tau}| \) | \( \Sigma^{\tau}|\emptyset_{\mathbf{y}U}^{\Psi_1}| \triangleright_{2} \emptyset_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\sigma}| \)  |
|  \( \Omega \) | \( \Omega^{\sigma}|\exists_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{2} \exists_{\mathbf{y}U}^{\Psi_1}|\Omega^{\tau}| \) | \( \Omega^{\tau}|\exists_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{1} \exists_{\mathbf{y}U}^{\Psi_1}|\Omega^{\sigma}| \) | \( \Omega^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_2}| = \forall_{\mathbf{y}U}^{\Psi_1}|\Omega^{\tau}| \) | \( \Omega^{\tau}|\emptyset_{\mathbf{y}U}^{\Psi_2}| \triangleright_{1} \emptyset_{\mathbf{y}U}^{\Psi_1}|\Omega^{\sigma}| \)  |
|  \( \Pi \) | \( \Pi^{\sigma}|\exists_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{3} \exists_{\mathbf{y}U}^{\Psi_2}|\Pi^{\tau}| \) | \( \Pi^{\tau}|\exists_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{2} \exists_{\mathbf{y}U}^{\Psi_2}|\Pi^{\sigma}| \) | \( \Pi^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{1} \forall_{\mathbf{y}U}^{\Psi_2}|\Pi^{\tau}| \) | \( \Pi^{\tau}|\emptyset_{\mathbf{y}U}^{\Psi_1}| \cong \emptyset_{\mathbf{y}U}^{\Psi_2}|\Pi^{\sigma}| \)  |
|  \( \$ \) |  | \( \$\tau|\exists_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{3} \exists_{\mathbf{y}U}^{\Psi_1}|\$\sigma| \) | \( \$\sigma|\forall_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{2} \forall_{\mathbf{y}U}^{\Psi_1}|\$\tau| \) | \( \$\tau|\emptyset_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{1} \emptyset_{\mathbf{y}U}^{\Psi_1}|\$\sigma| \)  |

where every statement holds if the mentioned functors exist, and where

1. In general, \(\triangleleft^1\) means \(\leftarrow\), \(\triangleright_1\) means \(\rightarrow\) and the other symbols mean nothing.
2. If \(\sqcup \ltimes U\) is \(\top\)-slice right adjoint, then \(\triangleleft^1\) upgrades to \(\cong\) and \(\triangleleft^2\) upgrades to \(\leftarrow\).
3. If \(\sqcup \ltimes U\) is cartesian (hence \(\top\)-slice right adjoint), then \(\triangleleft^1\) and \(\triangleleft^2\) upgade to \(\cong\) and \(\triangleleft^3\) upgrades to \(\leftarrow\).
4. If \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful, then we have

\[
\Sigma^ {\sigma |} \forall_ {\mathbf {y} U} ^ {\Psi_ {1} |} \cong \forall_ {\mathbf {y} U} ^ {\Psi_ {2} |} \Sigma^ {\tau |}: \overbrace {\mathcal {V} / (\Psi_ {1} \ltimes \mathbf {y} U)} ^ {\text {   }} \to \widehat {\mathcal {W} / \Psi_ {2}} \tag {55}
\]

so that \(\triangleright_{1}\) upgrades to \(\cong\) and \(\triangleright_{2}\) upgrades to \(\rightarrow\).

Proof. 1. The general case is a corollary of theorem 6.2.1 for \( G = \sqcup \ltimes U \).

2. To prove the \(\top\)-slice right adjoint case, we show in the base category that \(\Sigma^{\prime\sigma}\exists_{U}^{\prime\Psi_{1}} = \exists_{U}^{\prime\Psi_{2}}\Sigma^{\prime(\sigma\times\mathbf{y}U)}\). We use the construction of \(\exists_{U}^{\prime\Psi}\) in the proof of presheafwise right adjointness (proposition 4.1.9). On one hand, we have:

\[
\Sigma^ {\prime \sigma} \exists_ {U} ^ {\prime \Psi_ {1}} (V, (\psi_ {1} ^ {W _ {0} \Rightarrow \Psi_ {1}} \ltimes \mathbf {y} U) \circ \varphi^ {V \Rightarrow W _ {0} \ltimes U}) = \Sigma^ {\prime \sigma} \Sigma^ {\prime \psi_ {1}} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi) = \Sigma^ {\prime \sigma \circ \psi_ {1}} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi).
\]

On the other hand:

\[
\begin{array}{l} \exists_ {U} ^ {\prime \Psi_ {2}} \Sigma^ {\prime (\sigma \ltimes \mathbf {y} U)} (V, (\psi_ {1} ^ {W _ {0} \Rightarrow \Psi_ {1}} \ltimes \mathbf {y} U) \circ \varphi^ {V \Rightarrow W _ {0} \ltimes U}) = \exists_ {U} ^ {\prime \Psi_ {2}} (V, ((\sigma \circ \psi_ {1}) \ltimes \mathbf {y} U) \circ \varphi) \\ = \Sigma^ {\prime \sigma \circ \psi_ {1}} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi). \\ \end{array}
\]

41