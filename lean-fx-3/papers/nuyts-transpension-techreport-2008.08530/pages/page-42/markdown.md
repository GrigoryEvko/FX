3. This follows from theorem 2.3.18.

4. We show that \(\Sigma^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_1|}\cong \forall_{\mathbf{y}U}^{\Psi_2|}\Sigma^{\tau |}\). Pick a presheaf \(\Gamma\) over \(\mathcal{V} / (\Psi_1\times \mathbf{y}U)\). On the one hand, we have:

\[
\begin{array}{l} (W _ {2}, \psi_ {2} ^ {W _ {2} \Rightarrow \Psi_ {2}}) \Rightarrow \Sigma^ {\sigma |} \forall_ {\mathbf {y} U} ^ {\Psi_ {1} |} \Gamma \\ = \exists (W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}). (\theta : (W _ {2}, \psi_ {2}) \rightarrow \Sigma^ {\prime \sigma} (W _ {1}, \psi_ {1})) \times ((W _ {1}, \psi_ {1}) \Rightarrow \forall_ {\mathbf {y} U} ^ {\Psi_ {1}} | \Gamma) \\ = \exists (W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}). (\theta : (W _ {2}, \psi_ {2}) \rightarrow (W _ {1}, \sigma \circ \psi_ {1})) \times ((W _ {1} \ltimes U, \psi_ {1} \ltimes \mathbf {y} U) \Rightarrow \Gamma) \\ \cong \exists W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \theta^ {W _ {2} \rightarrow W _ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1} \circ \theta) \times ((W _ {1} \ltimes U, \psi_ {1} \ltimes \mathbf {y} U) \Rightarrow \Gamma) \\ \end{array}
\]

We now absorb \(\theta\) into \(\psi_{1}\):

\[
\cong \psi_ {1} ^ {W _ {2} \Rightarrow \Psi_ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1}) \times ((W _ {2} \ltimes U, \psi_ {1} \ltimes \mathbf {y} U) \Rightarrow \Gamma).
\]

On the other hand, we have:

\[
\begin{array}{l} (W _ {2}, \psi_ {2} ^ {W _ {2} \Rightarrow \Psi_ {2}}) \Rightarrow \forall_ {\mathbf {y} U} ^ {\Psi_ {2} |} \Sigma^ {\tau |} \Gamma \\ = \left(W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U\right) \Rightarrow \Sigma^ {\tau |} \Gamma \\ = \exists (V _ {1}, \varphi_ {1} ^ {V _ {1} \Rightarrow \Psi_ {1} \ltimes \mathbf {y} U}). (\omega : (W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U) \rightarrow \Sigma^ {\prime \tau} (V _ {1}, \varphi_ {1})) \times ((V _ {1}, \varphi_ {1}) \Rightarrow \Gamma) \\ = \exists (V _ {1}, \varphi_ {1} ^ {V _ {1} \Rightarrow \Psi_ {1} \ltimes \mathbf {y} U}). (\omega : (W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U) \rightarrow (V _ {1}, (\sigma \ltimes \mathbf {y} U) \circ \varphi_ {1})) \times ((V _ {1}, \varphi_ {1}) \Rightarrow \Gamma) \\ \end{array}
\]

We now deconstruct \(\varphi_{1} = (\psi_{1}\ltimes \mathbf{y}U)\circ \chi\)

\[
\begin{array}{l} \cong \exists V _ {1}, W _ {1}, \chi^ {V _ {1} \rightarrow W _ {1} \ltimes U}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}. \\ (\omega : (W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U) \rightarrow (V _ {1}, ((\sigma \circ \psi_ {1}) \ltimes \mathbf {y} U) \circ \chi)) \times ((V _ {1}, (\psi_ {1} \ltimes \mathbf {y} U) \circ \chi) \Rightarrow \Gamma) \\ \cong \exists V _ {1}, W _ {1}, \chi^ {V _ {1} \rightarrow W _ {1} \ltimes U}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \omega^ {W _ {2} \ltimes U \rightarrow V _ {1}}. \\ (\psi_ {2} \ltimes \mathbf {y} U = ((\sigma \circ \psi_ {1}) \ltimes \mathbf {y} U) \circ \chi \circ \omega) \times ((V _ {1}, (\psi_ {1} \ltimes \mathbf {y} U) \circ \chi) \Rightarrow \Gamma) \\ \end{array}
\]

We now absorb \(\omega\) into \(\chi\):

\[
\begin{array}{l} \cong \exists W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \chi^ {W _ {2} \ltimes U \rightarrow W _ {1} \ltimes U}. \\ \left(\psi_ {2} \ltimes \mathbf {y} U = \left(\left(\sigma \circ \psi_ {1}\right) \ltimes \mathbf {y} U\right) \circ \chi\right) \times \left(\left(W _ {2} \ltimes U, \left(\psi_ {1} \ltimes \mathbf {y} U\right) \circ \chi\right) \Rightarrow \Gamma\right) \\ \text {   Let   } \chi = \mathbb {J} _ {U} ^ {\prime \Psi_ {2}} \theta : \mathbb {J} _ {U} ^ {\prime \Psi_ {2}} (W _ {2}, \psi_ {2}) \to \mathbb {J} _ {U} ^ {\prime \Psi_ {2}} (W _ {1}, \sigma \circ \psi_ {1}): \\ \cong \exists W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \theta^ {W _ {2} \rightarrow W _ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1} \circ \theta) \times ((W _ {2} \ltimes U, ((\psi_ {1} \circ \theta) \ltimes \mathbf {y} U)) \Rightarrow \Gamma) \\ \end{array}
\]

We now absorb \(\theta\) into \(\psi_{1}\):

\[
\cong \psi_ {1} ^ {W _ {2} \Rightarrow \Psi_ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1}) \times ((W _ {2} \ltimes U, (\psi_ {1} \ltimes \mathbf {y} U)) \Rightarrow \Gamma)
\]

This proves the isomorphism. The rest follows from lemma 2.1.2.

### 6.4 Multiplier and modality

Theorem 6.4.1. Assume a commutative diagram (up to natural isomorphism \(\nu : F(\sqcup \ltimes U) \cong G_{\sqcup} \ltimes U'\))

\[
\begin{array}{c} \mathcal {W} \xrightarrow {G} \mathcal {W} ^ {\prime} \\ \sqcup \ltimes U \Bigg | _ {\downarrow} \quad \Bigg | _ {\downarrow} \sqcup \ltimes U ^ {\prime} \\ \mathcal {V} \xrightarrow [ F ]{} \mathcal {V} ^ {\prime} \end{array} \tag {56}
\]

where \(\sqcup \ltimes U\) and \(\sqcup \ltimes U'\) are multipliers for \(U\) and \(U'\).

Then \(\Sigma^{\prime / \nu}\) is a strictly invertible functor and hence we have

\[
\Sigma^ {\nu_ {i} |} \cong \Omega^ {\nu_ {i} ^ {- 1} |} \cong \Pi^ {\nu_ {i} |} \cong \delta^ {\nu_ {i} ^ {- 1} |} \quad \Sigma^ {\nu_ {i} ^ {- 1} |} \cong \Omega^ {\nu_ {i} |} \cong \Pi^ {\nu_ {i} ^ {- 1} |} \cong \delta^ {\nu_ {i} |}, \tag {57}
\]

42