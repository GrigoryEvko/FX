(c) We have

\[
\exists_ {U} ^ {\prime \Psi} \exists_ {U} ^ {\prime \Psi} (W, \psi) = \exists_ {U} ^ {\prime \Psi} (W \times U, \psi \times \mathbf {y} U) \cong (W \times U, \pi_ {1} \circ (\psi \times \mathbf {y} U)) \tag {36}
\]

and of course \(\pi_1\circ (\psi \times \mathbf{y}U) = \psi \circ \pi_1:W\times U\to \Psi\)

Theorem 4.1.12 (Presheafwise quotient theorem \( ^{§A} \) ). If  \( \sqcup \times U : W \to V \)  is T-slice (or equivalently presheafwise, for either notion of shard-freedom) fully faithful and shard-free, then

1. (Obsolete.) \(\exists_{U}^{\prime \Psi}:\mathcal{W} / \Psi \simeq (\mathcal{V} / / U) / (\Psi \ltimes \mathbf{y}U,\pi_2)\) is an equivalence of categories.\(^{15}\)
2. \(\exists_{U}^{\prime \Psi}:\mathcal{W} / \Psi \simeq \mathcal{V} / / (\Psi \ltimes \mathbf{y}U)\) is an equivalence of categories.

### 4.2 Acting on presheaves

Proposition 4.2.1. The functor \(\sqcup \ltimes \mathbf{y}U:\widehat{\mathcal{W}}\to \widehat{\mathcal{V}}\)

1. is a multiplier for yU,
2. has the property that \(\exists_{\mathbf{y}U}:\widehat{\mathcal{W}}\to \widehat{\mathcal{V}} /\mathbf{y}U\) is naturally isomorphic to \((\exists_U)_{!}:\widehat{\mathcal{W}}\to \widehat{\mathcal{V} / U}\) over the equivalence between their codomains,
3. has the property that the slice functor \(\exists_{\mathbf{y}U}^{\prime \Psi}:\widehat{\mathcal{W}} /\Psi \to \widehat{\mathcal{V}} /\big(\Psi \ltimes \mathbf{y}U\big)\) is naturally isomorphic to the left lifting of the elements functor \((\exists_U^{\prime \Psi})_{!}:\widehat{\mathcal{W} / \Psi}\to \widehat{\mathcal{V} / (\Psi\ltimes\mathbf{y}U)}\) over the equivalences between their domains and codomains,
4. is copointed if and only if \(\sqcup \ltimes U\) is,
5. is a comonad if and only if \(\sqcup \ltimes U\) is,
6. is cartesian if and only if \(\sqcup \ltimes U\) is,
7. is \(\top\)-slice fully faithful if and only if \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful,
8. is slicewise fully faithful if and only if \(\sqcup \ltimes U\) is presheafwise fully faithful,
9. is \(\top\)-slice right adjoint if \(\sqcup \ltimes U\) is \(\top\)-slice right adjoint, and

- \(\exists_{\mathbf{y}U}\) is naturally isomorphic to \((\exists_U)_!\) over the equivalence \(\widehat{\mathcal{V}/U} \simeq \widehat{\mathcal{V}}/\mathbf{y}U\),
- \(\exists_{\mathbf{y}U}^{\prime \Psi}\) is naturally isomorphic to \((\exists_U^{\prime \Psi})_!\) over the equivalences between their domain and codomain.

Proof. 1. Since \(\top \ltimes \mathbf{y}U \cong \mathbf{y}\top \ltimes \mathbf{y}U \cong \mathbf{y}(\top \ltimes U) \cong \mathbf{y}U\). We use, in order, that \(\mathbf{y}\) preserves the terminal object, that \(F_{!}\circ \mathbf{y} \cong \mathbf{y}\circ F\) (theorem 2.3.2) and that \(\sqcup \ltimes U\) is a multiplier for \(U\).

2. The functor \((\exists_U)_{!}\) sends a presheaf \(\Gamma \in \widehat{\mathcal{W}}\) to the presheaf in \(\widehat{\mathcal{V} / U}\) determined by

\[
(V, \varphi) \Rightarrow (\exists_ {U}) _ {!} \Gamma = \exists W. ((V, \varphi) \rightarrow \exists_ {U} W) \times (W \Rightarrow \Gamma). \tag {37}
\]

On the other hand, \(\exists_{\mathbf{y}U}\Gamma\) is the slice object \((\Gamma \ltimes \mathbf{y}U,\pi_2)\in \widehat{\mathcal{V}} /\mathbf{y}U\). Taking the preimage of \(\pi_2\) (proposition 2.3.6), we get a presheaf \(\Delta \in \widehat{\mathcal{V} / U}\) determined by

\[
\begin{array}{l} (V, \varphi) \Rightarrow \Delta = \left\{\left(\gamma \ltimes \mathbf {y} U\right) \circ \chi : V \Rightarrow \Gamma \ltimes \mathbf {y} U \mid \pi_ {2} \circ (\gamma \ltimes \mathbf {y} U) \circ \chi = \varphi \right\} \\ = \left\{\left(\gamma \ltimes \mathbf {y} U\right) \circ \chi : V \Rightarrow \Gamma \ltimes \mathbf {y} U \mid \pi_ {2} \circ \chi = \varphi \right\} \\ \cong \exists W. (\chi : V \to W \ltimes U) \times (\gamma : W \Rightarrow \Gamma) \times (\pi_ {2} \circ \chi = \varphi) \\ \cong \exists W. (\chi : (V, \varphi) \to \exists_ {U} W) \times (W \Rightarrow \Gamma). \\ \end{array}
\]

Indeed, we see that these functors are isomorphic.

\( ^{15} \) We use a slight abuse of notation as  \( (\mathcal{V}//U)/(\Psi \ltimes \mathbf{y}U, \pi_{2}) \)  is in fact neither a slice category nor a category of elements.

30