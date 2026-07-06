- An indirectly dimensionally split element \((V, \psi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) that is not in the image of \(\exists_{U}^{\prime \Psi}\) even up to isomorphism, will be called an indirect shard\(^{\S A}\) of the multiplier.

- Directly presheafwise shard-free\(^{\S A}\) if for all \(\Psi\), the functor \(\exists_{U}^{\prime \Psi}\) is essentially surjective on elements \((V, \varphi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) such that \(\varphi: V \to \Psi \ltimes \mathbf{y}U\) is directly dimensionally split:

- We say that \(\varphi : V \Rightarrow \Psi \ltimes \mathbf{y}U\) is directly dimensionally split with direct dimensional section \(\chi : W \ltimes U \to V\) if \(\varphi \circ \chi\) is of the form \(\psi \ltimes \mathbf{y}U\). The section can alternatively be presented as a morphism of elements \(\chi : \exists_{U}^{\prime \Psi}(W, \psi) \to (V, \varphi)\).

- We denote the full subcategory of directly dimensionally split elements as \(\mathcal{V} // (\Psi \ltimes \mathbf{y}U)\).

- A directly dimensionally split element \((V, \psi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) that is not in the image of \(\exists_{U}^{\prime \Psi}\) even up to isomorphism, will be called a direct shard\(^{\S A}\) of the multiplier.

- Presheafwise right adjoint\(^{\S A}\) if for all \(\Psi\), the functor \(\exists_{U}^{\prime \Psi}\) has a left adjoint \(\exists_{U}^{\prime \Psi}: \mathcal{V}/(\Psi \ltimes \mathbf{y}U) \to \mathcal{W}/\Psi\). We denote the unit as \(\text{copy}_{U}^{\prime \Psi}: \text{Id} \to \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}\) and the co-unit as \(\text{drop}_{U}^{\prime \Psi}: \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi} \to \text{Id}\).

This is indeed a generalization:

Proposition 4.1.2. The functor \(\exists_{U}^{\prime \mathbf{y}W_0}: \mathcal{W} / \mathbf{y}W_0 \to \mathcal{V} / (\mathbf{y}W_0 \ltimes \mathbf{y}U)\) is equal to \(\exists_{U}^{\prime W_0}: \mathcal{W} / W_0 \to \mathcal{V} / (W_0 \ltimes U)\) over the obvious isomorphisms between their domains and codomains. Hence, each of the presheafwise notions implies the slicewise notion (definition 3.5.1). Moreover, each of the \(\top\)-slice elemental notions implies the basic \(\top\)-slice notion.

Proof. Most of this is straightforward after extracting the construction of the isomorphism \(\mathbf{y}W_0\times \mathbf{y}U\cong\) \(\mathbf{y}(W_0\times U)\) from the proof of theorem 2.3.2. To see the last claim, note that

\[
\{\varphi : W \ltimes U \Rightarrow \mathbf {y} W _ {0} \ltimes \mathbf {y} U | \pi_ {2} \circ \varphi = \pi_ {2} \} \cong ((W \ltimes U, \pi_ {2}) \rightarrow (W _ {0} \ltimes U, \pi_ {2})) = (\lrcorner_ {U} W \rightarrow \lrcorner_ {U} W _ {0}).
\]

So if injectivity/surjectivity holds for all W and  \( W_{0} \) , then we can conclude that  \( \perp_{U} \)  is faithful/full. ☐

Note that both notions of presheafwise shard-freedom are well-defined:

Proposition 4.1.3. 1. (Obsolete.) The functor \(\exists_{U}^{\prime \Psi}\) produces indirectly dimensionally split elements.

2. The functor \(\exists_{U}^{\prime \Psi}\) produces directly dimensionally split elements.

3. Directly dimensionally split elements are indirectly dimensionally split with the same section. Hence, direct shards are indirect shards and indirect presheafwise shard-freedom implies direct presheafwise shard-freedom.

Proof. See proposition 3.5.3.

Proposition 4.1.4. If \(\sqcup \ltimes U\) is \(\top\)-slice faithful, then it is presheafwise faithful.

Proof. Analogous to proposition 3.5.4.

Proposition 4.1.5. If \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful, then it is \(\top\)-slice elementally faithful.

Proof. We have

\[
\begin{array}{l} \{\varphi : W \ltimes U \Rightarrow \Psi \ltimes \mathbf {y} U \mid \pi_ {2} \circ \varphi = \pi_ {2} \} \\ \cong \exists W _ {0}. (\varphi^ {\prime}: W \ltimes U \to W _ {0} \ltimes U) \times (\psi : W _ {0} \Rightarrow \Psi) \times (\pi_ {2} \circ (\psi \ltimes \mathbf {y} U) \circ \varphi^ {\prime} = \pi_ {2}) \\ \cong \exists W _ {0}. (\varphi^ {\prime}: W \ltimes U \to W _ {0} \ltimes U) \times (\psi : W _ {0} \Rightarrow \Psi) \times (\pi_ {2} \circ \varphi^ {\prime} = \pi_ {2}) \\ \cong \exists W _ {0}. (\varphi^ {\prime}: \mathbb {1} _ {U} W \rightarrow \mathbb {1} _ {U} W _ {0}) \times (\psi : W _ {0} \Rightarrow \Psi) \tag {30} \\ \end{array}
\]

and

\[
(W \Rightarrow \Psi) \cong \exists W _ {0}. (W \rightarrow W _ {0}) \times (W _ {0} \Rightarrow \Psi). \tag {31}
\]

26