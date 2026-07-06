CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

### 3.4.3 Complicial sets as a model of  \( (\infty,\omega) \) -categories

Proposition 3.4.3.1. For any \(n \in \mathbb{N} \cup \{\omega\}\), the composite

\[
j ^ {n + 1} \circ i ^ {n + 1}: \mathrm{tPsh} (\Delta) ^ {n + 1} \to \mathrm{tPsh} (\Delta) ^ {n + 1}
\]

is a Quillen equivalence.

Proof. Using theorem 2.2.4.2, and propositions 3.4.1.4 and 3.4.2.2, we have a zigzag of weak equivalences

\[
j ^ {\omega} \circ i ^ {\omega} (\mathbf {D} _ {n}) \rightarrow j ^ {\omega} \circ i ^ {\omega} (\mathrm{N} (\mathbf {D} _ {n})) \rightarrow \mathrm{N} (\mathbf {D} _ {n}) \leftarrow \mathbf {D} _ {n}
\]

natural in \( n \). The corollary 2.4.4.15 then provides a zigzag of weakly invertible natural transformations

\[
j ^ {\omega} \circ i ^ {\omega} \leftrightarrow i d _ {\mathrm{tPsh} (\Delta) ^ {\omega}}.
\]

This also induces for any integer n a zigzag of weakly invertible natural transformations

\[
j ^ {n + 1} \circ i ^ {n + 1} \leftrightarrow i d _ {\mathrm{tPsh} (\Delta) ^ {n + 1}}.
\]

□

Theorem 3.4.3.2. For \( n < \omega \), the model category \( \mathrm{tPsh}(\Delta)^n \) is a model of \( (\infty, n) \)-categories.

Proof. To demonstrate the theorem, we will proceed by induction. The initialization is exactly the theorem 2.14 of [BOR21]. Suppose now the result is true at the stage n. We can apply [BSP21, example 15.8] which implies that the  \( (\infty,1) \) -category represented by  \( \operatorname{Seg}(\operatorname{tPsh}(\Delta)^{n}) \)  is a model of  \( (\infty,n+1) \) -categories, and according to 3.1.2.10, so is  \( \operatorname{tSeg}(\operatorname{tPsh}(\Delta)^{n}) \) . Eventually, the proposition 3.4.1.4 and 3.4.2.2 imply that the functor

\[
i ^ {n + 1} \circ j ^ {n + 1}: \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n}) \to \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n})
\]

preserves globes up to homotopy. Proposition 15.10 of [BSP21] states that \( i^{n+1} \circ j^{n+1} \) is a Quillen equivalence, and proposition 3.4.3.1 implies that \( j^{n+1} \circ i^{n+1} \) is a Quillen equivalence. The functor \( i^{n+1} \) is then a Quillen equivalence, and \( \mathrm{tPsh}(\Delta)^{n+1} \) is a model of \( (\infty, n+1) \)-categories.

3.4.3.3. For an integer n, we consider the model structure on  \( \mathrm{Psh}_{\Delta}(\Theta_{n}) \)  (resp.  \( \mathrm{Psh}_{\Delta}(\Theta) \) ) obtained as the left Bousfield localization of the projective model structure along the set of map  \( W_{n} \)  (resp. W) defined in paragraph 1.1.2.14. For any  \( n < \omega \) , the inclusion  \( \Theta_{n} \to \Theta \)  induces a Quillen adjunction

\[
\iota^ {n}: \mathrm{Psh} _ {\Delta} (\Theta_ {n}) \xrightarrow [ \leftarrow ]{\perp} \mathrm{Psh} _ {\Delta} (\Theta): \tau_ {n} \tag {3.4.3.4}
\]

168