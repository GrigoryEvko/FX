CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

(2) as well as units

\[
X _ {n} \rightarrow X _ {n + 1}
\]

which associate to an \(n\)-cell \(x\), a \((n + 1)\)-cell \(\mathbb{I}_x\),

and satisfying the following axioms:

(1) \(\forall x\in X_n,\pi_n^\epsilon (\mathbb{I}_x) = x.\)
(2) \(\pi_k^+ (x\circ_ny) = \pi_k^+ (x)\) and \(\pi_k^- (x\circ_ny) = \pi_k^- (y)\) whenever the composition is defined and \(k\leqslant n\)
(3) \(\pi_k^\epsilon (x\circ_ny) = \pi_k^\epsilon (x)\circ_n\pi_k^\epsilon (y)\) whenever the composition is defined and \(k > n\)
(4) \(x\circ_{n}\mathbb{I}_{\pi_{n}^{-}x} = x\) and \(\mathbb{I}_{\pi_n^+ x}\circ_nx = x.\)
(5) \((x\circ_{n}y)\circ_{n}z = x\circ_{n}(y\circ_{n}z)\) as soon as one of these is defined.
(6) If \( k < n \)

\[
(x \circ_ {n} y) \circ_ {k} (z \circ_ {n} w) = (x \circ_ {k} z) \circ_ {n} (y \circ_ {k} w)
\]

when the left-hand side is defined.

A \(n\)-cell \(a\) is non trivial if is not in the image of the application \(\mathbb{I}: X_{n-1} \to X_n\).

A morphism of  \( \omega \) -categories is a map of globular sets commuting with both operations. The category of  \( \omega \) -categories is denoted by  \( \omega \) -cat.

1.1.1.3. By abuse of notation, we also denote by  \( D_{n} \)  the  \( \omega \) -category that admits for any k < n only two k-non-trivial cells, denoted by  \( e_{k}^{-} \)  and  \( e_{k}^{+} \) , and a single n-non-trivial cell, denoted by  \( e_{n} \)  verifying :

\[
\pi_ {l} ^ {-} (e _ {k} ^ {\epsilon}) = e _ {l} ^ {-} \quad \pi_ {l} ^ {+} (e _ {k} ^ {\epsilon}) = e _ {l} ^ {+} \quad \text {for} l \leq k <   n
\]

\[
\pi_ {l} ^ {-} (e _ {n}) = e _ {l} ^ {-} \quad \pi_ {l} ^ {+} (e _ {n}) = e _ {l} ^ {+} \quad \mathrm{for} l \leq n
\]

Remark furthermore that the  \( \omega \) -category  \( D_{n} \)  represents n-cells, in the sense that  \( \operatorname{Hom}(\mathbf{D}_{n}, C) \cong C_{n} \) . We will not make the difference between n-cells and the corresponding morphism of  \( D_{n} \to C \) .

The \(\omega\)-category \(\partial \mathbf{D}_n\) is obtained from \(\mathbf{D}_n\) by removing the \(n\)-cell \(e_n\). We thus have a morphism

\[
i _ {n}: \partial \mathbf {D} _ {n} \to \mathbf {D} _ {n}.
\]

Note that \(\partial \mathbf{D}_0 = \emptyset\).

26