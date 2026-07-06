6.1. UNIVALENCE

Applying lemma 6.1.4.7, and the fact that any morphism \(\{l\} \to [a,m] \to (I \otimes [n]^{\sharp})^{\sharp}\) uniquely factors through \(\coprod_k I^\sharp \otimes \{k\}\), we get a cartesian square

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ^ {c} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \lim _ {[ a, m ] \to (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \end{array}
\]

Eventually, the lemma 6.1.4.9 induces equivalences

\[
\begin{array}{l} \lim _ {[ a, m ] \rightarrow (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \sim \tau_ {0} \mathrm{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp} \times b ^ {\flat}) \\ \lim _ {[ a, m ] \to I ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \sim \tau_ {0} \mathrm{LCart} (I ^ {\sharp} \times b ^ {\flat}) \\ \lim _ {[ a, m ] \to I ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp}) \sim \tau_ {0} \mathrm{LCart} (I ^ {\sharp}) \\ \end{array}
\]

This concludes the proof.

Lemma 6.1.4.11. There is a family of cartesian squares

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \tau_ {0} \operatorname{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp} \times b ^ {\flat}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} (I ^ {\sharp} \otimes \{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} ((I ^ {\sharp} \otimes \{k \}) \times b ^ {\flat}) \end{array}
\]

natural in \(I, b\) and \(n\).

Proof. By the construction of \(\mathrm{LCart}^c (I;b)\), we have a cartesian square

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \operatorname{Hom} ([ n ], \operatorname{LCart} (I \times b ^ {\flat})) \\ \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} ^ {c} (I) \longrightarrow \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} (I \times b ^ {\flat}) \end{array}
\]

According to lemma 6.1.4.6, this induces a cartesian square

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \operatorname{Hom} ([ n ], \operatorname{LCart} (I) _ {/ \pi_ {b}}) \\ \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} ^ {c} (I) \longrightarrow \prod_ {k \leq n} \tau_ {0} (\operatorname{LCart} (I) _ {/ \pi_ {b}}) \end{array}
\]

As the functor \(\mathrm{LCart}^c (I)\to \mathrm{LCart}(I)_{/\pi_b}\) factors through \(\mathrm{LCart}^c (I)_{/\pi_b}\), the proposition 6.1.3.29 induces a cartesian square

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \tau_ {0} (\operatorname{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp}) _ {/ \pi_ {b}}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} (I ^ {\sharp} \otimes \{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} (\operatorname{LCart} (I ^ {\sharp} \otimes \{k \}) _ {/ \pi_ {b}}) \end{array}
\]

Eventually, a last application of lemma 6.1.4.6 concludes the proof.

335