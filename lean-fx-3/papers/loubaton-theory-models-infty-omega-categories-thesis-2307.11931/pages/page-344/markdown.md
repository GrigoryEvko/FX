CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Lemma 6.1.4.9. Let \( b \) be a globular sum and let \( F: I \to (\infty, \omega) \)-cat be a \( \mathbf{W} \)-small diagram. The canonical morphism

\[
\operatorname{LCart} (\underset {I} {\operatorname{colim}} F ^ {\sharp} \times b ^ {\flat}) \to \underset {I} {\lim} \operatorname{LCart} (F ^ {\sharp} \times b ^ {\flat})
\]

is an equivalence.

Proof. The corollary 6.1.2.16 implies that the canonical morphism

\[
\operatorname{LCart} (\underset {I} {\operatorname{colim}} F ^ {\sharp}) \to \underset {I} {\lim} \operatorname{LCart} (F ^ {\sharp})
\]

is an equivalence. We recall that for any  \( (\infty,\omega) \) -category A, we denote by  \( \pi_{b}:A^{\sharp}\times b^{\flat}\to A^{\sharp} \)  the canonical projection. As the  \( (\infty,1) \) -categorical slice preserves limits, the previous equivalence induces an equivalence

\[
\operatorname{LCart} (\underset {I} {\operatorname{colim}} F ^ {\sharp}) _ {/ \pi_ {b}} \to \underset {I} {\lim} \operatorname{LCart} (F ^ {\sharp}) _ {/ \pi_ {b}}.
\]

The results then follows from lemma 6.1.4.6.

Lemma 6.1.4.10. There is a family of cartesian squares

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \longrightarrow \tau_ {0} \mathrm{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp} \times b ^ {\flat}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \mathrm{LCart} (I ^ {\sharp} \otimes \{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} \mathrm{LCart} ((I ^ {\sharp} \otimes \{k \}) \times b ^ {\flat}) \end{array}
\]

natural in I, b and n.

Proof. By definition,  \( (I \ominus [b, n]^{\sharp})^{\sharp} \)  fits in the following cartesian square:

\[
\begin{array}{c} \operatorname{colim} _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} [ a \times b, m ] ^ {\sharp} \longrightarrow \operatorname{colim} _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} [ a, m ] ^ {\sharp} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{colim} _ {[ a, m ] \to (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} [ a \times b, m ] ^ {\sharp} \longrightarrow (I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp} \end{array}
\]

Combined with corollary 6.1.2.16, this implies that the \(\infty\)-groupoid \(\tau_0\mathrm{LCart}((I\ominus [b,n]^{\sharp})^{\sharp})\) fits in the cartesian square:

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ^ {c} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \lim _ {[ a, m ] \to (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a \times b, m ] ^ {\sharp}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a \times b, m ] ^ {\sharp}) \end{array}
\]

334