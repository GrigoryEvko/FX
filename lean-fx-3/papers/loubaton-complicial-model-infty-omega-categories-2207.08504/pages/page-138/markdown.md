CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Corollary 3.3.1.12. Let \( n \in \mathbb{N} \). The adjunction between \( \mathrm{Psh}(\Theta_n \times \Delta) \) and \( \mathrm{tPsh}(\Delta)^n \) constructed in [OR22] is a Quillen equivalence.

Proof. A direct induction using [OR22, theorem 3.22] implies that the left adjoint preserves globes. The results then follow from the fact that these two categories are models of \((\infty, n)\)-categories and from proposition 3.1.3.4.

#### 3.3.2 The case \(n = \omega\)

Construction 3.3.2.1. We define by induction the functor

\[
q: \Theta \to \mathrm{tPsh} (\Delta)
\]

by the formula

\[
q ([ 0 ]) := [ 0 ], \quad q ([ \mathbf {a}, n ]) := \underset {[ b, m ] \to [ \mathbf {a}, n ]} {\operatorname{colim}} q (b) \otimes [ n ].
\]

This induces an adjunction:

\[
i: \mathrm{Psh} (\Theta \times \Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta): N _ {i}
\]

where the left adjoint is the left Kan extension of the functor  \( (a,n)\mapsto q(a)\times[n]^{\sharp} \) .

We denote  \( i_{\omega} := i \) ,  \( N_{i_{\omega}} := N_{i} \) , and for an integer n,

\[
i _ {n}: \mathrm{Psh} (\Theta_ {n} \times \Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta): N _ {i _ {n}}
\]

the restriction of this adjunction.

Proposition 3.3.2.2. For any \(n \in \mathbb{N} \cup \{\omega\}\), the adjunction constructed in 3.3.2.1

\[
i _ {n}: \mathrm{Psh} (\Theta_ {n} \times \Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta) ^ {n}: N _ {i _ {n}}
\]

is a Quillen pair, where \(\mathrm{Psh}(\Theta_n\times \Delta)\) is endowed with the model structure described in construction 3.1.3.2.

Proof. We first prove by induction on \( n \) that the restricted functor \( (q_n)_! : \mathrm{Psh}(\Theta_n) \to \mathrm{tPsh}(\Delta)^n \) sends \( W_n \) onto weak equivalences. The initialization is trivial. The case \( n = 1 \) is a consequence of proposition 2.2.1.10 applied to the identity functor \( id : \mathrm{tPsh}(\Delta)_1 \to \mathrm{tPsh}(\Delta)_1 \).

Suppose the result true at the stage  \( n \geq 1 \) . We recall that the Gray tensor product on stratified simplicial sets is a Quillen bifunctor. The induction hypothesis and the proposition 2.1.1.8 then imply that the functor

\[
(q _ {n + 1} ^ {\prime}) _ {!}: \mathrm{Psh} (\Delta [ \Theta_ {n} ]) \to \mathrm{tPsh} (\Delta) ^ {n + 1}
\]

defined by \( q_{n+1}'[a, n] := a \otimes [n] \), sends \( \overline{\mathbf{W}_n} \otimes \overline{\mathbf{W}_1} \) to weak equivalences. As \( M_{n+1} \) is included in this set of morphisms, it is send by \( q_{n+1}' \) to weak equivalences. As \( q_{n+1}' \) preserves monomorphisms and colimits, the proposition 2.1.1.8 implies that this functor sends \( \overline{M_{n+1}} \) to weak equivalences. Now remark that \( (q_{n+1})_! \) is the composite

\[
\mathrm{Psh} (\Theta_ {n + 1}) \xrightarrow {i ^ {*}} \mathrm{Psh} (\Delta [ \Theta_ {n} ]) \xrightarrow {(q _ {n + 1} ^ {\prime}) !} \mathrm{tPsh} (\Delta) ^ {n + 1}
\]

and the proposition 1.1.3.17 then implies that \((q_{n + 1})_!\) sends \(\mathrm{W}_{n + 1}\) to weak equivalences.

As \( \mathrm{W} := \cup_{n} \mathrm{W}_{n} \), the functor \( q_{!} : \mathrm{Psh}(\Theta) \to \mathrm{tPsh}(\Delta)^{\omega} \) sends \( \mathrm{W} \) to weak equivalences. By definition of the model structure on \( \mathrm{Psh}(\Theta_{n} \times \Delta) \), this concludes the proof.

138