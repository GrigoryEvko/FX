CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.1.3.7. In the following lemmas and proposition, we focus on the case where I is of the form  \( A^{\sharp} \) , where everything happens more simply.

Lemma 6.1.3.8. Let \( j: A \to B \) be a morphism between \( (\infty, \omega) \)-categories and \( i: [n] \to [m] \) a morphism of \( \Delta \). Let \( E \) be an object of \( \operatorname{Fun}([n], \operatorname{LCart}(A^{\sharp})) \). The canonical morphism

\[
\mathbf {L} \oint_ {n, A ^ {\sharp}} (\mathbf {R} j ^ {*} \circ E \circ i) \rightarrow \mathbf {R} (j \times i ^ {\sharp}) ^ {*} \mathbf {L} \oint_ {m, B ^ {\sharp}} E
\]

is an equivalence.

Proof. As equivalences in  \( \operatorname{Fun}([m],\operatorname{LCart}(B^{\sharp})) \)  are detected on points, an equivalences on  \( \operatorname{LCart}(B^{\sharp}\times[m]^{\sharp}) \)  are detected on fibers, we can suppose that n=0, A=1, and we denote by k the image of i and a the image of B. As  \( L\oint_{0,1} \)  is the identity, one has to show that the canonical morphism

\[
\mathbf {R} a ^ {*} E _ {k} \rightarrow \mathbf {R} (a \times \{k \}) ^ {*} \mathbf {L} \oint_ {m, B ^ {\sharp}} E \tag {6.1.3.9}
\]

is an equivalence.

Moreover, for any \( l \leq n \), the proposition 5.2.1.7 implies that the canonical morphism \( \mathbf{F}(E_l \otimes \mathbf{F}h_l^{[n]}) \to E_l \times \mathbf{F}h_l^{[n]} \) is an equivalence, as this two left cartesian fibrations are replacement of \( E_l \otimes h_l^{[n]} \sim E_l \times h_l^{[n]} \). According to proposition 5.2.4.13, \( \mathbf{R}(a \times \{k\}^\sharp)^* \) preserves colimits, we then have

\[
\mathbf {R} (a \times \{k \}) ^ {*} \mathbf {L} \oint_ {m, B ^ {\sharp}} E \sim \underset {m} {\mathrm{colim}} \prod_ {i _ {0} \leq \ldots \leq i _ {m} \leq k} \mathbf {R} a ^ {*} E _ {i _ {0}} \sim \underset {i: [ k ]} {\mathrm{colim}} \mathbf {R} a ^ {*} E _ {i} \sim \mathbf {R} a ^ {*} E _ {k}.
\]

The morphism (6.1.3.9) is then an equivalence, which concludes the proof.

Proposition 6.1.3.10. The functor \(\mathbf{R}\mathring{\partial}_{n,I}\) is natural in \(n:\Delta^{op}\) and \(I:(\infty ,\omega)\text{-cat}_{\mathrm{m}}^{op}\). The functor \(\oint_{n,A^{\sharp}}\) is natural in \(n:\Delta^{op}\) and \(A:(\infty ,\omega)\text{-cat}^{op}\).

Proof. The proof is similar to the one of proposition 6.1.2.14, using lemma 6.1.3.6 and lemma 6.1.3.8 instead of lemma 6.1.2.9 and lemma 6.1.2.13. \(\square\)

Proposition 6.1.3.11. For any \((\infty, \omega)\)-category \(A\) and any integer \(n\), the adjunction

\[
\mathbf {L} \oint_ {n, A ^ {\sharp}}: \mathrm{Fun} ([ n ], \mathrm{LCart} (A ^ {\sharp})) \xrightarrow [ \longleftarrow ]{\perp} \mathrm{LCart} ((A \times [ n ]) ^ {\sharp}): \mathbf {R} \mathring {\partial} _ {n, A ^ {\sharp}}
\]

is an adjoint equivalence.

Proof. As in both case equivalences are detected on fibers, and as these functors are natural in A and n, one can show the result for A being the terminal  \( (\infty,\omega) \) -category and n=0. In this case remark that these two functors are the identities. □

322