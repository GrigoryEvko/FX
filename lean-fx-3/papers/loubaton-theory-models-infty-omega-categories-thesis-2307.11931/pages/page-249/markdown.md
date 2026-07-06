5.1. MARKED \((\infty, \omega)\)-CATEGORIES

5.1.1.20. In section 4.2.1, we define the notion of fully faithful morphism of \((\infty, \omega)\)-categories. There is an equivalent notion for marked \((\infty, \omega)\)-categories:

Definition 5.1.1.21. A morphism \( f: C \to D \) is fully faithful if for any pair of objects \( x, y \), the morphism of marked \( (\infty, \omega) \)-categories \( \hom_C(x, y) \to \hom_D(fx, fy) \) is an equivalence, and if a 1-cell \( v \) is marked whenever \( f(v) \) is.

We now give some adaptation of the result on fully faithful functors to the case of marked  \( (\infty,\omega) \) -categories without proofs, as they are obvious modifications to this new framework.

Proposition 5.1.1.22. A morphism is fully faithful if and only if it has the unique right lifting property against \(\emptyset \to \mathbf{D}_n\) and \(\mathbf{D}_n \to (\mathbf{D}_n)_t\) for \(n > 0\).

Proposition 5.1.1.23. Fully faithful morphisms are stable under limits.

Proposition 5.1.1.24. A morphism \( f: C \to D \) is an equivalence if and only if it is fully faithful and surjective on objects.

5.1.1.25. A morphism \( f: C \to D \) between marked \( (\infty, \omega) \)-categories is a discrete Conduché functor if for any triplet of integers \( k < n \leq m \), \( f \) has the unique right lifting property against

\[
\mathbb {I} _ {m + 1}: \mathbf {D} _ {m + 1} ^ {\flat} \to \mathbf {D} _ {m} ^ {\flat} \quad \text {and} \quad \nabla_ {k, m} ^ {\sharp_ {n}}: \mathbf {D} _ {m} ^ {\sharp_ {n}} \to \mathbf {D} _ {m} ^ {\sharp_ {n}} \coprod_ {\mathbf {D} _ {k} ^ {\flat}} \mathbf {D} _ {m} ^ {\sharp_ {n}}.
\]

Example 5.1.1.26. If \( f \) is a discrete Conduché functor between marked \( (\infty, \omega) \)-categories, \( f^{\sharp} \) is a discrete Conduché functor. Conversely, if \( g \) is a discrete Conduché functor between \( (\infty, \omega) \)-categories, so are \( g^{\sharp} \), \( g^{\flat} \) and \( g^{\sharp n} \) for any integer \( n \).

5.1.1.27. A marked globular sum is a marked  \( (\infty,\omega) \) -category whose underlying  \( (\infty,\omega) \) -category is a globular sum and such that for any pair of integers  \( k \leq n \) , and any pair of k-composable n-cells  \( (x,y) \) ,  \( x \circ_{k} y \)  is marked if and only if x and y are marked.

A morphism \( i: a \to b \) between marked globular sum is globular if the morphism \( i^{\sharp} \) is globular.

The proposition 1.1.2.11 implies that a morphism \(a \to b\) between marked globular sums is a discrete Conduché functor if and only if it is globular.

Lemma 5.1.1.28. Let \( p: C \to D^b \) be a discrete Conduché functor between marked \( (\infty, \omega) \)-categories. The canonical morphism \( (C^\sharp)^b \to C \) is an equivalence.

239