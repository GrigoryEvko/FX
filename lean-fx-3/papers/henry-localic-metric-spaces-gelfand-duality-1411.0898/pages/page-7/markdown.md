- A locale $\mathcal{L}$ is said to be positive, if whenever we can write $\mathcal{L}$ as a union of open sublocales:

$$\mathcal{L} = \bigvee_{i \in I} u_i$$

the set of indices $I$ has to be inhabited. In this case, we write $\mathcal{L} > \emptyset$.

- A locale $\mathcal{L}$ is said to be locally positive if every open sublocale can be written as a union of positive open sublocales.

If one assumes the law of excluded middle, then an open sublocale is positive if and and only if it is non-zero and every locale is locally positive (any non-zero element is the union of just itself, and the zero element is the empty union). But without the law of excluded middle this becomes a non trivial property.

2.3.2. If $X$ is a locale (preferably locally positive) we will denote by $\mathcal{O}(X)^+$ the subset of positive open sublocales of $X$.

2.3.3. Local positivity is closely related to the notion of open map:

Proposition : Let $f : \mathcal{L} \to \mathcal{M}$ be a morphism of locale, then the following conditions are equivalent:

- For any \(U\) open sublocale of \(\mathcal{L}\), its image \(f_{1}(U)\) is an open sublocale of \(\mathcal{M}\); i.e. \(f\) is an open map.
- The frame morphism \( f^{*} : \mathcal{O}(\mathcal{M}) \to \mathcal{O}(\mathcal{L}) \) has a left adjoint \( f_{\circ} \) (i.e. \( f_{\circ}(U) \leqslant V \) if and only if \( U \leqslant f^{*}(V) \)) which satisfies the additional identity:

$$f_{\circ}(U \wedge f^{*}(V)) = (f_{\circ}U) \wedge V;$$

- $\mathcal{L}$ is locally positive as a $\mathcal{M}$-locale.

Moreover in this situation, $f_{\circ}$ is the same as $f_1$ (restricted to open sublocales) and it corresponds to the internal map which associates to every $U \in \mathcal{O}(\mathcal{L})$ the $\mathcal{M}$-proposition " $U$ is positive ".

For a proof, see [2]1.6.1 and 1.6.2 for the equivalence of the first two points, and see [12] C3.1.17 for the last point.

Because of this proposition, locally positive locales are generally called "open locales". We cannot use this terminology here because we will have to speak a lot about locally positive sublocales, and "open sublocales" would have two possible meaning in this case. The name "overt" has also been proposed to avoid this confusion.

7