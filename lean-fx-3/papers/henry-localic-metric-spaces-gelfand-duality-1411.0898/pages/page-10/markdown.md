classifies the sequences $(x_n)$ such that for each $n$ one has $x_n R x_{n+1}$ is positive and locally positive.

This is proved in [15] as lemma $C$.

2.3.9. A geometric morphism $f : \mathcal{M} \to \mathcal{L}$ is said to be *fiberwise dense* (or to have a fiberwise dense image) if for any proposition $U$, one has the relation:

$$p^*(U) = f_* f^* p^*(U)$$

where $p$ denotes the canonical map $\mathcal{L} \to \{*\}$ and $U$ is identified with an open sublocale of $\{*\}$.

A sublocale $S \subset \mathcal{L}$ is said to be *fiberwise closed* if it is fiberwise dense in no other sublocale of $\mathcal{L}$.

2.3.10. In the presence of the law of excluded middle these are equivalent to the more classical notions of density and closeness, but in general fiberwise density only implies density, and closeness only implies fiberwise closeness. For this reason they have also been called “strongly dense” and “weakly closed”, but we prefer the terminology “fiberwise” which is more uniform, more specific and allows less confusions. This name “fiberwise” comes from the fact that, when interpreted internally in $\mathsf{Sh}(X)$ for a (nice enough) topological space $X$, it indeed corresponds to a notion of fiberwise density (and fiberwise closeness) of morphisms of locales over $X$ whereas the usual notion of density would correspond to simple density, without taking the basis into account.

Aside from this difference of terminology, these definitions and the proof of all the results stated here can be found in [12] after C1.1.22 and after C1.2.14.

Of course every sublocale $S$ admits a fiberwise closure $\overline{S}$ which is the smallest fiberwise closed sublocale containing $S$, or equivalently, the unique fiberwise closed sublocale in which $S$ is fiberwise dense.

2.3.11. In the case of locally positive locales, the fiberwise density takes the following simpler form.

**Proposition :** Let $f : X \to Y$ be a map with $X$ locally positive. Then the following conditions are equivalent:

(a) \(f\) is fiberwise dense.
(b) \(Y\) is locally positive, and for any positive open sublocale \(U\) of \(Y\), \(f^{*}(U)\) is positive.

In presence of the law of excluded middle, every locale is locally positive and a positive open sublocale is just a non-zero open sublocale. Hence the previous proposition asserts (in presence of the law of excluded middle) that $f$ is fiberwise dense if for every non zero open sublocale $f^*(U)$ is also non zero, which is a classical characterisation of a dense map.

10