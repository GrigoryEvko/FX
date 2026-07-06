2.2.3. A *sublocale* of a locale $X$ is (an equivalence class of) a locale $Y$ endowed with a morphism $f: Y \rightarrow X$ such that $f^*$ is a surjective frame homomorphism (such a morphism is called an *inclusion*). A morphism of locale $f$ is said to be *surjective* if the corresponding frame homomorphism is injective. In particular, the injection/surjection factorisation of frame homomorphisms induces a unique (up to unique isomorphism) factorisation of every morphism of locale $f: X \rightarrow Y$ in a surjection followed by an inclusion:

$$X \rightarrow f_!(X) \hookrightarrow Y.$$

The sublocale $f_!(X)$ is called the image$^{3}$ of $f$. More generally if $S$ is any sublocale of $X$ we denote by $f_!(S)$ the image of the restriction of $f$ to $S$ and this is called the image of $S$ by $f$.

2.2.4. If $f: X \rightarrow Y$ is a morphism of locales and $S$ is a sublocale of $Y$ then the categorical pull-back $f^{-1}(S)$ is a sublocale of $X$ and one has an adjunction formula:

$$A \subset f^{-1}(B) \Leftrightarrow f_!(A) \subset B$$

for any sublocale $A$ of $X$ and $B$ of $Y$.

2.2.5. If $U$ is an element of the frame $\mathcal{O}(X)$ then it corresponds to a sublocale (also denoted $U$) of $X$ which is defined by the frame $\mathcal{O}(U) = \{v \in \mathcal{O}(X) | v \leq U\}$ and which is sent into $X$ by the morphism corresponding to $i^*(V) = V \wedge U$ for any $V \in \mathcal{O}(X)$. Hence, the elements of $\mathcal{O}(X)$ correspond to particular sublocales of $X$, which justifies the term “open sublocales” for elements of $\mathcal{O}(X)$. Also, through this identification, one has $f^*(U) = f^{-1}(U)$.

2.2.6. To any locale $X$ one can associate the topos of sheaves on $X$, denoted $\mathsf{Sh}(X)$. If $X$ and $Y$ are two locales, the category of geometric morphisms from $\mathsf{Sh}(X)$ to $\mathsf{Sh}(Y)$ is (equivalent to) the ordered set of locale morphisms from $X$ to $Y$ ordered by the pointwise ordering of the corresponding frame homomorphism (this is called the specialisation order). For this reasons locales will be seen as a specific kind of toposes.

2.2.7. An extremely important result of the theory of locales, that we will use constantly, is that there is an equivalence of category between $X$-locales, that is locales in the logic of $\mathsf{Sh}(X)$ and locales $Y$ endowed with a morphism to $X$. This allows one to turn any reasonable property of locales into a property of geometric morphisms, corresponding to the relative notion, for example one says that a map $Y \rightarrow X$ is proper if the $X$-locale corresponding to $Y$ is compact in the logic of $\mathsf{Sh}(X)$.

$^{3}$From a purely categorical point of view, we should call it the regular image of $X$.

5