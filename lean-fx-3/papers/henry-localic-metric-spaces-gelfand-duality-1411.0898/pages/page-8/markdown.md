2.3.4. The following lemma will often be useful to prove that some locales are locally positive:

**Lemma :** *Let $X$ be a locale, and $p$ the morphism from $X$ to the point $\{*\}$. Assume that there is a basis $(b_i)_{i \in I}$ of $X$ and a collection of propositions $(w_i)_{i \in I}$ such that:*

$$w_i \Rightarrow (b_i) > \emptyset$$

$$b_i \leqslant p^* w_i$$

*Then $X$ is positive, $w_i$ is equivalent to “$b_i > \emptyset$” and an arbitrary open sublocale of $X$ is positive if and only if it contains one of the $b_i$ such that $b_i > \emptyset$.*

**Proof :**

As the $b_i$ form a basis, any $U \in \mathcal{O}(X)$ can be written as:

$$U = \bigvee_{\substack{i \in I \\ b_i \leqslant U}} b_i$$

but as $b_i \leqslant p^*(w_i) = \bigvee_{w_i} \top$ one has:

$$U = \bigvee_{\substack{i \in I \\ b_i \leqslant U}} p^*(w_i) \wedge b_i = \bigvee_{\substack{i \in I \\ b_i \leqslant U \text{ and } w_i}} b_i$$

as $w_i$ implies that $b_i$ is positive, this is an expression of $U$ as a supremum of positive open sublocales, proving that $X$ is locally positive. Now $w_i \Rightarrow b_i > \emptyset$ and as $b_i = \bigvee_{w_i} b_i$ one also has $b_i > \emptyset \Rightarrow w_i$, which proves the equivalence between $w_i$ and “$b_i$ is positive”. Finally if $U$ is positive, then from the previous expression of $U$ as a union, there exists an $i$ such that $b_i \leqslant U$ and $w_i$ hence $b_i$ is positive, and conversely if $U$ contains a positive $b_i$ then $U$ is itself positive. $\square$

**2.3.5. Proposition :** *A locale $\mathcal{L}$ is locally positive if and only if it can be defined by a Grothendieck site where each covering is inhabited. In this situation, an open $U$ of $\mathcal{L}$ is positive if and only if it contains one of the representable.*

This is essentially the localic version of [12, C3.1.19]. It can be applied to site as defined in [12, C2.1.1], that is where the cover are only assumed to satisfies the base change axiom.

8