principle” in the sense that an equivalence of category $I \simeq J$ does not imply that $I^{(\alpha)} \simeq J^{(\alpha)}$.

A binary relation $R$ on a set $X$ is said to be well-founded if there is no infinite chain $x_1, \dots, x_n, \dots$ in $X$ such that $x_{n+1}Rx_n$ for all $n$. Equivalently, if the only subset $S \subset X$ satisfying $(\forall y, yRx \Rightarrow y \in S) \Rightarrow x \in S$ is $S = X$. A poset is said to be well-founded if the relation $<$ defined as $x \leqslant y$ and $x \neq y$ is well-founded. For example ordinals are well-founded as posets, and up to isomorphisms they are the unique well-founded totally ordered sets.

A functor $F : \mathcal{C} \to \mathcal{D}$ is said to be *identity-reflecting* if for every arrow $f$, $F(f)$ is an identity arrow implies that $f$ is an identity arrow. Note that this notion also breaks the equivalence principle: a functor equivalent to an identity-reflecting functor doesn't have to be identity-reflecting.

The posetal reflection of a category $I$, is the universal poset with a functor from $I$. One start with the relation on the set of objects of $I$ defined by $x \leqslant y :=$ “There exists an arrow $x \to y$” which is transitive and reflective and then one quotient the set of objects by the equivalence relation $x \leqslant y$ and $y \leqslant x$ to make into a poset.

### 3.2 Lemma. For a category $I$ the following conditions are equivalent:

1. (1) *The functor from $I$ to its posetal reflection is identity-reflecting.*
2. (2) *The category $I$ has no non-identity isomorphisms or endomorphisms.*

*Proof.* Any isomorphism or endomorphism is sent to an identity in the posetal reflection of $I$, so the implication $(1) \Rightarrow (2)$ is clear. We hence assume that $I$ has no non-identity endomorphisms or isomorphisms. Two objects $x, y$ of $I$ become identified in the posetal reflection of $I$ if and only if there are maps $f : x \to y$ and $g : y \to x$, but then the composite $f \circ g$ and $g \circ f$ are endomorphisms, hence identity, hence $f$ and $g$ are isomorphisms, and hence $x = y$. It follows that the map from $I$ to its posetal reflection is bijective on objects, and as $I$ has no non-identity endomorphisms this makes it identity-reflecting. $\square$

### 3.3 Proposition. For a category $I$, the following conditions are equivalents:

1. (SW1) *There are no identity-reflecting functors $\omega^{\circ p} \to I$.*
2. (SW2) *The relation $x < y$ on objects of $I$ defined by “there exists a non-identity arrow $x \to y$” is well-founded.*
3. (SW3) *The category $I$ has no non-identity isomorphisms or endomorphisms and its posetal reflection is a well-founded poset.*
4. (SW4) *There is an identity-reflecting functor $\mathcal{C} \to \mathbf{Ord}$.*
5. (SW5) *The canonical functor $I^{(\mathbf{Ord})} \to I$ admits a section (up to equality)*

*A category satisfying these conditions is said to be strictly well-founded.*

9