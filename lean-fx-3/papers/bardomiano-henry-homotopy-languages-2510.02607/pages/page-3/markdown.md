For example, because the notion of limit in a category is naturally formulated without using equality between objects we automatically know that equivalences of categories preserve limits, or that if two diagrams are naturally isomorphic then a limit for one is also a limit for the other.

To be a little more precise, the above-mentioned results are about first-order formulas in which we can have quantifiers over all objects of the category, or over all morphisms in a given hom-set “hom($X, Y$)”. We can use equality between two terms taken from the same hom($X, Y$), but not between two terms of type “objects”, or two terms that are in different hom-sets.

For example, the property of an object $X$ to be a terminal object, which can be written as

$$\text{isTerminal}(X) := \forall Y \in \text{Ob}, (\exists v \in \text{Hom}(Y, X) \text{ and } \forall u, w \in \text{Hom}(Y, X), u = w)$$

is an instance of such a formula, but the following formula

$$\begin{aligned} \forall X, Y \in \text{Ob}, \forall f \in \text{Hom}(X, Y), \forall g \in \text{Hom}(Y, X), \\ (f \circ g = \text{id}_Y \text{ and } g \circ f = \text{id}_X \Rightarrow X = Y) \end{aligned}$$

which states that the category we are working with is skeletal, or the formula

$$\begin{aligned} \forall X, Y \in \text{Ob}, \forall f \in \text{Hom}(X, Y), \forall g \in \text{Hom}(Y, X), \\ (f \circ g = \text{id}_Y \text{ and } g \circ f = \text{id}_X \Rightarrow f = \text{id}_X) \end{aligned}$$

which expresses that identities are the only isomorphisms, are not of this form: the first one involves the equality $X = Y$, and the second one involves an equality $f = \text{id}_X$ that is not correctly typed as $f \in \text{Hom}(X, Y)$. And these two formulas are indeed not invariant under equivalence of categories$^1$.

Note that in order for this to make sense, it is key to use a notion of “dependent types”. Indeed, we need to be able to formulate the idea that a morphism $f$ is in $\text{Hom}(X, Y)$, without being able to say that $s(f) = X$ and $t(f) = Y$ as this would involve using equality between objects. So, given two objects $X$ and $Y$, we need to be able to consider the type of arrows from $X$ to $Y$ as a primitive notion.

Now, it is natural to expect that similar results can be generalized to higher categories. For example, we expect (and it can be shown) that a

$^1$As they are formulas with no free parameters, invariance under substitution by isomorphic objects does not really make sense.

3