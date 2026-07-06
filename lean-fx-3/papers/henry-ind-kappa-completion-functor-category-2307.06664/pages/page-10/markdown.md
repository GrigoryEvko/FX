Proof. The equivalence between (SW1) and (SW2) is immediate as the functors mentioned in (SW1) are exactly the downward chains for the relation mentioned in (SW2).

(SW2) $\Rightarrow$ (SW3): indeed, any isomorphisms or endomorphisms in $I$ would allow to obtain either a $x$ such that $x < x$ or $x, y$ such that $x < y$ and $y < x$ which is impossible in a well-founded relation, and if there are no isomorphisms or endomorphisms, then the posetal reflection is the set of objects with the relation of the point (SW2).

(SW3) $\Rightarrow$ (SW4) Every well-founded-poset admits a functor to **Ord** which is identity-reflecting (e.g. defined by well-founded induction as $v(x) = \sup_{y<x} v(y)^+$) so the implication follows by Lemma 3.2.

(SW4) $\Rightarrow$ (SW5). Given $F: I \to \mathbf{Ord}$ an identity-reflecting functor, then the functor $(Id, F): I \to I \times \mathbf{Ord}$ is a section of the first projection and takes values in $I^{(\mathbf{Ord})}$.

(SW5) $\Rightarrow$ (SW1): a section of $I^{(\mathbf{Ord})} \to I$ is automatically identity reflecting, so the existence of such section implies that there is an identity reflecting functor $I \to \mathbf{Ord}$ which clearly contradicts the existence of an identity reflecting functor $\omega^{\mathrm{op}} \to I$ as there is no such functor $\omega^{\mathrm{op}} \to \mathbf{Ord}$.

### 3.4 Proposition. For a category $I$, the following conditions are equivalents

(W1) I has no non-identity endomorphisms and it admits a conservative functor to Ord.
(W2) I has no non-identity endomorphisms and its posetal reflection is well-founded.
(W3) Every skeleton of \( I \) is a strictly well-founded category.
\((W_{4})\) I is equivalent to a strictly well-founded category.
(W5) The canonical functor \( I^{(\alpha)} \to I \) admits a section up to natural isomorphisms.
(W6) The identity functor on \( I \) is a retract of a functor that can be factored as a functor \( I \to I^{(\alpha)} \) followed by the canonical functor \( I^{(\alpha)} \to I \).

A category satisfying these equivalent conditions will be said to be Well-founded.

Condition (W6) may seem a little strange - the only reason it is here is because this characterization will be used in the next subsection to show the implication $(A2) \Rightarrow (A4)$ of Theorem 1.3.

Proof. (W1) $\Rightarrow$ (W2). Such a conservatif functor factors into a conservatif functor from the posetal reflection of $I$ to **Ord**, which implies that this posetal reflection has no infinite strictly decreasing chains, hence is well-founded.

(W2) $\Rightarrow$ (W3). This follows immediately from point (SW3) of Proposition 3.3: indeed in a skeleton all isomorphisms will be endomorphisms, and hence a skeleton of a category satisfying (W2), will have non-identity endomorphisms and isomorphisms and a well-founded posetal reflection, so satisfy condition (SW3) of Proposition 3.3.

10