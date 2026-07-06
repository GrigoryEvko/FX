and hence as the bottom map is a complemented inclusion by assumption, the top map is also a complemented inclusion. This shows that $S' \rightarrow S$ is a cofibration. $\square$

As discussed just before Lemma 1.8, the slice $\mathfrak{s}\mathcal{E} \downarrow X$ is enriched over simplicial sets and has cotensors by finite simplicial sets. Under the present hypotheses, it also has tensors by finite (and even countable) simplicial sets, which are simply tensors in the underlying category $\mathfrak{s}\mathcal{E}$.

Part (iii) of the next Proposition extends the pullback cotensor properties of part (i) of Lemma 1.5 to slice categories.

#### Proposition 5.8. Let $X \in \mathfrak{s}\mathcal{E}$.

- (i) *Pushout products of cofibrations in $\mathfrak{s}\mathcal{E} \downarrow X$ exist. Moreover, cofibrations in $\mathfrak{s}\mathcal{E} \downarrow X$ are closed under pushout product.*
- (ii) *The pushout tensor properties of Proposition 5.5 hold also in $\mathfrak{s}\mathcal{E} \downarrow X$.*
- (iii) *The pullback cotensor in $\mathfrak{s}\mathcal{E} \downarrow X$ of a cofibration between finite simplicial sets and a fibration is a fibration. If the given cofibration or fibration is trivial, then the result is a trivial fibration.*

*Proof.* For part (i), recall that pushout products in $\mathfrak{s}\mathcal{E} \downarrow X$ are computed from pushout products in $\mathfrak{s}\mathcal{E}$ by pulling back along the diagonal $X \rightarrow X \times X$. Since the latter is a monomorphism, the conclusion follows from Proposition 5.3 and Lemma 5.7. For part (ii), note that the forgetful functor $\mathfrak{s}\mathcal{E} \downarrow X \rightarrow \mathfrak{s}\mathcal{E}$ preserves tensors and pushouts and thus the pushout tensor properties follow directly from Proposition 5.5. Part (iii) was already established as Lemma 1.8, but now it also follows by the tensor-cotensor adjunction. $\square$

#### Proposition 5.9.

- (i) *Let $f: X \rightarrow Y$ be a morphism in $\mathfrak{s}\mathcal{E}$. If $X$ is cofibrant, then the pullback functor $f^*: \mathfrak{s}\mathcal{E} \downarrow Y \rightarrow \mathfrak{s}\mathcal{E} \downarrow X$ preserves cofibrations.*
- (ii) *Let $A \rightarrow X$ and $B \rightarrow X$ be morphisms in $\mathfrak{s}\mathcal{E}$. If $A$ and $B$ are cofibrant, then so is $A \times_X B$.*
- (iii) *Cofibrant objects in $\mathfrak{s}\mathcal{E}$ are closed under finite limits.*

*Proof.* For (i), if $A \rightarrow B$ is a cofibration over $Y$, then its pullback along $f: X \rightarrow Y$ coincides with the pushout product of $A \rightarrow B$ and $\varnothing \rightarrow X$ in $\mathfrak{s}\mathcal{E} \downarrow Y$, which is a cofibration by part (i) of Proposition 5.3. Part (ii) is a special case of part (i). Finally, for part (iii), it suffices to check that cofibrant objects are closed under pullback and that the terminal object is cofibrant. The former follows from part (ii). The latter follows by definition since $0 \rightarrow 1$ is a generating cofibration. $\square$

## 6 Pushforward along cofibrations

This section and Sections 7, 8 and 9 constitute the third part of the paper, in which we show how the two weak factorisation systems of Section 4 give rise to the effective model structure (Theorem 9.9). For this, we shall work with a fixed countably lextensive category $\mathcal{E}$. We do not assume that the category $\mathcal{E}$ is (locally) Cartesian closed, but we establish the existence of certain exponentials and pushforwards required by our argument. We also provide a criterion for the cofibrancy of some of these constructions. We begin with a few remarks on exponentiable maps.

#### Proposition 6.1. Let $f: X \rightarrow Y$ in $\mathcal{E}$. Then, the following are equivalent:

32