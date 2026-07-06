**Definition 2.1.2.** The *category* $\mathbf{Adj}_s$ *of adjunctions with strong morphisms* is defined as follows:

(i) An object consists of categories $\mathcal{C}$ and $\mathcal{D}$ with functors $F: \mathcal{C} \rightarrow \mathcal{D}$ and $G: \mathcal{D} \rightarrow \mathcal{C}$ and natural transformations $\eta: \mathrm{Id} \rightarrow GF$ and $\epsilon: FG \rightarrow \mathrm{Id}$ such that $\epsilon F \circ F\eta = \mathrm{id}$ and $G\epsilon \circ \eta G = \mathrm{id}$.

(ii) A morphism $(U, V, \alpha, \beta): (\mathcal{C}_1, \mathcal{D}_1, F_1, G_1, \eta_1, \epsilon_1) \rightarrow (\mathcal{C}_2, \mathcal{D}_2, F_2, G_2, \eta_2, \epsilon_2)$ consists of functors $U: \mathcal{C}_1 \rightarrow \mathcal{C}_2$ and $V: \mathcal{D}_1 \rightarrow \mathcal{D}_2$ with isomorphisms $\alpha: F_2U \cong VF_1$ and $\beta: UG_1 \cong G_2V$ satisfying $\beta F_1 \circ U\eta = G_2\alpha \circ \eta'U$ and $V\epsilon \circ \alpha G_1 = \epsilon'V \circ F_2\beta$:

Note that the two equations in 2.1.2(ii) are interderivable. There are functors from $\mathbf{Adj}_s$ to $\mathbf{Fun}_s$ selecting the left and right adjoint, respectively. Observe that while there are lax versions of $\mathbf{Fun}_s$ and $\mathbf{Adj}_s$ for which these functors are fully faithful, this is not the case here. Requiring natural isomorphisms instead of just natural transformations is how we encode preservation of free algebras in Theorems 2.2.14 and 2.3.26.

**Definition 2.1.3.** The *category* $\mathbf{PtdEndo}_s$ *of pointed endofunctors with strong morphisms* is defined as follows:

(i) An object $(\mathcal{E}, \mathsf{T})$ is a pointed endofunctor $\mathsf{T}$ on a category $\mathcal{E}$.

(ii) A morphism $(F, \gamma): (\mathcal{E}_1, (T_1, \tau_1)) \rightarrow (\mathcal{E}_2, (T_2, \tau_2))$ is a functor $F: \mathcal{E}_1 \rightarrow \mathcal{E}_2$ and isomorphism $\gamma: FT_1 \cong T_2F$ such that $\gamma \circ F\tau_1 = \tau_2F$.

**Definition 2.1.4.** The *category* $\mathbf{Mnd}_s$ *of monads with strong morphisms* is defined as follows:

(i) An object $(\mathcal{E}, \mathsf{M})$ is a monad $\mathsf{M}$ on a category $\mathcal{E}$.

(ii) A morphism $(F, \gamma): (\mathcal{E}_1, (M_1, \eta_1, \mu_1))$ to $(\mathcal{E}_2, (M_2, \eta_2, \mu_2))$ is a strong morphism of pointed endofunctors $(F, \gamma): (\mathcal{E}_1, (M_1, \eta_1)) \rightarrow (\mathcal{E}_2, (M_2, \eta_2))$ such that $\gamma \circ F\mu_1 = \mu_2F \circ M_2\gamma \circ \gamma M_1$.

**Terminology 2.1.5.** A *strict* morphism of pointed endofunctors is a strong morphism for which the isomorphism $\gamma: FT \cong T'F$ is an identity; likewise for strict morphisms of monads.

There is a functor from $\mathbf{Mnd}_s$ to $\mathbf{Fun}_s$ forgetting the monad structure and the endofunctor aspect, and there is a functor from $\mathbf{Adj}_s$ to $\mathbf{Mnd}_s$ sending an adjunction to its associated monad. Like $\mathbf{Adj}_s$, $\mathbf{Mnd}_s$ is a wide subcategory of its more common lax version.

**Remark 2.1.6.** The above categories and the below categories of configurations are in fact strict 2-categories and the functors relating them are strict 2-functors, but we shall not need this here.

## 2.2 Well-pointed endofunctors

**Definition 2.2.1.** A pointed endofunctor $\mathsf{S} = (S, \sigma)$ is *well-pointed* when $S\sigma = \sigma S$.

We use transfinite iteration to build the free monad on a well-pointed endofunctor. We aim to do so constructively (see Appendix A), so this requires some care. For concreteness, we use Powell's set-theoretic definition of ordinals [Pow75]—an ordinal is a transitive set whose elements are transitive sets—but the constructive reader should be able to substitute the definition appropriate for their favorite metatheory.

10