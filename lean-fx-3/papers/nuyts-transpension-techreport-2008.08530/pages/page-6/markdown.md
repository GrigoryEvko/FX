Proof. To see the implication from left to right: It is a standard fact of adjoint functors [nLa21a] that the left adjoint $F_!$ is fully faithful if and only if $\eta : \Gamma \to F^*F_!\Gamma$ is a natural isomorphism. If $F$ is fully faithful, then we can apply the co-Yoneda lemma:

$$(V \Rightarrow F^*F_!\Gamma) = (\exists V'.(FV \to FV') \times (V' \Rightarrow \Gamma)) \cong (\exists V'.(V \to V') \times (V' \Rightarrow \Gamma)) \cong (V \Rightarrow \Gamma)$$

i.e. $F^*F_!\Gamma \cong \Gamma$ and it is straightforward to see that this isomorphism is indeed the co-unit.

The implication from right to left is straightforward. By full faithfulness of $\mathbf{y}$ and by theorem 2.3.2 we have

$$(\mathbf{y}U \to \mathbf{y}V) \cong (U \to V),$$

$$(F_!\mathbf{y}U \to F_!\mathbf{y}V) \cong (\mathbf{y}FU \to \mathbf{y}FV) \cong (FU \to FV).$$

### 2.3.4 Dependent presheaf categories

Let $\mathcal{W}$ be a category. Then $\widehat{\mathcal{W}}$ is a category with families (CwF). The following notion is standard:

**Definition 2.3.5.** For any $\Gamma \in \widehat{\mathcal{W}}$, the **category of elements** of $\Gamma$, denoted

$$\int_{\mathcal{W}} \Gamma \quad \text{or} \quad \mathcal{W}/\Gamma \tag{5}$$

has objects $(W, \gamma)$ where $W \in \mathcal{W}$ and $\gamma : W \Rightarrow \Gamma$, and the morphisms $(W, \gamma) \to (W', \gamma')$ are the morphisms $\chi : W \to W'$ such that $\gamma' \circ \chi = \gamma$.

Clearly, we have an isomorphism $\mathcal{W}/U \cong \mathcal{W}/\mathbf{y}U$ between the slice category over $U$ and the category of elements of $\mathbf{y}U$.$^4$

We will use type-theoretic notation to make statements about the CwF $\widehat{\mathcal{W}}$, e.g. $\Gamma \vdash \text{Ctx}$ means $\Gamma \in \widehat{\mathcal{W}}$ and $\Gamma \vdash T$ type means $T \in \text{Ty}(\Gamma)$. Now for any context or closed type $\Gamma \in \widehat{\mathcal{W}}$, there is another CwF $\widehat{\mathcal{W}/\Gamma}$. Statements about this category will also be denoted using type-theoretic notation, but prefixed with '$\Gamma$ |'.

By unfolding the definitions of types and terms in a presheaf CwF, it is trivial to show that there is a correspondence — which we will treat as though it were the identity — between both CwFs:

- Contexts \(\Gamma \mid \Theta \vdash \mathrm{Ctx}\) correspond to types \(\Gamma \vdash \Theta\) type which we will think of as telescopes \(\Gamma.\Theta \vdash \mathrm{Ctx}\),
- Substitutions \(\Gamma \mid \sigma : \Theta \to \Theta'\) correspond to functions \(\Gamma \vdash \sigma : \Theta \to \Theta'\), or equivalently to telescope substitutions \(\mathrm{id}_{\Gamma}.\sigma : \Gamma.\Theta \to \Gamma.\Theta'\),
- Types \(\Gamma \mid \Theta \vdash T\) type correspond to types \(\Gamma.\Theta \vdash T\) type,
- Terms \(\Gamma \mid \Theta \vdash t : T\) correspond to terms \(\Gamma.\Theta \vdash t : T\).

In summary, the pipe is equivalent to a dot.

**Proposition 2.3.6.** We have an equivalence of categories $\widehat{\mathcal{W}/\Gamma} \simeq \widehat{\mathcal{W}}/\Gamma$.

Proof. $\to$ We map the presheaf $\Gamma \mid \Theta \vdash \text{Ctx}$ to the slice object $(\Gamma.\Theta, \pi)$.

$\leftarrow$ We map the slice object $(\Delta, \sigma)$ to the preimage of $\sigma$, i.e. the presheaf $\sigma^{-1}$ which sends $(W, \gamma)$ to $\{\delta : W \Rightarrow \Delta \mid \sigma \circ \delta = \gamma\}$.

$\widehat{\mathcal{W}/\Gamma}$ We need a natural isomorphism $\eta : \forall \Theta.(\Gamma \mid \eta : \Theta \cong \pi^{-1})$. If $\theta : (W, \gamma) \Rightarrow \Theta$, then we define $\eta(\theta) = (\gamma, \theta) : W \Rightarrow \Gamma.\Theta$ and indeed we have $\pi \circ (\gamma, \theta) = \gamma$. This is clearly invertible.

$^4$Depending on pedantic details, we may even have $\mathcal{W}/U = \mathcal{W}/\mathbf{y}U$.

6