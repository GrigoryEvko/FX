4. For each $x \in I$, we have:

$$\gamma' : \Gamma^{2 \times I} \vdash_{\text{sm}} \Theta^{\partial \mathcal{K}_{(0,x)}} \gamma' \equiv \Theta^{\partial \mathcal{K}_x} \gamma'^{\text{ev}}$$

$$\gamma' : \Gamma^{2 \times I}, y : \Theta^{\partial \mathcal{K}_{(0,x)}} \gamma' \vdash_{\text{sm}} B^{(0,x)} \gamma' y \equiv B^x \gamma'^{\text{ev}} y$$

$$\partial \mathcal{K}_{(1,x)} = p^* \partial \mathcal{K}_x \cup \{(\xi, 1_x)\}$$

$$\gamma' : \Gamma^{2 \times I} \vdash_{\text{sm}} \Theta^{\partial \mathcal{K}_{(1,x)}} \gamma' \equiv \left( y' : (\Theta^{\partial \mathcal{K}_x})^D \gamma', a_{(0,x)} : B^x \gamma'^{\text{ev}} y'^{\text{ev}} \right)$$

$$\gamma' : \Gamma^{2 \times I}, y' : \Theta^{\partial \mathcal{K}_{(1,x)}} \gamma' \vdash_{\text{sm}} B^{(1,x)} \gamma' y' \equiv (B^x)^d \gamma' y'$$

5. For each $h \in H(x)$, we have:

$$\gamma' : \Gamma^{2 \times I}, y' : \Theta^{p^*H} \vdash_{\text{sm}} b^{(0,h)} \gamma' y' \equiv b^h \gamma'^{\text{ev}} y'^{\text{ev}}$$

$$\gamma' : \Gamma^{2 \times I}, y' : \Theta^{p^*H} \vdash_{\text{sm}} b^{(1,h)} \gamma' y' \equiv (b^h)^d \gamma' y'$$

For the inductive step of 1, we have

$$2 \times (I \oplus H) = (2 \times I) \oplus (i_0)_! H \oplus (p^*H \cup \{(\xi, 1_\star)\}).$$

Thus, using 2, we have

$$\Gamma^{2 \times (I \oplus H)}$$

$$\equiv \left( \gamma' : \Gamma^{(2 \times I)}, A_{(0,\star)} : \Theta^{(i_0)_!} H \to \text{Type}_\ell, A_{(1,\star)} : \Theta^{(p^*H \cup \{(\xi, 1_\star)\})} \to \text{Type}_\ell \right)$$

$$\equiv \left( \gamma' : (\Gamma^I)^D, A_{(0,\star)} : \Theta^H \gamma'^{\text{ev}} \to \text{Type}_\ell, A_{(1,\star)} : (y' : (\Theta^H)^D \gamma') \to A_{(0,\star)} y'^{\text{ev}} \to \text{Type}_\ell \right)$$

$$\equiv \left( \gamma : \Gamma^I, A_\star : \Theta^H \gamma \to \text{Type}_\ell \right)^D.$$

The other cases are similar. We can likewise show that

$$\Gamma^{I, 2 \times I} \equiv (\Gamma^I)^d,$$

with the isomorphism $\Gamma^{2 \times I} \cong (\Gamma^I \mid \Gamma^{I, 2 \times I})$ coinciding with the evens/odds pairing isomorphism $(\Gamma^I)^D \cong (\Gamma^I \mid (\Gamma^I)^d)$.

**4.5.5.5 Discrete fibrations.** The isomorphism $\Gamma^I \cong (\Gamma^I \mid \Gamma^{J,I})$ ensures that if $J \subseteq I$ is a sieve, we have a weakening substitution $\Gamma^I \to \Gamma^J$. But more generally, we can expect to induce a context substitution from any discrete fibration. Even more generally, we can get a *partial* substitution from a 'dependent' discrete fibration, in the following sense.

**Definition 4.57.** If $i : J \hookrightarrow I$ is the inclusion of a sieve in a direct category, a **co-section** of it is a discrete fibration $p : I \to J$ such that $p \circ i = 1_J$. In this case, if $H$ is a presheaf on $I$ and $K$ a presheaf on $J$, a morphism $H \to K$ over $p$ is a **relative isomorphism** if it induces a bijection $\sum_{y \in I} H(y) \to \sum_{y \in J} K(y)$.

Note that the projection $p : 2 \times I \to I$ above is *not* a co-section of the sieve $i_0 : I \hookrightarrow 2 \times I$, since it is not a discrete fibration. The prototypical example of a relative isomorphism is $\partial \mathcal{K}_x \to \partial \mathcal{K}_{p(x)}$ for any $x \in I$ (this is essentially the definition of a discrete fibration).

Now we define and prove inductively:

94