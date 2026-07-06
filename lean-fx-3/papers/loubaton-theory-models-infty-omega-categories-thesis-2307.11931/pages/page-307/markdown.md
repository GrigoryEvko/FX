5.2. CARTESIAN FIBRATIONS

5.2.5.21. We now suppose that the morphism $i : I \to A^{\sharp}$ is smooth, and we are willing to construct a morphism $i_* : \underline{\mathrm{LCart}}(A^{\sharp}) \to \underline{\mathrm{LCart}}(I)$ which corresponds to $\mathbf{R}i_* : \mathrm{LCart}^c(I) \to \mathrm{LCart}(A^{\sharp})$ on the sub maximal $(\infty, 1)$-categories..

As smooth morphisms are stable by pullback, the maps $i \times id_b^b$ are smooth for any $b : \Theta$. The morphism $i^* : E_0 \to E_1$ then preserves colimits and fits into an adjunction

$$ i^* : E_1 \underset{\perp}{\overset{\longrightarrow}{\longleftarrow}} E_0 : i_* \tag{5.2.5.22} $$

where the left adjoint sends a left cartesian fibration $p$ over $A^{\sharp} \times a^{\flat}$ to $(i \times id_a)^*p$ and the right adjoint sends a left cartesian fibration $q$ over $I \times a^{\flat}$ to $\mathbf{R}(i \times id_a)_*q$.

Lemma 5.2.5.23. Let $p$ be a left cartesian fibration over $I$. We have an equivalence

$$ \mathbf{R}(i \times id_{a^{\flat}})_*(p \times id_{a^{\flat}}) \sim (\mathbf{R}i_*p) \times id_{a^{\flat}}. $$

Proof. The morphism $p \times id_{a^{\flat}}$ is the limit of the cospan

$$ p \to id_I \leftarrow id_I \times id_{a^{\flat}} $$

The result is then a direct consequence of the fact that $\mathbf{R}i_*$ preserves limits as it is a right adjoint.

We recall that $\tilde{E}_0$ and $\tilde{E}_1$ are defined as the full sub $(\infty, 1)$-categories of $E_0$ and $E_1$ whose objects are respectively of shape $p \times id_a$ and $q \times id_a$ for $p$ and $q$ classified left cartesian fibrations over $I$ and $A^{\sharp}$. The lemma 5.2.5.23 and the second assertion of lemma 5.2.5.13 imply that (5.2.5.22) restricts to an adjunction

$$ i^* : \tilde{E}_1 \underset{\perp}{\overset{\longrightarrow}{\longleftarrow}} \tilde{E}_0 : i_* \tag{5.2.5.24} $$

Lemma 5.2.5.25. Let $q \to q'$ be a morphism in $\tilde{E}_0$ corresponding to a cartesian square. The induced morphism $i_*(q) \to i_*(q')$ also corresponds to a cartesian square.

Proof. The proof is similar to that of the lemma 5.2.5.15, using lemma 5.2.5.23 instead of lemma 5.2.5.13.

The lemmas 5.2.5.15 and 5.2.5.25 imply that the two adjoints of (5.2.5.24) preserve the cartesian cells of the Grothendieck fibrations $\tilde{E}_0 \to \Theta$ and $\tilde{E}_1 \to \Theta$. These two adjoints then induce by Grothendieck deconstruction a family of adjunction

$$ (i_a)^* : \mathrm{LCart}(A^{\sharp}; a) \underset{\perp}{\overset{\longrightarrow}{\longleftarrow}} \mathrm{LCart}^c(I; a) : (i_a)_* \tag{5.2.5.26} $$

natural in $a : \Theta^{op}$. The family of functors $(i_a)_*$ then induces a morphism of $(\infty, \omega)$-categories

$$ i_* : \underline{\mathrm{LCart}}^c(I) \to \underline{\mathrm{LCart}}(A^{\sharp}) \tag{5.2.5.27} $$

297