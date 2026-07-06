COMPACT HAUSDORFF LOCALES IN PRESHEAF TOPOSES

9

**Theorem 5.1.** *For any small category $\mathcal{C}$ there is an equivalence of categories*

$$\mathbf{KRegFrm}_{\mathcal{C}} \simeq [\mathcal{C}^{op}, \mathbf{KRegFrm}].$$

*Proof.* Firstly, recall that $\mathbf{NDL}_{\mathcal{C}}$ is isomorphic to $[\mathcal{C}^{op}, \mathbf{NDL}]$; this is implicit in the exposition above as it is the category of models of a geometric theory, or consult D.1.2.14 of [J02]. We can therefore treat compact regular frames in $\tilde{\mathcal{C}}$, firstly as normal distributive lattices via the forgetful functor and then as functors $\mathcal{C}^{op} \to \mathbf{NDL}$. That is, in what follows we identify $\mathbf{KRegFrm}_{\mathcal{C}}$ with the non-full subcategory of $[\mathcal{C}^{op}, \mathbf{NDL}]$ which is fixed by the idempotent endofunctor $C_{\tilde{\mathcal{C}}} = \widetilde{C \circ \_}$. We define the two functors:

$$\Phi : \begin{array}{c c c} \mathbf{KRegFrm}_{\tilde{\mathcal{C}}} & \to & [\mathcal{C}^{op}, \mathbf{KRegFrm}] \\ L & \mapsto & C \circ L \end{array}$$

$$\Psi : \begin{array}{c c c} [\mathcal{C}^{op}, \mathbf{KRegFrm}] & \to & \mathbf{KRegFrm}_{\tilde{\mathcal{C}}} \\ A & \mapsto & \tilde{A} \end{array}$$

These are well defined: given $L \in \mathbf{KRegFrm}_{\tilde{\mathcal{C}}}$, and more generally any $L \in [\mathcal{C}^{op}, \mathbf{NDL}]$, the composite $C \circ L$ determines a functor $\mathcal{C}^{op} \to \mathbf{KRegFrm}$; and this is clearly natural in $L$. For any $A \in [\mathcal{C}^{op}, \mathbf{KRegFrm}]$, we have $A \cong C \circ A$ (functorially), and hence $\tilde{A} \simeq \widetilde{C \circ A} \simeq C_{\tilde{\mathcal{C}}}(A)$, hence $\tilde{A}$ being of the form $C_{\tilde{\mathcal{C}}}(\_)$ it is a compact regular frame in $\tilde{\mathcal{C}}$ by an internal application of Proposition 2.4.

Certainly $L \cong C_{\tilde{\mathcal{C}}}L \cong \widetilde{C \circ L}$, from which $\Psi \Phi \cong Id_{\mathbf{KRegFrm}_{\tilde{\mathcal{C}}}}$.

So we have to but check $\Phi \Psi \cong Id_{[\mathcal{C}^{op}, \mathbf{KRegFrm}]}$; that is, that $C \circ \tilde{A} \cong A$ naturally for each $A : \mathcal{C}^{op} \to \mathbf{KRegFrm}$. Since $\tilde{A}$ is a compact regular frame in $\tilde{\mathcal{C}}$ we know that there is an isomorphism $\alpha : \widetilde{C \circ \tilde{A}} \to \tilde{A}$; this gives rise to a lax natural transformation $\psi^{\alpha} : C \circ \tilde{A} \to A$, using the notation of Lemma 3.7. But then note that for any object $a$ of $\mathcal{C}$, $\psi_{a}^{\alpha} : C \circ \tilde{A} \to A(a)$ is a suplattice homomorphism as well as a lattice homomorphism; i.e. it is a frame homomorphism. (Recall Example 3.2; so the $\epsilon$ and $\mu$ used to construct $\psi^{\alpha}$ are both also suplattice homomorphisms and certainly $\alpha_{a}$ is a suplattice homomorphism as it is an order-isomorphism.) But then $\psi_{a}^{\alpha}$ is a frame homomorphism between compact regular frames, so we can use $\psi^{Id_{\tilde{F}}} = Id_{F}$ and $\psi^{\beta}\psi^{\alpha} \sqsubseteq \psi^{\beta\alpha}$ established in Lemma 3.7 to see that $\psi_{a}^{\alpha}$ is an isomorphism; this is because the partial ordering of frame homomorphisms between compact regular frames is discrete (e.g. III Lemma 1.5 of [J82]). Next, $\psi^{\alpha}$ is constructed as a lax natural transformation, but in fact it can be seen to be a natural transformation as the homsets of $\mathbf{KRegFrm}$ are discrete. Finally, for naturality in $A$, recall part (ii) of Lemma 3.7; again we only have lax-naturality from the Lemma, but this is sufficient as the morphisms involved are all frame homomorphisms between compact regular frames.

(Note in the above that relative to both our base topos $\mathbf{Set}$ and $\tilde{\mathcal{C}}$ we are passing through a forgetful functor back to $\mathbf{NDL}$ without notation; however, these forgetful functors create isomorphisms.)

**Remark 5.2.** It should be noted that Theorem 25 of [SVW14] also in effect provides this description of compact regular frames in a presheaf topos

**Remark 5.3.** It should be noted that, Joyal and Tierney gave in [JT84] a general description of internal frames in the topos $\tilde{\mathcal{C}}$, at least in the case where $\mathcal{C}$ has finite limits, which in theory could be specialized to a description of compact regular