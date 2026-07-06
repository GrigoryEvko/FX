11:40

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

that the diagram commutes. Switching to type-theoretic notation, this amounts to a type $L(\Delta) \vdash A$ type—which gives rise to a type $R(L(\Delta)) \vdash \mathsf{R}(A)$ type by applying $\mathsf{R}$—and a term $\Delta \vdash M : \mathsf{R}(A)[\eta_\Delta]$. The universal property of the pullback dictates that we must show the existence of a unique term $L(\Delta) \vdash N : A$ such that

$$RL(\Delta) \vdash \mathsf{r}(N)[\eta_\Delta] = M : \mathsf{R}(A)[\eta_\Delta] \quad (7.4)$$

First, observe that we can form the substitution $\eta_\Delta.M : \Delta \to RL\Delta.\mathsf{R}(A)$. We can then postcompose the isomorphism $\nu_{\Delta,A}$ to obtain a morphism of type $\Delta \to R(L\Delta.A)$. To this we can apply $L$ and postcompose the counit $\epsilon_{L\Delta.A}$ to obtain a substitution

$$k \triangleq \epsilon_{L\Delta.A} \circ L(\nu_{\Delta,A} \circ \eta_\Delta.M) : L\Delta \to L\Delta.A$$

Using naturality of the counit and the equations satisfied by the canonical isomorphism $\nu_{\Delta,A}$, it is easy to show that $\mathbf{p} \circ k = \mathsf{id} : L\Delta \to L\Delta$, and hence that we can extract a term

$$L(\Delta) \vdash N \triangleq \mathbf{q}[k] : A$$

Using naturality of $\mathsf{r}(-)$, naturality of the unit, and one of the triangle identities, we can calculate that this term satisfies equation (7.4). Finally, we can prove this choice is unique by calculating that any such $N$ necessarily satisfies $k = \mathsf{id}.N$, and hence that $\mathbf{q}[k] = N$.

It is routine to show that this is size-preserving, using the fact that $\mathsf{R}$ preserves size. $\square$

The converse is not in general true: a dependent right adjoint need not extend to a functor on the category of contexts. Nevertheless, it does whenever the category of contexts is *democratic* [CD14], i.e. if every context is isomorphic to extending the empty context by some type: see [BCM$^+$20, §4.1] for a proof.

## 8. PRESHEAF MODELS

It is well-known that the category $\mathbf{PSh}(\mathcal{C})$ of presheaves over any small category $\mathcal{C}$ is a model of Martin-Löf type theory. A functor $\mu : \mathcal{C} \to \mathcal{D}$ induces by *precomposition* a functor

$$\mu^* : \mathbf{PSh}(\mathcal{D}) \to \mathbf{PSh}(\mathcal{C})$$

between categories of presheaves. This functor has a right adjoint

$$\mu_* : \mathbf{PSh}(\mathcal{C}) \to \mathbf{PSh}(\mathcal{D})$$

given by *right Kan extension* [ML78, §X.3] [Awo10, §9.6] [Rie16, §6]. We show that an appropriately functorial version of this structure can be bootstrapped into a model of MTT, where the modalities are right adjoints to this precomposition functor. More concretely, starting with a small 2-category $\mathcal{I}$, and a functor

$$J : \mathcal{I} \to \mathbf{Cat}$$

we will construct a model of MTT where each mode corresponds to the category $\mathbf{PSh}(J(i))$, and the modalities are the functors $J(f)_*$, for each $f \in \mathrm{Hom}_{\mathcal{I}}(i_0, i_1)$.