## 4.2 Invariance along Barton trivial fibrations

In this section we introduce a class of left Quillen functor that we call *Barton trivial fibrations* as they are essentially a non-simplicial version of the trivial fibrations of the model structure constructed by Barton in [Bar19], and we establish that theorem 4.2 holds for these particular functors.

**Definition 4.9.** Let $F : \mathcal{C} \to \mathcal{D}$ a morphism between $\kappa$-coclans. We say that $F$ is *extensible* if for every object in $X \in \mathcal{C}$ and for any cofibration $g : FX \hookrightarrow Y \in \mathcal{D}$ there exists $f : X \hookrightarrow Z$ and an isomorphism $F(Z) \cong Y$ making the obvious triangle commutative.

Dually, $F : \mathcal{C} \to \mathcal{D}$ a morphism between $\kappa$-clans is *extensible* if the induced map of $\kappa$-coclans $F^{\mathrm{op}} : \mathcal{C}^{\mathrm{op}} \to \mathcal{D}^{\mathrm{op}}$ is extensible.

In our setting, a functor $F : \mathcal{M} \to \mathcal{N}$ between weak model categories will be called extensible if the cocclan morphism $F : \mathcal{M}^{\mathrm{COF}} \to \mathcal{N}^{\mathrm{COF}}$ is extensible.

The terminology *extensible* in the definition above for both clans and cocclans, instead of “extensible” and “co-extensible”, is simply because it is always clear whether it refers to cofibrations or fibrations. This is because, for example, when considering a morphism between clans the relevant structure that ought to be preserved is that related to fibrations. The name extensible from theorem 4.9 is adapted from Reid Barton’s PhD thesis [Bar19, Definition 8.3.1].

**Definition 4.10.** A left Quillen functor $F : \mathcal{M} \to \mathcal{N}$ between weak model categories is called *weakly conservative* if for any core cofibration $x \hookrightarrow y \in \mathcal{M}^{\mathrm{COF}}$ such that $h : Fx \xrightarrow{\sim} Fy$ is a trivial cofibration, the map $x \hookrightarrow y$ is a trivial cofibration.

The ‘weakly’ part in the previous definition does not come from weak model categories, but rather from the fact that core trivial cofibrations are weak equivalences.

**Definition 4.11.** Let $F : \mathcal{M} \to \mathcal{N}$ a left Quillen functor between weak model categories. We say that $F$ is a *Barton trivial fibration* if it is extensible as a morphism between of the cocclans $\mathcal{M}^{\mathrm{COF}}$ and $\mathcal{N}^{\mathrm{COF}}$ and weakly conservative.

*Remark 4.12.* Barton trivial fibrations which are also simplicial Quillen functors between combinatorial simplicial model categories are exactly the trivial fibrations in [Bar19] in the model 2-category of pre-model categories. As the reader might anticipate, the notion of fibration between (simplicial) model categories exists as well, but we will make no use of it.

62