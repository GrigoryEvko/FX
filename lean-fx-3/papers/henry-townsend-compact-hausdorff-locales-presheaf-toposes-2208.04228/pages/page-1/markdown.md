arXiv:2208.04228v1 [math.CT] 8 Aug 2022

# COMPACT HAUSDORFF LOCALES IN PRESHEAF TOPOSES

SIMON HENRY AND CHRISTOPHER TOWNSEND

ABSTRACT. We prove that for any small category $\mathcal{C}$, the category $\mathbf{KHausLoc}_{\hat{\mathcal{C}}}$ of compact Hausdorff locales in the presheaf topos $\hat{\mathcal{C}}$, is equivalent to the category of functors $\mathcal{C} \rightarrow \mathbf{KHausLoc}$.

## 1. INTRODUCTION

In this paper we prove for any small category $\mathcal{C}$ that there is an equivalence of categories:

$$\mathbf{KRegFrm}_{\hat{\mathcal{C}}} \simeq [\mathcal{C}^{op}, \mathbf{KRegFrm}]$$

where $\mathbf{KRegFrm}$ is the category of compact regular frames, $\hat{\mathcal{C}}$ is the presheaf topos $[\mathcal{C}^{op}, \mathbf{Set}]$ and $\mathbf{KRegFrm}_{\hat{\mathcal{C}}}$ is the category of compact regular frames in the topos $\hat{\mathcal{C}}$. Since $\mathbf{KRegFrm}$ is dual to the category of compact Hausdorff locales ($\mathbf{KHausLoc}$) in every topos, the claim of the abstract is shown with this categorical equivalence.

This result can be thought of as a new example of “open/proper duality” (e.g. [T06]). Indeed, discrete locales are locales $X$ such that both the unique map $X \rightarrow 1$ and the diagonal map $X \rightarrow X \times X$ are open maps, and discrete locales in the topos $\hat{\mathcal{C}}$ correspond to presheaves on $\mathcal{C}$; that is, to functors $\mathcal{C}^{op} \rightarrow \mathbf{Set}$. In this note, we are proving that “dually”, compact Hausdorff locales in $\hat{\mathcal{C}}$, that is locales $X$ in $\hat{\mathcal{C}}$ such that both the unique map $X \rightarrow 1$ and the diagonal map $X \rightarrow X \times X$ are proper, correspond to functors $\mathcal{C} \rightarrow \mathbf{KHausLoc}$.

In summary, the proof proceeds as follows. In section 2 we show that compact regular frames can be characterised as completions of normal distributive lattices, with the completion given by an idempotent functor $C$ acting on the category of normal distributive lattices ($\mathbf{NDL}$). This characterisation applies internally in the presheaf topos $\hat{\mathcal{C}}$, hence we have established that any compact regular frame in $\hat{\mathcal{C}}$ is the completion of an object of $\mathbf{NDL}_{\hat{\mathcal{C}}}$. Because the notion of normal distributive lattice is geometric (in the sense of geometric logic, e.g. D1 of [J02]), we have an isomorphism of categories $\mathbf{NDL}_{\hat{\mathcal{C}}} \cong [\mathcal{C}^{op}, \mathbf{NDL}]$. These observations give us a way of understanding the category $\mathbf{KRegFrm}_{\hat{\mathcal{C}}}$ as consisting of objects obtained by completing objects of $[\mathcal{C}^{op}, \mathbf{NDL}]$. To conclude the proof we need an explicit description of the relative version of the idempotent endofunctor $C$, acting on $\mathbf{NDL}_{\hat{\mathcal{C}}}$ and essentially this is what is provided by the rest of the paper.

In section 3 we introduce a categorical construction on presheaves taking values in an order enriched category. This construction is adjoint to the forgetful functor from the category of presheaves and natural transformation to the category of presheaves and lax natural transformation. In section 4, we give examples of this construction and explain how it is used to describe the relative version of the construction $C$

2020 Mathematics Subject Classification. 06D22, 18B25, 18F20, 18F70.

1