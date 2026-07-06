Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:37

(i) A partition of the objects of $|\mathbb{D}|$ (which we call **sorts**) into **primitive sorts** and **derived sorts**.
(ii) For each derived sort $R$, there is exactly one $\mathbb{D}$-cone $G_R : \mathcal{C}_R \to |\mathbb{D}|$ whose concrete vertex $G(K)$ is $R^-$ or $R^+$, and this is an arrow-type cone whose other vertex $G(L)$ is a primitive sort. We call it the **sorting cone** for $R$.

**Definition 6.3.** Let $\mathbb{D}$ be a sorted doctrine and $\pi : \mathcal{S} \to |\mathbb{D}|$ a $\mathbb{D}$-sketch.

- $\mathcal{S}$ is **well-sorted** if for every derived sort $R$ and every object $\widetilde{R} \in \pi^{-1}(R)$, there exists a proto-extremal lift of $G_R$ that maps the vertex to $\widetilde{R}$.
- $\mathcal{S}$ is **strictly well-sorted** if for every derived sort $R$ with corresponding primitive sort $S$, there is a specified bijection between the objects of $\pi^{-1}(R)$ and $\pi^{-1}(S)$ and, for each $\widetilde{R}$ and $\widetilde{S}$ that correspond under this bijection, a specified proto-extremal lift of $G_R$ with entries $\widetilde{R}$ and $\widetilde{S}$.

We write $\mathbb{D}$-sCat for the 2-category of well-sorted $\mathbb{D}$-complete sketches ($\mathbb{D}$-categories).

Thus a $\mathbb{D}$-category is well-sorted if and only if the functor $\pi^{-1}(S) \to \pi^{-1}(R)$ induced by each sorting cone is essentially surjective on objects, and strictly well-sorted if a particular choice of this functor has been made that is bijective on objects. We are “really” interested in the strictly well-sorted sketches, but the non-strictly well-sorted ones are more convenient to work with technically. Fortunately we have the following:

**Proposition 6.4.** *For a sorted doctrine $\mathbb{D}$, every well-sorted $\mathbb{D}$-category is equivalent in $\mathbb{D}$-Sketch to a strictly well-sorted one.*

*Proof.* If $\pi : \mathcal{S} \to |\mathbb{D}|$ is well-sorted, for each derived sort $R$ with corresponding primitive sort $S$ we have an essentially surjective functor $\pi^{-1}(S) \to \pi^{-1}(R)$. Thus, we can replace $\pi^{-1}(R)$ by an equivalent category whose objects are those of $\pi^{-1}(S)$, making the functor bijective on objects. These equivalences on fibers extend to an equivalence of $\mathbb{D}$-categories. $\square$

Thus, $\mathbb{D}$-sCat is equivalent (as a bicategory) to its full sub-2-category of strictly well-sorted $\mathbb{D}$-categories.

**Example 6.5.** Any LNL doctrine can be made sorted with all sorts primitive, so that all $\mathbb{D}$-sketches are (vacuously) strictly well-sorted.

**Example 6.6.** Let $\mathbb{D}$ be any doctrine for which $|\mathbb{D}|$ has exactly one nonlinear object $\mathbf{x}$ and one linear object $\mathbf{A}$, such as LNLMULTI or the terminal object LNLPOLY. Suppose furthermore that the only $\mathbb{D}$-cone with vertex $\mathbf{x}^\pm$ is an arrow-type cone with vertex $\mathbf{x}^-$ and abstract projection in $\mathcal{C}(\mathbf{A}^+, \mathbf{x}^-)$ (that is, a U-cone). Then we can make $\mathbb{D}$ a sorted doctrine where $\mathbf{A}$ is primitive, $\mathbf{x}$ is derived, and this cone is the sorting cone.

We call this a **Kleisli sorted** doctrine. Then a $\mathbb{D}$-category is strictly well-sorted just when it is of Kleisli type (Definition 3.9). If $\mathbb{D}$ also contains $\mathsf{F}$, then by Lemma 3.8 this is equivalent to its being the Kleisli adjunction of the comonad $! = \mathsf{FU}$. Thus, the 2-category of symmetric monoidal categories with a linear exponential comonad, and its variants with internal-homs and/or limits and colimits, are equivalent to $\mathbb{D}$-sCat for some sorted LNL doctrine $\mathbb{D}$. Similarly, by taking an $\mathsf{F}$-cone as sorting we can represent cartesian monoidal categories with a commutative strong monad.

**Example 6.7.** Let $\mathbb{D}$ be the sorted doctrine defined as follows. We take $|\mathbb{D}| = \text{DBLSPLIT}$, as in Remark 2.7; thus a functor $\pi : \mathcal{P} \to |\mathbb{D}|$ partitions the nonlinear objects of $\mathcal{P}$ into left-hand and right-hand ones. We equip $\mathbb{D}$ with cones for $\otimes, \mathbb{1}, \mathcal{A}, \bot$, as well as $\mathsf{F}$ defined on