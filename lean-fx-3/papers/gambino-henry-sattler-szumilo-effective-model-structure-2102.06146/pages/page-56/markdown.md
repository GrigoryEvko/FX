that they are sufficiently well-behaved for our purposes. Indeed, a particularly simple characterisation of cofibrations (they coincide with levelwise complemented inclusions, see Lemma 12.3) enables certain arguments unavailable in $\mathfrak{s}\mathcal{E}$.

The critical result that is that the homotopy theories of simplicial and semisimplicial objects in $\mathfrak{s}\mathcal{E}$ are equivalent (Theorem 12.6). We will show that under the assumption that $\mathcal{E}$ is either countably complete (Theorem 12.8) or countably lextensive (Theorem 12.17).

We begin by introducing some basic concepts. Since these are largely analogous to the simplicial case, we only treat them briefly, mainly to fix the notation. We write $\Delta_+$ for the subcategory of $\Delta$ consisting of the face operators (i.e., the injective maps) and $\mathfrak{s}_*\mathcal{E} = [\Delta_+^{\mathrm{op}}, \mathcal{E}]$ for the category of semisimplicial objects in $\mathcal{E}$. In particular, $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ is the category of semisimplicial sets. The representable semisimplicial sets are denoted by $\Delta_+[n]$. For any finite semisimplicial set $K$, we define the *evaluation functor* $\mathrm{ev}_K: \mathfrak{s}\mathcal{E} \to \mathcal{E}$ as

$$\mathrm{ev}_K(X) = \int_{[n] \in \Delta_+} X_n^{K_n}.$$

The category $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ carries a non-Cartesian closed symmetric monoidal structure whose tensor is called the *geometric product* and denoted by $\boxtimes$. It is uniquely determined by the property that $\Delta_+[m] \boxtimes \Delta_+[n]$ is the semisimplicial set of non-degenerate simplices in the nerve of the poset $[m] \times [n]$.

The forgetful functor $U: \mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t} \to \mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ has both the left adjoint $L$ and the right adjoint $R$ given by $\mathfrak{K}\mathfrak{n}$ extensions along the inclusion $\Delta_+ \to \Delta$. The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ also has the left or the right adjoint if $\mathcal{E}$ is countably lextensive (or even just finitely cocomplete) or countably complete, respectively. These will be used in the proofs of the two variants of this section's main theorem announced above.

The homotopy theory of semisimplicial sets is well established. Weak homotopy equivalences are defined as semisimplicial maps that become simplicial weak homotopy equivalences upon applying the functor $L$. The category $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ also carries classes of (trivial) fibrations and cofibrations, defined below. These do not form a model structure, but they satisfy certain weaker axioms. E.g., $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ is a weak model category (and even a right semi-model category), see [Hen19, Section 5.5]. For our purposes, Theorem 12.2 below is sufficient.

For a finite semisimplicial set $K$ and $X \in \mathfrak{s}_*\mathcal{E}$ we define the cotensor $K \pitchfork X \in \mathfrak{s}_*\mathcal{E}$ by letting

$$(K \pitchfork X)_n = X(\Delta_+[n] \boxtimes K)$$

and the semisimplicial hom-object

$$\mathrm{Hom}_{\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}}(X, Y)_n = \mathrm{Hom}_{\mathfrak{S}\mathfrak{e}\mathfrak{t}}(X, \Delta_+[n] \pitchfork Y).$$

Exactly as in the simplicial case, this makes $\mathfrak{s}_*\mathcal{E}$ into a $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$-enriched category with respect to the geometric product and $\pitchfork$ becomes the cotensor for this enrichment.

The boundaries $\partial\Delta_+[n]$ and horns $\Lambda_+^k[n]$ are defined analogously to their simplicial counterparts ($\partial\Delta_+[n]$ consists of non-degenerate simplices of $\partial\Delta[n]$ and similarly for $\Lambda_+^k[n]$). This gives rise to the generating sets

$$\begin{aligned} I_{\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}} &= \{\partial\Delta_+[n] \to \Delta_+[n]\} \text{ and } J_{\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}} = \{\Lambda_+^k[n] \to \Delta_+[n]\} \text{ in } \mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t} \\ \text{ and } I_{\mathfrak{s}_*\mathcal{E}} &= \{\underline{\partial\Delta_+[n]} \to \underline{\Delta_+[n]}\} \text{ and } J_{\mathfrak{s}_*\mathcal{E}} = \{\Lambda_+^k[n] \to \underline{\Delta_+[n]}\} \text{ in } \mathfrak{s}_*\mathcal{E}. \end{aligned}$$

Then a morphism $X \to Y$ in $\mathfrak{s}\mathcal{E}$ is a *fibration* if the pullback evaluation

$$X(\Delta_+[n]) \to X(\Lambda_+^k[n]) \times_{Y(\Lambda_+^k[n])} Y(\Delta_+[n])$$

56