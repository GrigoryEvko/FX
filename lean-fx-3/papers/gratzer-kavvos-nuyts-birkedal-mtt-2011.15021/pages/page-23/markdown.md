Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:23

where $\gamma': \Delta \to \Gamma'$ is the unique arrow that makes the diagram commute. The requirement that this diagram be a pullback leads us to the following definition.

**Definition 5.4.** A *modal natural model* on a context structure $[\![-\!]]: \mathcal{M}^{\text{coop}} \to \mathbf{Cat}_1$ consists of a family of natural transformations of presheaves

$$\left(\tau_m : \widetilde{\mathcal{T}}_m \Rightarrow \mathcal{T}_m\right)_{m \in \mathcal{M}}$$

where $\widetilde{\mathcal{T}}_m, \mathcal{T}_m: \mathbf{PSh}(\mathcal{C}[m])$ such that for every $\mu: \text{Hom}_{\mathcal{M}}(m, n)$ the natural transformation

$$[\![\widehat{\bullet}_\mu]\!]^* \tau_n : [\![\widehat{\bullet}_\mu]\!]^* \widetilde{\mathcal{T}}_n \Rightarrow [\![\widehat{\bullet}_\mu]\!]^* \mathcal{T}_n$$

is a natural model.

We will write $\Gamma.(\mu \mid A)$ for the object $\Gamma'$ that makes (5.3) a pullback, as we do in the type theory.

**5.2. Connectives.** We shall only discuss the key cases of $\Pi$ types, modal types, Boolean types, and universes. The interpretation of the other connectives largely follows the style of [Awo18]. More details can be found in the tech report [GKNB20].

**5.2.1. $\Pi$ Structure.** Even though MTT $\Pi$ types are close to traditional $\Pi$ types they are not quite the same, as they involve a modality in the domain. Thus, we need to construct an appropriate variation of the interpretation given by [Awo18]. To begin, we need some way to represent the *binding* of an additional assumption. This is achieved through the use of *polynomial endofunctors*. Given a 'display map' $\ell: E \to B$ we define a polynomial endofunctor $\mathbf{P}_{\ell:E \to B}: \mathbf{PSh}(\mathcal{C}[m]) \to \mathbf{PSh}(\mathcal{C}[m])$ by$^4$

$$\mathbf{P}_{\ell:E \to B}(A) \triangleq \sum_{b:B} A^{\ell^{-1}(b)}$$

When specialized to the 'modalized' natural model $\ell \triangleq [\![\widehat{\bullet}_\mu]\!]^*(\tau_n): [\![\widehat{\bullet}_\mu]\!]^* \widetilde{\mathcal{T}}_n \Rightarrow [\![\widehat{\bullet}_\mu]\!]^* \mathcal{T}_n$, this functor has a useful property: morphisms $\mathbf{y}(\Gamma) \Rightarrow \mathbf{P}_{[\![\widehat{\bullet}_\mu]\!]^* \tau_n}(\mathcal{T}_m)$ are in bijection with tuples

$$(A \in \mathcal{T}_n([\![\widehat{\bullet}_\mu]\!](\Gamma)), B \in \mathcal{T}_m(\Gamma.(\mu \mid A))) \tag{5.4}$$

This enables the representation of a pair of types $\Gamma.\widehat{\bullet}_\mu \vdash A \text{ type}_1 @ n$ and $\Gamma.(\mu \mid A) \vdash B \text{ type}_1 @ m$—i.e. the premises of $\Pi$ formation—as a single morphism $\mathbf{y}(\Gamma) \Rightarrow \mathbf{P}_{[\![\widehat{\bullet}_\mu]\!]^* \tau_n}(\mathcal{T}_n)$. A similar observation applies to the presheaf of terms $\widetilde{\mathcal{T}}_m$. See [Awo18, Lemma 5] for a detailed proof of this property.

A model is equipped with a $\Pi$-structure if for $\mu: \text{Hom}_{\mathcal{M}}(n, m)$ we have a pullback

$$\begin{array}{ccc} \mathbf{P}_{[\![\widehat{\bullet}_\mu]\!]^* \tau_n}(\widetilde{\mathcal{T}}_m) & \xrightarrow{\text{lam}} & \widetilde{\mathcal{T}}_m \\ \downarrow & & \downarrow \\ \mathbf{P}_{[\![\widehat{\bullet}_\mu]\!]^* \tau_n}(\mathcal{T}_m) & \xrightarrow[\Pi]{} & \mathcal{T}_m \end{array}$$

$^4$This is given in the internal language, but may also be written purely categorically, as is done in *op. cit.*