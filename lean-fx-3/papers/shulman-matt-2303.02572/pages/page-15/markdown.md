Shulman

18–15

**Theorem 6.1** Let $\mathcal{L}$ be a 2-category with a class of morphisms $\mathcal{S}$. If an adjoint modal pre-model $(\widehat{\mathcal{C}}, \mathcal{C})$ over $(\mathcal{L}, \mathcal{S})$ is such that $\mathcal{C}$ has pre-$\Pi$-structure, positive pre-modalities, and negative pre-modalities over $\mathcal{L}[\mathcal{S}^{\dagger}]$, then $(\widehat{\mathcal{C}}, \widehat{\tau}^{\dagger})$ models MATT over $\mathcal{L}[\mathcal{S}^{\dagger}]$. $\square$

Any category with pullbacks has a canonical natural pseudo-model where all maps are type projections.

**Lemma 6.2** Let $\mathcal{M}$ be an adjoint mode theory, and $\mathcal{C}: \mathcal{M} \to \mathcal{C}$ at be a pseudofunctor such that each $\mathcal{C}_p$ is locally cartesian closed. If we make $\mathcal{C}$ a modal pre-model in the canonical way, as above, then it has pre-$\Pi$-structure, positive pre-modalities, and negative pre-modalities.

**Proof.** Since $\mathcal{C}_p$ is locally cartesian closed and everything is a type projection, we have pre-$\Pi$-structure. For positive pre-modalities we take $i_{\Gamma,A}^{\mu}$ to be an identity, and similarly for negative pre-modalities. $\square$

**Theorem 6.3** Let $\kappa$ be an infinite regular cardinal, $\mathcal{L}$ a $\kappa$-small 2-category with a class of morphisms $\mathcal{S}$, and $\mathcal{C}: \mathcal{L} \to \mathcal{C}$ at a pseudofunctor such that each $\mathcal{C}_p$ is locally cartesian closed with $\kappa$-small limits, each $\mathcal{C}_{\mu}$ preserves $\kappa$-small limits, and has a right adjoint if $\mu \in \mathcal{S}$. Then $\widehat{\mathcal{C}}$ models extensional MATT over $\mathcal{L}[\mathcal{S}^{\dagger}]$.

**Proof.** By Lemma 4.5, local cartesian closure lifts from $\mathcal{C}$ to $\widehat{\mathcal{C}}$. Thus, $(\widehat{\mathcal{C}}, \mathcal{C})$ is an adjoint modal pre-model, so Theorem 6.1 and Lemma 6.2 yield a model of MATT. Composition and diagonals yield weakly stable $\Sigma$-types and extensional identity types in each $\mathcal{C}_p$, hence mode-locally by Theorem-Schema 5.7. $\square$

**Remark 6.4** In addition, the following should follow from Lemma 4.5 and Theorem-Schema 5.7.

- If each $\mathcal{C}_p$ has finite coproducts, then $\widehat{\mathcal{C}}$ models sum types at each mode.
- If each $\mathcal{C}_p$ is locally presentable and each $\mathcal{C}_{\mu}$ is accessible, then each $\widehat{\mathcal{C}}_p$ is again locally presentable. Thus, by the methods of [28], $\widehat{\mathcal{C}}$ models inductive types and quotient-inductive types at each mode.
- If $\mathcal{C}$ is a diagram of Grothendieck topoi and geometric morphisms, then each $\widehat{\mathcal{C}}_p$ is also a topos. Thus, if there are enough inaccessible cardinals, $\widehat{\mathcal{C}}$ models universes at each mode (see [16,41,13,39]).

Let $\mathcal{T}$opos denote the 2-category of Grothendieck topoi, geometric morphisms, and transformations.

**Theorem 6.5** Let $\mathcal{L}$ be a finite 2-category and $\mathcal{E}: \mathcal{L}^{\mathrm{coop}} \to \mathcal{T}$opos a pseudofunctor. Then the co-dextrification $\widehat{\mathcal{E}}$ models extensional MATT over $\mathcal{L}[\mathcal{L}^{\dagger}]$, with positive and negative modalities representing inverse image and direct image functors respectively, and extensional MLTT at each mode. $\square$

**Remark 6.6** Theorem 6.5 does not state explicitly how to extract conclusions about $\mathcal{E}$ from the interpretation of MATT in $\widehat{\mathcal{E}}$. We will not try to make this precise here, but the idea is that $\widehat{\mathcal{E}}_p$ can be viewed as a “presentation” of $\mathcal{E}_p$ via the reflector $\mathsf{L}^p: \widehat{\mathcal{E}}_p \to \mathcal{E}_p$, and that the interpretation of MATT respects this “quotient”. For instance, the anodyne context morphisms (Definition 5.14) in $\widehat{\mathcal{E}}_p$ are precisely those that are inverted by $\mathsf{L}^p$; thus MATT is “unable to distinguish” contexts that present the same object of $\mathcal{E}_p$. One way to make this more precise is using Quillen model categories.

We end by discussing some examples of simple classes of diagrams in $\mathcal{T}$opos, to explore the flexibility and the limits of Theorems 6.3 and 6.5. As we will see, in some cases extra left adjoints already exist, so that co-dextrification is not necessary; but even in this case, some coherence results like those of section 5 are often still needed (see Remark 5.3). Table 1 summarizes some of the following examples, along with whether left adjoints already exist, and pointers to related theories in the literature.

**Example 6.7** If $\mathcal{L}$ consists of two objects $p, q$ and one nonidentity morphism $\mu: p \to q$, then a functor $\mathcal{L}^{\mathrm{coop}} \to \mathcal{T}$opos is a single geometric morphism. The resulting instance of MATT has two modes related by an adjoint pair of modalities $\mu \boxminus_{\blacksquare}$ and $\mu \diamondsuit_{\blacksquare}$. It is related to the split-context theory AdjTT of [43], and can be interpreted in any geometric morphism.

In particular, there is a unique geometric morphism from any topos $\mathcal{E}$ to **Set**. The resulting instance of MATT combines the usual internal language of $\mathcal{E}$ at one mode with the classical world of **Set** at another

$^3$ This is an $\infty$-topos without any 1-categorical analogue, so it is not covered by the semantic results in this paper.