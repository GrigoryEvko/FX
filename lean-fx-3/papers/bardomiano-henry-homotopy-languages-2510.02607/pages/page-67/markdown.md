This shows that the map is surjective.

As an immediate consequence of theorem 4.15, we can establish the $4^{th}$ invariance theorem in the special case where $F : \mathcal{M} \to \mathcal{N}$ is a Barton trivial fibration. We will use this result to be able to establish $4^{th}$ invariance theorem for the general case later on.

**Theorem 4.16.** *Let $F : \mathcal{M} \to \mathcal{N}$ be a Barton trivial fibration between weak model categories. Then for any cofibrant $\Gamma \in \mathcal{M}$ the induced map $h\mathbb{L}F_A : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \to h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$ is an isomorphism.*

*Proof.* By the previous theorem 4.8 we know that $h\mathbb{L}F_\Gamma : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \to h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$ is injective. Next we can use theorem 4.15 by observing that this surjectivity also descends to the level of $h\mathbb{L}F_\Gamma : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \to h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$. $\square$

Since our next goal is to prove $4^{th}$ invariance theorem, with theorem 4.16 at hand, we simply need to reduce our problem to the case in which we have Barton trivial fibrations. The constructions to come are essentially the necessary steps for this reduction process.

### 4.3 Path objects for weak model categories

The next step is to build some sort of “path object” for (weak) model category so that we can emulate Brown Factorization lemma to factor a general Quillen equivalence into a retract of a Barton trivial fibration followed by a Barton fibration. Ideally, we would want for a model category $\mathcal{M}$, we would like to build a diagram of left Quillen functors

$$\mathcal{M} \to P\mathcal{M} \to \mathcal{M} \times \mathcal{M}$$

where the maps $P\mathcal{M} \to \mathcal{M}$ are Barton trivial fibrations, and then try to use it to follow the proof of Brown’s Factorization Lemma. Unfortunately, that is not going to be quite possible: we will not be able to construct a map $\mathcal{M} \to P\mathcal{M}$. Instead, similarly to the proof of the $3^{rd}$ invariance theorem, we will construct, a diagram of the form

$$\begin{array}{ccc} R\mathcal{M} & \longrightarrow & P\mathcal{M} \\ \downarrow^p & & \downarrow \\ \mathcal{M} & \longrightarrow & \mathcal{M} \times \mathcal{M} \end{array}$$

where the arrow $p$ is a Barton trivial fibration. This will turn out to be sufficient to build our desired Brown style factorization. The weak model

67