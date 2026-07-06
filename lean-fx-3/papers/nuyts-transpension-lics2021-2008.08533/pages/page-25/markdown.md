Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:25

- **Copointed**$^{\S A}$ if it is equipped with a natural first projection $\pi_1 : (\sqcup \ltimes U) \to \text{Id}$.

*This property carries over to $\sqcup \ltimes \mathbf{y}U$ and thus allows for shape weakening.*

- A **comonad**$^{\S A}$ if it is additionally equipped with a natural diagonal $\delta : (\sqcup \ltimes U) \to ((\sqcup \ltimes U) \ltimes U)$ such that $\pi_1 \circ \delta = (\pi_1 \ltimes U) \circ \delta = 1_{(\sqcup \ltimes U)}$ and $\delta \circ \delta = (\delta \ltimes U) \circ \delta : (\sqcup \ltimes U) \to (\sqcup \ltimes U)^3$. *This property carries over to $\sqcup \ltimes \mathbf{y}U$ and thus allows for shape variable contraction.*

- **Cartesian** if it is naturally isomorphic to the cartesian product with $U$.

*This property carries over to $\sqcup \ltimes \mathbf{y}U$ and is thus a sufficient condition for allowing exchange. Additionally, it will erase the distinction between weakening $\Omega[u]$ (Section 6.4) and fresh shape weakening $\lrcorner[u]$ (Section 6.6), see Theorem 6.31.*

- $\top$-**slice faithful**$^{\S A}$ if $\lrcorner_U$ is faithful.

*This is a basic well-behavedness property that is satisfied by all examples of interest. Example 6.20 is a counterexample.*

- $\top$-**slice full**$^{\S A}$ if $\lrcorner_U$ is full.

*For multipliers for objects other than $\top$, this property precludes the exchange rule (Proposition 6.3). $\top$-slice fully faithful multipliers will give rise to fully faithful modalities for fresh weakening $\lrcorner[u]$ and transpension $\Diamond[u]$ (Theorem 6.31).*

- $\top$-**slice shard-free**$^{\S A}$ if $\lrcorner_U$ is essentially surjective on slice objects $(V, \psi)$ such that $\psi : V \to U$ is dimensionally split (Definition 6.6). A **shard**$^{\S A}$ is a slice object $(V, \psi)$ that is not up to isomorphism in the image of $\lrcorner_U$ even though $\psi$ is dimensionally split.

*Intuitively, a shard is a shape over $\mathbb{U}$ that covers all of $\mathbb{U}$ (as expressed by the fact that $\psi$ is dimensionally split, which just means split epi in most applications), but that is not prism-shaped in the direction of $\mathbb{U}$ (as it would then be in the image of $\lrcorner_U$). Shard-freedom will be a requirement for the $\Phi$-rule [Mou16] to hold (Theorem 10.1) and for elimination of the transpension type by pattern matching to be sound (Theorem 9.3).*

- $\top$-**slice right adjoint** if $\lrcorner_U$ has a left adjoint $\exists_U : \mathcal{W}/U \to \mathcal{W}$.$^{16}$

**Proposition 6.3.** *If a $\top$-slice full multiplier for $U$ is:*

- a *comonad*, then $U$ is terminal,
- *cartesian*, then it is naturally isomorphic to the identity functor.

*Proof.* The second statement clearly follows from the first, so we only prove the first. Consider the following diagram:

$$\top \ltimes U \xrightarrow{\delta} (\top \ltimes U) \ltimes U \tag{6.1}$$

It commutes, because $\pi_2 = \pi_2 \circ (\pi_1 \ltimes U) : (\top \ltimes U) \ltimes U \to U$ and $(\pi_1 \ltimes U) \circ \delta = 1$. So it is a morphism of slice objects $\delta : \lrcorner_U \top \to \lrcorner_U (\top \ltimes U)$ and thus, since $\lrcorner_U$ is full, of the form $\lrcorner_U v$ for some $v : \top \to \top \ltimes U$. This means in particular that

$$\text{id}_{\top \ltimes U} = \pi_1 \circ \delta = \pi_1 \circ (v \ltimes U) = v \circ \pi_1 : \top \ltimes U \to \top \ltimes U, \tag{6.2}$$

so the identity on $\top \ltimes U$ factors over $\top$. Then $\top \ltimes U \cong U$ is terminal.

$^{16}$A functor $\sqcup \ltimes U$ with this property is usually called a *parametric* or *local right adjoint*, but the word 'local' is overloaded [nLa23b] and so is 'parametric', and we wanted uniform terminology.