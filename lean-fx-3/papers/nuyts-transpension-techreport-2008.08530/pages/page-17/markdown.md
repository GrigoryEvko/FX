This quotient theorem applies to examples 3.3.1, 3.3.3, 3.3.8 and 3.3.9. However, we can extend the quotient theorem to also consider multipliers that are not $\top$-slice objectwise pointable theorem 3.4.10, and then it will apply to more examples.

We will use the quotient theorem in theorem 4.4.7 on transpension elimination, a dependent eliminator for the transpension type from which we can build a dependent eliminator for BCM's $\Psi$-type and prove BCM's $\Phi$-rule [Mou16, BCM15].

### 3.4.3 Dealing with unpointability

Since multipliers that are not $\top$-slice objectwise pointable, do not guarantee that $\nexists_U$ produces split epi slice objects, we need to come up with a larger class of suitable epi-like morphisms to $U$ before we can proceed.

**Definition 3.4.6.** Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$, we say that a morphism $\varphi : V \to U$ is **dimensionally split** if there is some $W \in \mathcal{W}$ such that $\pi_2 : W \ltimes U \to U$ factors over $\varphi$. The other factor $\chi$ such that $\pi_2 = \varphi \circ \chi$ will be called a **dimensional section** of $\varphi$. We write $\mathcal{V} // U$ for the full subcategory of $\mathcal{V} / U$ of dimensionally split slice objects.

The $\top$-slice objectwise pointability condition for multipliers is automatically satisfied if we replace 'split epi' with 'dimensionally split':

**Corollary 3.4.7.** For any multiplier $\sqcup \ltimes U$, any projection $\pi_2 : W \ltimes U \to U$ is dimensionally split. $\square$

**Proposition 3.4.8.** Take a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$.

1. If $\varphi \circ \chi$ is dimensionally split, then so is $\varphi$.
2. The identity morphism $\text{id}_U : U \to U$ is dimensionally split.
3. If $\varphi : V \to U$ is dimensionally split and $\chi : V' \to V$ is split epi, then $\varphi \circ \chi : V' \to U$ is dimensionally split.
4. Every split epimorphism to $U$ is dimensionally split.
5. If $\sqcup \ltimes U$ is $\top$-slice objectwise pointable, then every dimensionally split morphism is split epi.

*Proof.* 1. If $\pi_2 : W \ltimes U \to U$ factors over $\varphi \circ \chi$, then it certainly factors over $\varphi$.

2. Since $\pi_2 : \top \ltimes U \to U$ factors over $\text{id}_U$.
3. Let $\varphi'$ be a dimensional section of $\varphi$ and $\chi'$ a section of $\chi$. Then $\chi' \circ \varphi'$ is a dimensional section of $\varphi \circ \chi$.
4. From the previous two points, or (essentially by composition of the above reasoning) because if $\chi : U \to V$ is a section of $\varphi : V \to U$, then $\chi \circ \pi_2 : \top \ltimes U \to V$ is a dimensional section of $\varphi$.
5. If $\varphi : V \to U$ is dimensionally split, then some $\pi_2 : W \ltimes U \to U$ factors over $\varphi$. Since $\pi_2$ is split epi, $\text{id}_U$ factors over $\pi_2$ and hence over $\varphi$, i.e. $\varphi$ is split epi. $\square$

We can now extend the notions of shard and shard-freedom to multipliers that are not $\top$-slice objectwise pointable without changing their meaning for those that are:

**Definition 3.4.9.** We say that a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice **shard-free** if $\nexists_U$ is essentially surjective on $\mathcal{V} // U$, the full subcategory of $\mathcal{V} / U$ of dimensionally split slice objects. A dimensionally split slice object $(V, \psi)$ that is not in the image of $\nexists_U$ even up to isomorphism, will be called a **shard** of the multiplier.

Note that a multiplier is $\top$-slice shard-free if every dimensionally split slice object has an *invertible* dimensional section.

17