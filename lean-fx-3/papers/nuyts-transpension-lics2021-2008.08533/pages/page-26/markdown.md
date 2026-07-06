16:26

A. NUYTS AND D. DEVRIESE

Vol. 20:2

6.2. **Pointability, dimensional splitness and boundaries.** Before we move on to a list of examples, we owe the reader a definition for dimensional splitness (although the impatient reader may first read the example Section 6.3, ignoring shard-freedom, pointability and boundaries). In most popular base categories, namely all the *objectwise pointable* ones, we could have gotten away with saying 'split epi' instead of 'dimensionally split' (Proposition 6.8).

**Definition 6.4.** Let $\mathcal{W}$ be a category with terminal object $\top$. An object $W$ is **pointable**$^{\S A}$ if $() : W \to \top$ is split epi, i.e. if there exists at least one morphism $\top \to W$. A category is **objectwise pointable**$^{\S A}$ if each object is pointable.

We have carefully chosen the above terminology to emphasize (1) that pointability is a property, not structure (the corresponding structure is called *pointed*), and (2) that objectwise pointability does *not* require that the pointings can be chosen naturally.

**Proposition 6.5.** *Let $\sqcup \ltimes U$ be a multiplier on an objectwise pointable category $\mathcal{W}$. Then for any object $W$, the slice object $\lhd_U W$ is split epi.*

*Proof.* Any functor preserves split epimorphisms. We have $\lhd_U W = (W \ltimes U, \pi_2)$ and $\pi_2 : W \ltimes U \to U \cong \top \ltimes U$ is essentially the image of $W \to \top$. $\square$

When dealing with a category that is not objectwise pointable, the above theorem does not hold and the definition of shard-freedom w.r.t. split epi slice objects would not make sense, so we need a somewhat more general notion:

**Definition 6.6.** Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$, we say that a morphism $\varphi : V \to U$ is **dimensionally split** if there is some $W \in \mathcal{W}$ such that $\pi_2 : W \ltimes U \to U$ factors over $\varphi$. The other factor $\chi : W \ltimes U \to V$ such that $\pi_2 = \varphi \circ \chi$ will be called a **(dimensional) section** of $\varphi$. We write $\mathcal{W} // U$ for the full subcategory of $\mathcal{W} / U$ of dimensionally split slice objects.

We define the **boundary** $\partial U$ as the subpresheaf of the Yoneda-embedding $\mathbf{y} U$ consisting of those morphisms that are *not* dimensionally split.

Thus, a multiplier is $\top$-slice shard-free if and only if every dimensionally split slice object has an invertible dimensional section.

**Proposition 6.7.** *Let $\sqcup \ltimes U$ be a multiplier on $\mathcal{W}$. Then for any object $W$, the slice object $\lhd_U W$ is dimensionally split with section $\operatorname{id}_{W \ltimes U}$.* $\square$

**Proposition 6.8.** *If $\mathcal{W}$ is objectwise pointable, then a morphism $\varphi : V \to U$ is split epi if and only if it is dimensionally split.* [Nuy20b]

The notion of dimensionally split morphisms lets us consider the boundary and shard-freedom (a requirement for modelling $\Phi$) also in base categories that are not objectwise pointable, where the output of $\lhd_U$ may not be split epi.

**Remark 6.9.** $\top$-slice shard-freedom can also be formulated using (co)sieves [nLa23d]. A **sieve in $\mathcal{W}$** is a full subcategory $\mathcal{S}$ such that if $W \in \mathcal{S}$ and $\varphi : V \to W$, then $V \in \mathcal{S}$. The dual (where $\varphi$ points the other way) is called a **cosieve in $\mathcal{W}$**. Being full subcategories, (co)sieves can be regarded as subsets of $\operatorname{Obj}(\mathcal{W})$. A **sieve on $U \in \mathcal{W}$** is a sieve in $\mathcal{W} / U$ or, equivalently, a subpresheaf of $\mathbf{y} U$.

A multiplier is $\top$-slice shard-free if either of the following equivalent criteria is satisfied:
- The objects in the essential image of $\lhd_U$ constitute a cosieve in $\mathcal{W} / U$ [Nuy23a].