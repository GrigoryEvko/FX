6.1. UNIVALENCE

6.1.3.12. We set $\operatorname{Fun}^c([n], \operatorname{LCart}(I))$ as the pullback

$$\begin{array}{c} \operatorname{Fun}^c([n], \operatorname{LCart}(I)) \longrightarrow \operatorname{Fun}([n], \operatorname{LCart}(I)) \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \prod_{k \leq n} \operatorname{LCart}(I^\sharp) \longrightarrow \prod_{k \leq n} \operatorname{Fun}(\{k\}, \operatorname{LCart}(I)) \end{array}$$

where $I^\sharp$ stand for $(I^\sharp)^\sharp$. An object of this $(\infty, 1)$-category is then a sequence in $\operatorname{LCart}(I)$:

$$F_0 \longrightarrow \dots \longrightarrow F_n$$

such that for any integer $i \leq n$, $F_i$ is classified. A 1-cell of this $(\infty, 1)$-category is a sequence of square in $\operatorname{LCart}(I)$:

$$\begin{array}{c} F_0 \longrightarrow \dots \longrightarrow F_n \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ G_0 \longrightarrow \dots \longrightarrow G_n \end{array}$$

such that for any $k \leq n$, the morphism $F_k \to G_k$ comes from a morphism between the corresponding objects of $\operatorname{LCart}(I^\sharp)$.

**Proposition 6.1.3.13.** *Let $F: I \to (\infty, \omega)$-cat$_m$ be a **W**-small diagram. The canonical functor*

$$\operatorname{Fun}^c([n], \operatorname{LCart}(\underset{I}{\operatorname{colim}} F)) \to \lim_I \operatorname{Fun}^c([n], \operatorname{LCart}(F))$$

*is an equivalence.*

*Proof.* This morphism fits in an adjunction:

$$\operatorname{colim}_I: \lim_I \operatorname{Fun}^c([n], \operatorname{LCart}(F)) \xleftrightarrow[\perp]{\perp} \operatorname{Fun}^c([n], \operatorname{LCart}(\operatorname{colim}_I F))$$

The corollary 5.2.2.13 implies that the counit of this adjunction is an equivalence. To conclude, we have to show that the right adjoint is essentially surjective. On objects, this adjunction corresponds to the canonical equivalence

$$\lim_I \operatorname{Hom}([n], \operatorname{LCart}^c(F)) \sim \operatorname{Hom}([n], \operatorname{LCart}^c(\underset{I}{\operatorname{colim}} F))$$

induced by corollary 6.1.2.16

6.1.3.14. As $\mathbf{R}\mathring{\partial}_{0,I}$ is the identity, lemma 6.1.3.6 implies that the functor

$$\operatorname{LCart}((I \otimes [n]^\sharp)^\sharp) \to \operatorname{LCart}(I \otimes [n]^\sharp) \xrightarrow{\mathbf{R}\mathring{\partial}_{n,I}} \operatorname{Fun}([n], \operatorname{LCart}(I))$$

factors through a functor

$$\mathring{\partial}_{n,I}^c: \operatorname{LCart}((I \otimes [n]^\sharp)^\sharp) \to \operatorname{Fun}^c([n], \operatorname{LCart}(I)) \tag{6.1.3.15}$$

We are now willing to show that this functor is an equivalence, and to this extent, we will construct an inverse.

323