4.2. BASIC CONSTRUCTIONS

4.2.1.36. Let $n > 0$ be an integer. An $(\infty, n)$-category is a $\mathrm{W}_n$-local $\infty$-presheaf $C \in \mathrm{Psh}^\infty(\Theta_n)$. We then define

$$
(\infty, n)\text{-cat} := \mathrm{Psh}^\infty(\Theta_n)_{\mathrm{W}_n}.
$$

Remark that the $(\infty, 1)$-category $(\infty, 0)$-cat is equivalent to $\infty$-grd. Proposition 4.2.1.35 implies that $(\infty, n)$-cat identifies itself with the full sub $(\infty, 1)$-category of $\mathrm{Psh}^\infty(\Delta[\Theta_{n-1}])$ of $\mathrm{M}_n$-local objects:

$$
(\infty, n)\text{-cat} \sim \mathrm{Psh}^\infty(\Delta[\Theta_{n-1}])_{\mathrm{M}_n}.
$$

The inclusion $i_n : \Theta_n \to \Theta$ fits in an adjunction

$$
\tau_n^i : \Theta \xrightarrow{\perp} \Theta_n : i_n
$$

where the left adjoint sends $\mathbf{D}_k$ on $\mathbf{D}_{\min(n,k)}$. By extension by colimits, this induces an adjoint pair

$$
\tau_n^i : \mathrm{Psh}^\infty(\Theta) \xrightarrow{\perp} \mathrm{Psh}^\infty(\Theta_n) : i_n. \tag{4.2.1.37}
$$

where the two functors are colimit preserving. As the image of every morphism of $\mathrm{W}$ by $\tau_n^i$ is in $\mathrm{W}_n$ or is an equivalence, and as the image of $\mathrm{W}_n$ by $i_n$ is included in $\mathrm{W}$, the previous adjunction induces by localization an adjunction

$$
\tau_n^i : (\infty, \omega)\text{-cat} \xrightarrow{\perp} (\infty, n)\text{-cat} : i_n \tag{4.2.1.38}
$$

where the two adjoints are colimit preserving. The left adjoint is called the *intelligent n-truncation*.

**Proposition 4.2.1.39.** *The functor $i_n : (\infty, n)\text{-cat} \to (\infty, \omega)\text{-cat}$ is fully faithful.*

*Proof.* We have to check that the unit of the adjunction (4.2.1.38) is an equivalence. As the two functors preserve colimits, we have to show that the restriction to $\Theta$ of the unit is an equivalence which is obvious. $\square$

Being colimit preserving, the functor $i_n$ is also part of an adjunction

$$
i_n : (\infty, n)\text{-cat} \xrightarrow{\perp} (\infty, \omega)\text{-cat} : \tau_n \tag{4.2.1.40}
$$

The right adjoint is called the *n-truncation*.

We will identify objects of $(\infty, n)$-cat with their image in $(\infty, \omega)$-cat and we will then also note by $\tau_n$ and $\tau_n^i$ the composites $i_n\tau_n^i$ and $i_n\tau_n^i$.

**Proposition 4.2.1.41.** *The functor $\tau_n : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}$ preserves special colimits.*

193