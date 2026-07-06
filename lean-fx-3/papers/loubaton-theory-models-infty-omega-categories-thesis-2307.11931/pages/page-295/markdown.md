5.2. CARTESIAN FIBRATIONS

5.2.4.10. We denote by $\perp : (\infty, \omega)\text{-cat}_{\mathrm{m}} \to (\infty, \omega)\text{-cat}$ the left Kan extension of the functor $t\Theta \to (\infty, \omega)\text{-cat}$ that sends $a^{\flat}$ on $a$ and $(\mathbf{D}_{n+1})_t$ on $\mathbf{D}_n$. Roughly speaking, $\perp$ sends a marked $(\infty, \omega)\text{-category}$ to it's localization by marked cells. By abuse of notation, we also denote $\perp : \operatorname{Arr}((\infty, \omega)\text{-cat}_{\mathrm{m}}) \to (\infty, \omega)\text{-cat}$, the composite functor

$$
\operatorname{Arr}((\infty, \omega)\text{-cat}_{\mathrm{m}}) \xrightarrow{\mathrm{dom}} (\infty, \omega)\text{-cat}_{\mathrm{m}} \xrightarrow{\perp} (\infty, \omega)\text{-cat}
$$

This functor preserves colimits and sends initial and final morphisms to equivalences. For any object $E$ of $\operatorname{LCart}(A)$ and for any morphism $i: A \to B$, we then have a canonical equivalence

$$
\perp \mathbf{L} i_{!} E \sim \perp E. \tag{5.2.4.11}
$$

Let $A$ be an $(\infty, \omega)$-category and $a: 1 \to A^{\sharp}$ an object of $A$. According to proposition 5.2.1.19, the factorisation of $a: 1 \to A^{\sharp}$ in a final morphism followed by a right cartesian fibration is given by the canonical inclusion $\{a\} \to A_{a/}^{\sharp}$ and the canonical projection $\pi_a: A_{a/}^{\sharp} \to A^{\sharp}$. Let $E$ be an object of $\operatorname{LCart}(A^{\sharp})$ corresponding to a left cartesian fibration $p: X \to A^{\sharp}$. We then have a diagram

$$
\begin{array}{ccc}
X_a & \xrightarrow{i} & X_{/a} & \longrightarrow & X \\
\downarrow & \downarrow & \downarrow & \downarrow & \downarrow_p \\
\{a\} & \longrightarrow & A_{a/}^{\sharp} & \xrightarrow{\pi_a} & A^{\sharp}
\end{array}
$$

and the morphism $i$ is final as $p$ is proper. As $\perp$ sends final morphisms to equivalences, we then have an invertible natural transformation:

$$
\mathbf{R} a^* E \sim \perp \mathbf{R} a^* E \sim \perp \mathbf{R} \pi_a^* E \tag{5.2.4.12}
$$

**Proposition 5.2.4.13.** *The functor $\mathbf{R} a^*: \operatorname{LCart}(A^{\sharp}) \to \operatorname{LCart}(1) \sim (\infty, \omega)\text{-cat preserves colimits}$.*

*Proof.* As $\pi_a$ is a right cartesian fibration, it is smooth and $\mathbf{R} \pi_a^*$ then preserves colimits. The functor $\perp$ also preserves them. The result then follows from the equivalence (5.2.4.12).

5.2.4.14. Let $E$ be an object of $(\infty, \omega)\text{-cat}_{\mathrm{m}/A^{\sharp}}$ corresponding to a morphism $X \to A^{\sharp}$. We denote $\tilde{X} \to A^{\sharp}$ the left fibrant replacement of $E$. We then have a diagram

$$
\begin{array}{ccc}
X_{a/} & \longrightarrow & \tilde{X}_{a/} & \longrightarrow & A_{a/}^{\sharp} \\
\downarrow & \downarrow & \downarrow & \downarrow & \downarrow_{\pi_a} \\
X & \longrightarrow & \tilde{X} & \xrightarrow{\mathbf{F}E} & A^{\sharp}
\end{array}
$$

285