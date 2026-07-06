6.1. UNIVALENCE

According to proposition 6.1.1.5, we have equivalences

$$\mathrm{LFib}(\langle a, \mathrm{Sp}_n \rangle) \sim \lim_{[k] \to \mathrm{Sp}_n} \mathrm{Fun}([k], (\infty, \omega)\text{-cat}_{/a}) \sim \mathrm{Fun}([n], (\infty, \omega)\text{-cat}_{/a}) \sim \mathrm{LFib}(\langle a, n \rangle)$$

It remains the case $f := E^{eq} \to 1$. We have equivalences $\mathrm{N}_{(\omega,1)} E^{eq} \sim \langle [0], E^{eq} \rangle$ and $\mathrm{N}_{(\omega,1)} 1 \sim 1$. The proposition 6.1.1.5 induces equivalences

$$\mathrm{LFib}(\langle [0], E^{eq} \rangle) \sim \lim_{[k] \to E^{eq}} \mathrm{Fun}([k], (\infty, \omega)\text{-cat}) \sim \mathrm{Fun}(1, (\infty, \omega)\text{-cat})$$

which concludes the proof.

6.1.1.15. Let $A$ be an $(\infty, \omega, 1)$-category. An object $E : (\infty, \omega, 1)\text{-cat}_{/A}$ is **U-small** if for any morphism $i : \langle b, n \rangle \to A$, the space of morphism between $i$ and $E$ is **U-small**. Remark that an object $F$ of $\mathrm{LFib}(\mathrm{N}_{(\omega,1)} A)$ corresponding to a left fibration $X \to \mathrm{N}_{(\omega,1)} A$ is **U-small** if an only if for any object $a$ of $A$, $X(a)$ is **U-small**. Eventually, we define $\mathrm{LFib}_{\mathbf{U}}(A)$ as the full sub $(\infty, 1)$-category of $\mathrm{LFib}(A)$ whose objects correspond to **U-small** left fibrations. In particular, $\mathrm{LFib}_{\mathbf{U}}(A)$ is a **V-small** $(\infty, 1)$-category unlike $\mathrm{LFib}(A)$ which is a **W-small** $(\infty, 1)$-category. Moreover, the proposition 6.1.1.14 implies that the functor

$$C : (\infty, \omega)\text{-cat} \mapsto \tau_0 \mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} C)$$

sends colimits to limits. We then define $\underline{\omega}$ as the $(\infty, \omega)$-category that represents this object:

$$\begin{array}{rcl} \underline{\omega} : & \Theta^{op} & \to & \infty\text{-grd} \\ & a & \mapsto & \tau_0 \mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} a) \end{array} \tag{6.1.1.16}$$

We then have by definition an equivalence

$$\mathrm{Hom}(C, \underline{\omega}) \sim \tau_0 \mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} C). \tag{6.1.1.17}$$

As the functor $\mathrm{N}_{(\omega,1)}$ preserves product, for any $(\infty, \omega)$-category $D$, we also have a canonical equivalence

$$\mathrm{Hom}(C, \underline{\mathrm{Hom}}(D, \underline{\omega})) \sim \tau_0 (\mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} C \times \mathrm{N}_{(\omega,1)} D)). \tag{6.1.1.18}$$

Eventually, by construction, the $\infty$-groupoid of objects of $\underline{\omega}$ corresponds to the $\infty$-groupoid of **U-small** $(\infty, \omega)$-categories, and according to proposition 6.1.1.12, we have an equivalence

$$\mathrm{hom}_{\underline{\omega}}(C, D) \sim \underline{\mathrm{Hom}}(C, D). \tag{6.1.1.19}$$

The $(\infty, \omega)$-category $\underline{\omega}$ seems to be a decent candidate for the $(\infty, \omega)$-category of **U-small** $(\infty, \omega)$-categories.

309