6.1. UNIVALENCE

Proof. As equivalences between left fibrations and between left cartesian fibrations are detected on fibers, and as the two functors are natural in $C$, it is sufficient to show the result for $C$ being the terminal $(\infty, \omega)$-category. In this case remark that $\mathrm{LFib}(\mathrm{N}_{(\omega,1)} 1) \sim \mathrm{LCart}(1)$ and that both $\int_1$ and $\partial_1$ are the identities. $\square$

Corollary 6.1.2.16. Let $F : I \to (\infty, \omega)$-cat$_\mathrm{m}$ be a $\mathbf{W}$-small diagram. The canonical functor

$$\mathrm{LCart}^c(\underset{I}{\operatorname{colim}} F) \to \lim_{I} \mathrm{LCart}^c(F)$$

is an equivalence.

Proof. This functor fits in an adjunction:

$$\operatorname{colim}_I : \lim_I \mathrm{LCart}^c(F) \xrightarrow{\perp} \mathrm{LCart}^c(\operatorname{colim}_I F)$$

The corollary 5.2.2.13 implies that the counit of this adjunction is an equivalence. To conclude, we have to show that the right adjoint is essentially surjective. By definition, the morphism $\tau_0 \mathrm{LCart}(I^\sharp) \to \tau_0 \mathrm{LCart}^c(I)$ is an equivalence. According to theorem 6.1.2.15, on the $\infty$-groupoid of objects, the right adjoint corresponds to the equivalence

$$\tau_0 \mathrm{LFib}(\mathrm{N}_{(\omega,1)} \underset{I}{\operatorname{colim}} F^\sharp) \to \lim_{I} \tau_0 \mathrm{LFib}(\mathrm{N}_{(\omega,1)} F^\sharp)$$

given in proposition 6.1.1.14. $\square$

Corollary 6.1.2.17. Let $C$ be an $(\infty, \omega)$-category and $c$ be an object of $c$. The left fibration $\partial_C \mathbf{F} h_c$ is the morphism of simplicial objects:

$$\begin{array}{ccc} \cdots & \coprod_{x_0, x_1, x_2: C_0} \hom_C(y, x_0, x_1, x_2) \xrightarrow{\longleftrightarrow} \coprod_{x_0, x_1: C_0} \hom_C(y, x_0, x_1) \xrightarrow{\longleftrightarrow} \coprod_{x_0: C_0} \hom_C(y, x_0) \\ & \downarrow & \downarrow \\ \cdots & \coprod_{x_0, x_1, x_2: C_0} \hom_C(x_0, x_1, x_2) \xrightarrow{\longleftrightarrow} \coprod_{x_0, x_1: C_0} \hom_C(x_0, x_1) \xrightarrow{\longleftrightarrow} \coprod_{x_0: C_0} 1 \end{array}$$

Proof. We denote by $E := X \to \mathrm{N}_{(\omega,1)} C$ this left fibration. According to theorem 6.1.2.15, we can equivalently show that the Grothendieck integral of $E$ is the morphism $C_{c/}^\sharp \to C$. Remark that we have by construction a family of cartesian squares

$$\begin{array}{ccc} X_n \times_{(\mathrm{N}_{(\omega,1)} C)_n} (C_{/})_n & \longrightarrow & (C^\sharp)^{[1+n+1]\sharp} \xrightarrow{(C^\sharp)^{hn}} (C^\sharp)^{[1]\sharp} \\ \downarrow & \downarrow & \downarrow \\ \{c\} \times (\mathrm{N}_{(\omega,1)} C)_n \times C^\sharp & \longrightarrow & C^\sharp \times (C^\sharp)^{[n]\sharp} \times C^\sharp \longrightarrow C^\sharp \times C^\sharp \end{array}$$

317