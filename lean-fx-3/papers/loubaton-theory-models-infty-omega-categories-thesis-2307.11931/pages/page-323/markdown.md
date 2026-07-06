6.1. UNIVALENCE

By currying, we see these objects as functors $t\Theta^{op} \to \mathrm{Psh}^{\infty}(\Delta)$. The right vertical morphism is then pointwise a right fibration of $(\infty, 1)$-categories fibered in $\infty$-groupoids, as it corresponds, for a fixed $a : t\Theta$ and $n : \Delta$, to the morphism of $\infty$-groupoid:

$$\coprod_{x_0, \dots, x_n : C_0} \mathrm{Hom}(a, \mathrm{hom}_C(x_0, \dots, x_n)^\flat) \times \mathrm{Hom}(a, C_{x_n}^\sharp) \to \coprod_{x_0, \dots, x_n : C_0} \mathrm{Hom}(a, \mathrm{hom}_C(x_0, \dots, x_n)^\flat).$$

As the morphism $f$ is pointwise initial, so is $g$. As $\beta$ sends pointwise initial morphisms to equivalence, this implies that $\beta\alpha(f) := \beta(g)$ is an equivalence.

Suppose now given two cartesian squares

$$\begin{array}{c} X \xrightarrow{g} X' \xrightarrow{\quad} C_./ \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ \langle a, 0 \rangle \xrightarrow{\langle f, 0 \rangle} \langle b, 0 \rangle \longrightarrow (\mathrm{N}_{(\omega, 1)} C)^\flat \end{array}$$

with $f \in \mathrm{W}$. By currying, we see these objects as functors $\Delta \to \mathrm{Psh}^{\infty}(t\Theta)$. The right vertical morphism is then pointwise a right cartesian fibration. As the morphism $\langle f, 0 \rangle$ is pointwise in $\widehat{\mathrm{tW}}$, so is $g$. The morphism $\mathrm{colim}_n g_n$ is then in $\widehat{\mathrm{tW}}$ and $\beta\alpha(f) := \beta(g)$ is an equivalence.

### 6.1.2.7. We will denote also by

$$\int_C : \mathrm{LFib}(\mathrm{N}_{(\omega, 1)} C) \to \mathrm{LCart}(C^\sharp)$$

the restriction of the Grothendieck construction. This will not cause any confusion as from now on we will only consider the Grothendieck construction of left fibration. The lemma 6.1.2.6 then implies that this functor is colimit preserving, and it is then part of an adjunction

$$\int_C : \mathrm{LFib}(\mathrm{N}_{(\omega, 1)} C) \xrightarrow{\quad} \mathrm{LCart}(C^\sharp) : \partial_C \tag{6.1.2.8}$$

**Lemma 6.1.2.9.** Let $i : C^\sharp \to D^\sharp$ be a morphism. The natural transformation

$$\partial_C \circ \mathbf{R} i^* \to \mathbf{R}(\mathrm{N}_{(\omega, 1)} i)^* \circ \partial_D$$

is an equivalence.

Proof. As equivalences between left fibrations are detected on fibers, one can suppose that $C$ is the terminal $(\infty, \omega)$-category. Let $c$ denote the object of $D$ corresponding to $i$. Let $E$ be an object of $\mathrm{LFib}(\mathrm{N}_{(\omega, 1)} 1)$, corresponding to a morphism $A \to 1$. According to lemma 6.1.2.6, we then have equivalences

$$\begin{array}{l} \mathbf{L} i_! \int_1 E \sim \mathbf{L} i_! (A^\flat \times h_1^1) \\ \qquad \sim A^\flat \times \mathbf{F} h_c^D \\ =: \int_D \mathrm{N}_{(\omega, 1)} i_! E \\ \qquad \sim \int_D \mathbf{L}(\mathrm{N}_{(\omega, 1)} i)_! E \quad (6.1.2.6) \end{array}$$

313