Relative Elegance and Cartesian Cubes with One Connection

33

has recently proposed a type theory which directly represents $\sqrt{-}$ as a modality. The following definition and proposition constitute Theorem 5.2 of [LOPS18].

Definition 4.30 Define $p_{\mathrm{fib}}: \widetilde{U}_{\mathrm{fib}} \to U_{\mathrm{fib}}$ by pullback as follows:

$$\begin{array}{c} \widetilde{U}_{\mathrm{fib}} \xrightarrow{\pi_1} \widetilde{U} \\ p_{\mathrm{fib}} \downarrow \quad \downarrow p_U \\ U_{\mathrm{fib}} \xrightarrow{\pi_1} U \\ \pi_0 \downarrow \quad \downarrow (\mathrm{Fib\,id}_U)^\dagger \\ \sqrt[3]{\widetilde{U}} \xrightarrow[\sqrt[3]{p_U}]{\mathcal{J} \cdot \mathcal{U}}. \end{array}$$

Proposition 4.31 (LOPS18, Theorem 5.2) If $f: Y \to X$ is the pullback of $p_U$ along some $A: X \to U$, then $f$ is a uniform fibration if and only if $A$ factors through $\pi_1: U_{\mathrm{fib}} \to U$.

Corollary 4.32 The map $p_{\mathrm{fib}}$ is a uniform fibration.

Proof $p_{\mathrm{fib}}$ is the pullback of $p_U$ along $\pi_1$, which of course factors through itself.

Finally, we need a fibrancy structure on the universe $U$ itself. This is the most technically involved argument; we defer to prior work.

Proposition 4.33 The object $U_{\mathrm{fib}}$ is uniform fibrant.

Proof A fibrancy structure on $U_{\mathrm{fib}}$ is described in type-theoretic language in [ABCHFL21, §2.12], while Awodey [Awo23, §8] gives an external categorical construction.

Theorem 4.34 (Cubical-type model structure on semilattice cubical sets) There is a model structure on $\mathrm{PSh}_\kappa(\square_\nu)$ in which

- the cofibrations are the monomorphisms;
- the fibrations are those maps with the right lifting property against all pushout products $\delta_k \times m$ of an endpoint inclusion with a monomorphism.

We write $\widehat{\square}_\nu^{\mathrm{ty}}$ for this model category.

Proof By Corollary 3.33 applied with $\mathrm{PSh}_\kappa(\square_\nu)$ inside $\mathrm{PSh}(\square_\nu)$ and the factorization systems $(\mathcal{M}, \mathcal{F}_t)$ and $(C_t, \mathcal{F})$ defined in this section. Clearly all objects are cofibrant, and every fibration in $\mathrm{PSh}_\kappa(\square_\nu)$ is classified by $p_{\mathrm{fib}}: \widetilde{U}_{\mathrm{fib}} \to U_{\mathrm{fib}}$, which is a fibration (Corollary 4.32) between fibrant objects (Proposition 4.33).

Our question now is whether $\widehat{\square}_\nu^{\mathrm{ty}}$ presents $\infty$-Gpd. More narrowly, we can ask whether the following comparison adjunction evinces a Quillen equivalence between $\widehat{\square}_\nu^{\mathrm{ty}}$ and $\widehat{\Delta}^{\mathrm{kq}}$.

2025/10/16 00:43