CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**6.1.2.20.** A left cartesian fibration is **U**-small if its fibers are **U**-small $(\infty, \omega)$-categories. For an $(\infty, \omega)$-category $A$, we denote by $\mathrm{LCart}_{\mathbf{U}}(A^{\sharp})$ the full sub $(\infty, 1)$-category of $\mathrm{LCart}(A^{\sharp})$ whose objects correspond to **U**-small left cartesian fibrations over $A^{\sharp}$.

**Corollary 6.1.2.21.** *Let $\underline{\omega}$ be the **V**-small $(\infty, \omega)$-category of **U**-small $(\infty, \omega)$-categories and $A$ a **V**-small $(\infty, \omega)$-category. There is an equivalence*

$$\int_A : \mathrm{Hom}(A, \underline{\omega}) \to \tau_0 \mathrm{LCart}_{\mathbf{U}}(A^{\sharp})$$

*natural in $A : (\infty, \omega)$-cat$^{op}$.*

*Proof.* This is a direct consequence of the theorem 6.1.2.15 and the definition of $\underline{\omega}$. $\square$

**Corollary 6.1.2.22.** *The left cartesian fibration $\int_{\underline{\omega}} id$ is the universal left cartesian fibration with **U**-small fibers, i.e for any left cartesian fibration $X \to A^{\sharp}$ with **U**-small fibers, there exists a unique morphism $X \to \underline{\omega}$ and a unique cartesian square:*

$$\begin{array}{ccc} X & \longrightarrow & \mathrm{dom} \int_{\underline{\omega}} id \\ \downarrow & & \downarrow \int_{\underline{\omega}} id \\ A^{\sharp} & \longrightarrow & \underline{\omega}^{\sharp} \end{array}$$

*Proof.* This is a direct consequence of the corollary 6.1.2.21 and the functoriality of the Grothendieck construction given in proposition 6.1.2.14. $\square$

### 6.1.3 Univalence

**Notation.** Through this section, we will identify any marked $(\infty, \omega)$-category $C$ with the canonical induced morphism $C \to 1$. If $f : X \to Y$ is a morphism, $f \times C$ then corresponds to the canonical morphism $X \times C \to Y$.

**6.1.3.1.** For the remaining of this section, we fix a marked $(\infty, \omega)$-category $I$. Remark that $\mathbf{F}h_k^{[n]}$ corresponds to the inclusion $(d_0^{\sharp})^k : [n - k]^{\sharp} \to [n]^{\sharp}$. We define the functor

$$\oint_{n,I} : \mathrm{Fun}([n], (\infty, \omega)\text{-cat}_{\mathrm{m}/I}) \to (\infty, \omega)\text{-cat}_{\mathrm{m}/I \otimes [n]^{\sharp}}$$

whose value on a morphism $E : [n] \to (\infty, \omega)\text{-cat}_{\mathrm{m}/I}$ corresponding to a sequence $E_0 \to \dots \to E_n$, is

$$\oint_{n,I} E := \underset{m}{\mathrm{colim}} \coprod_{i_0 \le \dots \le i_m \le n} E_{i_0} \otimes \mathbf{F}h_{i_m}^{[n]}.$$

As this functor is colimit preserving, it induces an adjunction

$$\oint_{n,I} : \mathrm{Fun}([n], (\infty, \omega)\text{-cat}_{\mathrm{m}/I}) \xrightarrow{\perp} (\infty, \omega)\text{-cat}_{\mathrm{m}/I \otimes [n]^{\sharp}} : \mathring{\partial}_{n,I} \tag{6.1.3.2}$$

320