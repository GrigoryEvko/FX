CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**6.2.3.9.** Let $A$ be a $\mathbf{U}$-small $(\infty, \omega)$-category and $I$ a $\mathbf{U}$-small marked $(\infty, \omega)$-category. Recall that $\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$ is equivalent to $\underline{\mathrm{Hom}}_{\ominus}(I \times (A^t)^{\sharp}, \underline{\omega})$. Let $t$ be the canonical morphism $I \to 1$. As $t$ is smooth, corollary 6.2.2.7 induces adjunctions

$$\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A}) \xleftarrow{(t \times id_A)_*} \xrightarrow{(t \times id_A)_*} \widehat{A} \tag{6.2.3.10}$$

and $\widehat{A}$ is then lax $\mathbf{U}$-complete and lax $\mathbf{U}$-cocomplete. For a morphism $g: I \to \widehat{A}^{\sharp}$ corresponding to an object $E$ of $\mathrm{LCart}^c(I \times (A^t)^{\sharp})$, we then have

$$\int_{A^t} \underset{I}{\mathrm{laxcolim}} \, g \sim \mathbf{L}(t \times id_{(A^t)^{\sharp}})_! E \quad \int_{A^t} \underset{I}{\mathrm{laxlim}} \, g \sim \mathbf{R}(t \times id_{(A^t)^{\sharp}})_* E \tag{6.2.3.11}$$

Let $i: B^{\sharp} \to A^{\sharp}$ be any morphism. The squares given in paragraph 6.1.4.4 induce the commutative squares

$$\begin{array}{ccc} \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A}) & \xrightarrow{\mathrm{laxcolim}_I} & \widehat{A} \xleftarrow{\mathrm{laxlim}_I} & \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A}) \\ (id_I \times i^t)^* & \downarrow & \downarrow i^* & \downarrow (id_I \times i^t)^* \\ \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{B}) & \xrightarrow{\mathrm{laxcolim}_I} & \widehat{B} \xleftarrow{\mathrm{laxlim}_I} & \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{B}) \end{array}$$

In particular, choosing $B := 1$, this implies that the lax colimits and limits in $(\infty, \omega)$-presheaves commute with evaluation.

The next proposition implies that limits and colimits in $(\infty, \omega)$-presheaves can be detected as the level of the sub maximal $(\infty, 1)$-categories of $\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$ and $\widehat{A}$. We recall that the sub maximal $(\infty, 1)$-categories of $\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$, denoted by $\tau_1 \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$, is the adjoint of the functor $[n] \mapsto I \otimes [n]^{\sharp}$.

**Proposition 6.2.3.12.** *Let $I$ be a $\mathbf{U}$-small marked $(\infty, \omega)$-category, and $g: I \to A^{\sharp}$ a functor. An object $f$ of $\widehat{A}$ has a structure of colimit of the functor $g$ if and only if there exists an equivalence*

$$\mathrm{Hom}_{\tau_1 \widehat{A}}(f, h) \sim \mathrm{Hom}_{\tau_1 \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})}(F, \mathrm{cst} \, h)$$

*natural in $h: (\tau^1 \widehat{A})^{op}$. Similarly, the object $f$ has a structure of limit of the functor $F$ if and only if there exists an equivalence*

$$\mathrm{Hom}_{\tau_1 \widehat{A}}(h, f) \sim \mathrm{Hom}_{\tau_1 \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})}(\mathrm{cst} \, h, F)$$

*natural in $h: (\tau^1 \widehat{A})^{op}$.*

352