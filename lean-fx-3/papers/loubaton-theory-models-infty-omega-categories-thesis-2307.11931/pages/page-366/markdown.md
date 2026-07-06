CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

**Proposition 6.2.3.17.** *Consider a functor $F : I \to A^{\sharp}$ between $\mathbf{U}$-small marked $(\infty, \omega)$-categories. Then $F$ admits a lax limit if and only if there exists an object $l$ and an equivalence*

$$
\hom_A(a, l) \sim \underset{I}{\text{laxlim}} \hom_A(a, F(i))
$$

*natural in $a : A^t$. If such an object exists, then $l$ is the lax limit of $F$. Dually, $F$ admits a lax colimit if and only if there exists an object $c$ and an equivalence*

$$
\hom_A(c, a) \sim \underset{I}{\text{laxlim}} \hom_A(F(i), a)
$$

*natural in $a : A$. If such an object exists, then $c$ is the lax colimit of $F$.*

*Proof.* The first assertion is a direct application of lemma 6.2.3.16. The second one follows by duality, using the fact that the functor

$$
(\_)^\circ : \underline{\omega} \to \underline{\omega}^{t^\circ}
$$

preserves limits as it is an equivalence. $\square$

**Corollary 6.2.3.18.** *Left adjoints between $\mathbf{U}$-small $(\infty, \omega)$-categories preserve colimits and right adjoints preserve limits.*

*Proof.* Let $u : C \to D$ and $v : D \to C$ be two adjoint functors. Let $F : I \to C^{\sharp}$ be a functor admitting a colimit. We then have a sequence of equivalences

$$
\begin{array}{rcl}
\hom_C(u(\text{laxcolim}_I F), b) & \sim & \hom_D(\text{laxcolim}_I F, v(b)) \\
& \sim & \text{laxlim}_I \hom_D(F, v(b)) \quad (6.2.3.17) \\
& \sim & \text{laxlim}_I \hom_C(u(F), b) \\
& \sim & \hom_C(\text{laxlim}_I u(F), b) \quad (6.2.3.17)
\end{array}
$$

natural in $b : D$. The result then follows from the Yoneda lemma applied to $C^t$. The other assertion is proved similarly. $\square$

**Corollary 6.2.3.19.** *Consider a functor $F : I \to A^{\sharp}$ between $\mathbf{U}$-small marked $(\infty, \omega)$-categories. Then $F$ admits a limit if and only if there exists an object $l$ and an equivalence*

$$
\hom_A(a, l) \sim \hom_{\underline{\operatorname{Hom}}_\square(I, \underline{\omega})}(\text{cst } 1, \hom_A(a, F(\_)))
$$

*natural in $a : A^t$. If such an object exists, then $l$ is a limit of $F$. Dually, $F$ admits a colimit if and only if there exists an object $c$ and an equivalence*

$$
\hom_A(c, a) \sim \hom_{\underline{\operatorname{Hom}}_\square(I, \underline{\omega})}(\text{cst } 1, \hom_A(F(\_), a))
$$

*natural in $a : A$. If such an object exists, then $c$ is the colimit of $F$.*

356