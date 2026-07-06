6.2. YONEDA LEMMA AND APPLICATIONS

Proof. We recall that theorem 6.1.4.2 and corollary 6.1.4.3 induces equivalences

$$\tau_{1}\widehat{A}\sim\mathrm{LCart}_{\mathbf{U}}((A^{t})^{\sharp})\quad\tau_{1}\underline{\mathrm{Hom}}_{\ominus}(I,A)\sim\mathrm{LCart}_{\mathbf{U}}^{c}(I\otimes(A^{t})^{\sharp})$$

and that we have a triplet of adjoints

$$\mathrm{LCart}_{\mathbf{U}}^{c}(I\otimes(A^{t})^{\sharp})\xrightarrow[\leftarrow((\stackrel{\perp}{\times}(t\times id_{A^{t}}))^{*}\text{--}\mathrm{LCart}_{\mathbf{U}}((A^{t})^{\sharp})]{\underset{\perp}{\mathrm{L}}(t\times id_{A^{t}})_{*}\text{--}\mathrm{LCart}_{\mathbf{U}}((A^{t})^{\sharp})}$$

which is the image by $\tau_{1}$ of the triplet of adjoints (6.2.3.10). The first hypothesis induces an equivalence

$$\int_{A^{t}}f\sim\mathbf{L}(t\times id_{(A^{t})^{\sharp}})_{!}E$$

and the second one an equivalence

$$\int_{A^{t}}f\sim\mathbf{R}(t\times id_{(A^{t})^{\sharp}})_{*}E$$

where $E$ denote the object of $\mathrm{LCart}^{c}(I\times(A^{t})^{\sharp})$ corresponding to $g$. The assertions then follow from the equivalences (6.2.3.11).

Example 6.2.3.13. We recall that we denote by $\perp:\mathrm{Arr}((\infty,\omega)\text{-cat}_{\mathrm{m}})\to(\infty,\omega)\text{-cat}$ the functor sending a left fibration $Y\to A$ to the localization of $Y$ by marked cells. This functors sends initial and final morphisms to equivalences. If $E$ is a left cartesian fibration over a marked $(\infty,\omega)$-category $I$, we then have $\perp E\sim\mathbf{L}t_{!}E$ where $t$ denotes the morphism $I\to 1$.

Let $g:I\to\underline{\omega}$ be a diagram. We denote $\iota:I\to I^{\sharp}$ the canonical inclusion. By the explicit expression of lax colimit given above, we then have an equivalence

$$\operatorname*{laxcolim}_{I}g\sim\perp\iota^{*}\int_{I^{\sharp}}g^{\sharp}.$$

If $I$ is equivalent to $I^{\flat}$, we then have

$$\operatorname*{laxcolim}_{I}g\sim\mathrm{dom}(\int_{I^{\sharp}}g^{\sharp})^{\sharp}.$$

- Let $c:1\to\underline{\omega}$ be a morphism corresponding to an $(\infty,\omega)$-category $C$. For any $(\infty,\omega)$-category $A$, we then have

$$\operatorname*{laxcolim}_{A^{\sharp}}\mathrm{cst}_{c}\sim(\tau_{0}A)\times C\qquad\operatorname*{laxcolim}_{A^{\flat}}\mathrm{cst}_{c}\sim A\times C$$

- Let $f:[b,1]\to\underline{\omega}$ be a morphism corresponding to a morphism $A\times b\to B$. We then have

$$\operatorname*{laxcolim}_{[b,1]^{\flat}}f\sim A\times(1^{\text{co}}\star b)\coprod_{A\times b}B$$

353