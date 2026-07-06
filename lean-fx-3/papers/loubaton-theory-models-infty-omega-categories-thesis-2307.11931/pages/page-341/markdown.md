6.1. UNIVALENCE

**Theorem 6.1.4.2.** Let $I$ be a $\mathbf{U}$-small marked $(\infty, \omega)$-category. Let $\underline{\omega}$ be the $\mathbf{V}$-small $(\infty, \omega)$-category of $\mathbf{U}$-small $(\infty, \omega)$-categories, and $\underline{\mathrm{LCart}}_{\mathbf{U}}^{c}(I)$ the $\mathbf{V}$-small $(\infty, \omega)$-category of $\mathbf{U}$-small left cartesian fibrations. There is an equivalence

$$\underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \sim \underline{\mathrm{LCart}}_{\mathbf{U}}^{c}(I)$$

natural in $I$. On the maximal sub $\infty$-groupoid, this equivalence corresponds to the Grothendieck construction of theorem 6.1.2.15.

**Corollary 6.1.4.3.** Let $A$ be a $\mathbf{U}$-small $(\infty, \omega)$-category. Let $\underline{\mathrm{LCart}}_{\mathbf{U}}^{c}(A^{\sharp})$ be the $\mathbf{V}$-small $(\infty, \omega)$-category of $\mathbf{U}$-small left cartesian fibrations. There is an equivalence

$$\underline{\mathrm{Hom}}(A, \underline{\omega}) \sim \underline{\mathrm{LCart}}_{\mathbf{U}}(A^{\sharp})$$

natural in $A$. On the maximal sub $\infty$-groupoid, this equivalence corresponds to the Grothendieck construction of theorem 6.1.2.15.

Proof. This is a consequence of the equivalences $\underline{\mathrm{LCart}}(A^{\sharp}) \sim \underline{\mathrm{LCart}}^{c}(A^{\sharp})$, of the previous theorem and of the equivalence $\underline{\mathrm{Hom}}(A, \underline{\omega}) \sim \underline{\mathrm{Hom}}_{\ominus}(A^{\sharp}, \underline{\omega})$ induced by the second assertion of proposition 5.1.3.16. $\square$

**6.1.4.4.** The previous results provide equivalences

$$\underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \sim \underline{\mathrm{LCart}}^{c}(I) \quad \text{and} \quad \underline{\mathrm{Hom}}(A, \omega) \sim \underline{\mathrm{LCart}}(A^{\sharp})$$

By construction, for any morphism $f : I \to J$ between marked $\omega$-categories, we have a morphism

$$f^{*} : \underline{\mathrm{Hom}}_{\ominus}(J, \underline{\omega}) \to \underline{\mathrm{Hom}}(I, \underline{\omega})$$

Suppose now that the codomain of $f$ is of shape $A^{\sharp}$. The morphism (5.2.5.17) induces a morphism

$$f_{!} : \underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$$

and (5.2.5.18) induces natural transformations:

$$\mu : id \to f^{*}f_{!} \quad \epsilon : f_{!}f^{*} \to id$$

coming along with equivalences: $(\epsilon \circ_{0} f_{!}) \circ_{1} (f_{!} \circ_{0} \mu) \sim id_{f_{!}}$ and $(f^{*} \circ_{0} \epsilon) \circ_{1} (\mu \circ_{0} f^{*}) \sim id_{f^{*}}$. When $f$ is proper, the morphism (5.2.5.27) induces a morphism

$$f_{*} : \underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$$

and (5.2.5.28) induces natural transformations:

$$\mu : id \to f_{*}f^{*} \quad \epsilon : f^{*}f_{*} \to id$$

331