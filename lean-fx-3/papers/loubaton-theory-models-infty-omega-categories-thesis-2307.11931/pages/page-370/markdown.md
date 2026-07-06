CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

natural in $a : A^t$. The functor

$$a : A \mapsto \hom_{\widehat{A}}(f, y(a))$$

is then representable, which concludes the proof according to proposition 6.2.2.2.

**6.2.3.26.** Let $i : A \to B$ be a functor between two $\mathbf{U}$-small $(\infty, \omega)$-categories. We define $N_i : B \to \widehat{A}$ as

$$a : A^t, b : B \mapsto \hom_B(i(a), b)$$

**Corollary 6.2.3.27.** *Let $i : A \to B$ be a functor between two $\mathbf{U}$-small $(\infty, \omega)$-categories with $B$ lax $\mathbf{U}$-cocomplete. The morphism $N_i : B \to \widehat{A}$ admits a left adjoint that sends an $(\infty, \omega)$-presheaf $f$ to $\operatorname{laxcolim}_{A_{/f}^t} i(\_)$*

*Proof.* The proof is similar to the one of corollary 6.2.3.25.

### 6.2.4 Kan extensions

We suppose the existence of a Grothendieck universe $\mathbf{Z}$ containing $\mathbf{W}$. As a consequence, we can use all the results of the last three subsections to respectively $\mathbf{V}$-small and locally $\mathbf{V}$-small objects.

**6.2.4.1.** Let $f : A \to B^\sharp$ be a morphism between marked $\mathbf{U}$-small $(\infty, \omega)$-categories. This induces for any $(\infty, \omega)$-category $C$ a morphism

$$\_ \circ f : \underline{\operatorname{Hom}}_\odot(B, C) \to \underline{\operatorname{Hom}}(A, C).$$

Let $g : A \to C$ be a morphism. A *left Kan extension* of $g$ along $f$ is a functor $\operatorname{Lan}_f g : B \to C$ and an equivalence

$$\hom_{\underline{\operatorname{Hom}}(B, C)}(\operatorname{Lan}_f g, h) \sim \hom_{\underline{\operatorname{Hom}}_\odot(A, C)}(g, h \circ f).$$

Remark that if the left Kan extension along $f$ exists for any $g$, the proposition 6.2.2.2 implies that the assignation $g \mapsto \operatorname{Lan}_f g$ can be promoted to a left adjoint, which is called the *global left Kan extension* of $f$.

**Proposition 6.2.4.2.** *Let $C$ be a $\mathbf{U}$-small $(\infty, \omega)$-category, $f : I \to B^\sharp$ a functor between $\mathbf{U}$-small $(\infty, \omega)$-categories and $g : I \to \underline{\operatorname{Hom}}(C, \underline{\omega})$ a functor. The functor $g$ then corresponds to a morphism $\tilde{g} : \underline{\operatorname{Hom}}_\odot(C^\sharp \times I, \underline{\omega})$. The left Kan extension of $f$ along $g$ corresponds to the morphism $(id_{C^\sharp} \times f)_! \tilde{g}$.*

*Proof.* This is a direct consequence of corollary 6.2.2.7.

360