**Construction 7.5.** Lemma 7.4 allows us to construct a functor $\Omega : \mathbf{L}\mathbf{Adj} \rightarrow \mathbf{M}\mathbf{nd}_{\mathcal{C}}$, or more precisely, a functor $\mathbf{L}\mathbf{Adj}^{op} \rightarrow \mathbf{R}\mathbf{M}\mathbf{d}_{\mathcal{C}}$. The construction that sends an essentially surjective left adjoint functor $F : \mathcal{C} \rightarrow \mathcal{K}$ to the pullback $\mathcal{M} \rightarrow \mathcal{C}$ as in Lemma 7.4 is a contravariant functor: The presheaf construction (with its contravariant functoriality) defines a functor $((\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{\setminus \mathcal{C}})^{op} \rightarrow (\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{/\Pr(\mathcal{C})}$ (up to some easily dealt with size issues) which can be composed with the pullback functor $(\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{/\Pr(\mathcal{C})} \rightarrow (\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{/\mathcal{C}}$. Finally Lemma 7.4 shows that this functors sends the full subcategory $\mathbf{L}\mathbf{Adj}_{\mathcal{C}}$ to $\mathbf{R}\mathbf{M}\mathbf{d}_{\mathcal{C}}$.

We conclude the proof of Theorem 7.2, with:

**Proposition 7.6.** *The functor $\Omega : \mathbf{L}\mathbf{Adj}_{\mathcal{C}} \rightarrow \mathbf{M}\mathbf{nd}_{\mathcal{C}}$ of Construction 7.5 is an inverse for $\mathrm{Kl} : \mathbf{M}\mathbf{nd}_{\mathcal{C}} \rightarrow \mathbf{L}\mathbf{Adj}$.*

*Proof.* We will construct two explicit natural isomorphisms $\Omega \circ \mathrm{Kl}(M) \rightarrow M$ and $\mathrm{Kl} \circ \Omega(\mathcal{K}) \rightarrow \mathcal{K}$.

By Corollary 4.10 the restricted Yoneda embedding $\mathcal{C}^M \rightarrow \Pr(\mathcal{C}_M)$ is natural in $M$. Given the pullback defining the category of algebras of $\Omega(\mathcal{C}_M)$ this translated into a map, natural in $M$, from $\mathcal{C}^M$ to that category of algebras, which by Proposition 7.3 is an equivalence. Though the equivalence of Theorem 3.22, this translate to a isomorphism of monads $M \rightarrow \Omega \circ \mathrm{Kl}(M)$.

Given $F : \mathcal{C} \rightarrow \mathcal{K}$ in $\mathbf{L}\mathbf{Adj}$, recall that the category of algebras $\mathcal{C}^{\Omega(F)}$ is constructed (functorially) as the pullback:

$$\begin{array}{ccc} \mathcal{C}^{\Omega(F)} & \longrightarrow & \Pr \mathcal{K} \\ \downarrow & & \downarrow_{F^*} \\ \mathcal{C} & \longrightarrow & \Pr \mathcal{C} \end{array}$$

Its Kleisli category is the essentially image of the left adjoint of $\mathcal{C}^{\Omega(F)} \rightarrow \mathcal{C}$ and it is made functorial by Proposition 4.5. It hence follows from Proposition 4.8 (that the assumption are satisfied follows from the proof of Lemma 7.4) that we have a natural transformation $\mathcal{C}_{\Omega(F)} \rightarrow \Pr \mathcal{K}$ where $\Pr$ has its covariant/left adjoint functoriality$^4$. Now the explicit construction of the left adjoint to $\mathcal{C}^{\Omega(F)} \rightarrow \mathcal{C}$ done in the proof of Lemma 7.4 shows that the functor $\mathcal{C}_{\Omega(F)} \rightarrow \Pr \mathcal{K}$ induces an equivalence between $\mathcal{C}_{\Omega(F)}$ and the full subcategory

$^4$We refer again to section 6 of [12] for the fact that the two possible definition of this covariant functoriality are equivalent.

44