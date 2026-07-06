As well, the following proposition allows us to recover the $\infty$-category of algebras of a monad out of its Kleisli categories.

**Proposition 7.3.** *Let $\mathcal{C}^M \to \mathcal{C}$ be a monadic functor The square*

$$\begin{array}{ccc} \mathcal{C}^M & \longrightarrow & \operatorname{Pr}(\mathcal{C}_M) \\ \downarrow & & \downarrow \\ \mathcal{C} & \longrightarrow & \operatorname{Pr}(\mathcal{C}) \end{array}$$

*where the horizontal arrows are the restricted Yoneda embeddings is a pullback.*

*Proof.* In the diagram, the vertical maps are monadic, and the bottom horizontal map is fully faithful. By 6.3, we must show that the adjoint natural transformation (“$L_2\Psi \to \Phi L_1$” in the notation of 6.3) is an equivalence. But this was done within the proof of Proposition 4.9, when checking that Proposition 4.8 can be applied. $\square$

A key observation is that the pullback of Proposition 7.3 allows us to associate a monad on $\mathcal{C}$ to every essentially surjective left adjoint functor $L : \mathcal{C} \to \mathcal{K}$.

**Lemma 7.4.** *Let $F : \mathcal{C} \to \mathcal{K}$ be an essentially surjective left adjoint functor, then, in the pullback square:*

$$\begin{array}{ccc} \mathcal{M} & \longrightarrow & \operatorname{Pr}(\mathcal{K}) \\ \downarrow & \downarrow^\perp & \downarrow \\ \mathcal{C} & \longrightarrow & \operatorname{Pr}(\mathcal{C}) \end{array}$$

*The functor $\mathcal{M} \to \mathcal{C}$ is a monadic right adjoint.*

*Proof.* The proof is the same as in Proposition 5.2 except for the part about the existence of a left adjoint functor $\mathcal{C} \to \mathcal{M}$ (which in Proposition 5.2 follows from a presentability argument). Because $F : \mathcal{C} \to \mathcal{K}$ has a right adjoint $R$, the restriction functor $F^* : \operatorname{Pr}(\mathcal{K}) \to \operatorname{Pr}(\mathcal{C})$ sends the representable at $X \in \mathcal{K}$ to the representable at $R(X) \in \mathcal{C}$, and (as for any functor $F$), its left adjoint functor $F_! : \operatorname{Pr}(\mathcal{C}) \to \operatorname{Pr}(\mathcal{K})$ sends representables to representables. It follows that, as $\mathcal{C}$ and $\mathcal{M}$ are respectively full subcategories of $\operatorname{Pr}(\mathcal{C})$ and $\operatorname{Pr}(\mathcal{K})$ preserved by the action of $F^*$ and $F_!$, the restriction of $F_!$ to a functor $\mathcal{C} \to \mathcal{M}$ is a left adjoint to the restriction of $F^* : \mathcal{M} \to \mathcal{C}$. $\square$

43