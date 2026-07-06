By the $\infty$-categorical Yoneda lemma, it follows that when $R$ has a partial left adjoint $\mathcal{D}' \rightarrow \mathcal{C}'$ then there is an essentially unique functor $F : \mathcal{D}' \rightarrow \mathcal{C}$, called the partial left adjoint of $R$, endowed with an adjunction isomorphism:

$$\operatorname{Map}_{\mathcal{D}}(X, R(Y)) \simeq \operatorname{Map}_{\mathcal{C}}(F(X), Y)$$

natural in $X \in \mathcal{D}'$ and $Y \in \mathcal{C}$.

As mentioned above, our main example of partial left adjoints comes from morphisms of monads:

**Proposition 4.3.** *Let $f : T \rightarrow M$ be a morphism of monads on a category $\mathcal{C}$. Then the forgetful functor between their categories of algebras $f^* : \mathcal{C}^M \rightarrow \mathcal{C}^T$ has a partial left adjoint $f_! : \mathcal{C}_T \rightarrow \mathcal{C}_M$ between the full subcategories $\mathcal{C}_T \subset \mathcal{C}^T$ and $\mathcal{C}_M \subset \mathcal{C}^M$ of free algebras.*

*Proof.* Let $U : \mathcal{C}^T \rightarrow \mathcal{C}$ and $V : \mathcal{C}^M \rightarrow \mathcal{C}$ be the two forgetful functors.

For any free algebra $X = T(A) \in \mathcal{C}_T$ and $Y$ an $M$-algebra, we have a series of isomorphisms all natural in $Y \in \mathcal{C}^M$:

$$\operatorname{Map}_{\mathcal{C}^T}(X, f^*Y) \simeq \operatorname{Map}_{\mathcal{C}}(A, U(f^*Y)) \simeq \operatorname{Map}_{\mathcal{C}}(A, V(Y)) \simeq \operatorname{Map}_{\mathcal{C}^M}(MA, Y).$$

Thus, the functor $\operatorname{Map}_{\mathcal{C}^T}(X, f^*\text{-})$ is representable by $MA$, which concludes the proof. $\square$

In order to study the functoriality properties of the Kleisli category construction, we will consider more generally the question of how partial left adjoints assemble into a $\mathbf{Cat}_{\infty}$-valued functor. This occurs in exactly the same way as left adjoints assemble into a $\mathbf{Cat}_{\infty}$-valued functor (as show for example for adjointable functors between locally presentable $\infty$-categories in [15, Corollary 5.5.3.4]). To remind ourselves of the main case of interest, i.e. the category of monads, we will use similar notation for the general case:

**Assumption 4.4.** Consider a functor $\mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$, denoted $d \mapsto X^d$. For $f : d \rightarrow d'$ an arrow in $\mathcal{D}$, we denote the induced functor by $f^* : X^{d'} \rightarrow X^d$.

We also assume that for each object $d \in \mathcal{D}$, we have a full subcategory $X_d \subset X^d$ such that for each edge $f : d \rightarrow d'$, $f^* : X^{d'} \rightarrow X^d$ has a partial left adjoint $f_! : X_d \rightarrow X_{d'}$.

It should be noted that this automatically implies that if $d$ and $d'$ are isomorphic in $\mathcal{D}$, then the subcategory $X_d$ and $X_d'$ are identified by the equivalence between $X^d$ and $X^{d'}$.

27