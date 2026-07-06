**Proposition 4.5.** *Let $X^{\bullet} : \mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$ be a functor as in Assumption 4.4 above. Then there is a functor $\mathcal{D} \rightarrow \mathbf{Cat}_{\infty}$ that sends each object of $d$ to $X_d$ and each arrow $f$ to $f_!$.*

A precise construction of the functor is given in the proof and will be important on a few occasions in the rest of the paper.

*Proof.* Let $\pi : \mathcal{X} \rightarrow \mathcal{D}$ be the cartesian fibration classified by $X$. Up to equivalence of $\infty$-categories one can freely assume that objects of $\mathcal{X}$ are pairs $(d, x)$ where $d$ is an object of $\mathcal{D}$ and $x$ is an object of $\mathcal{X}^d$.

We write $\mathcal{X}'$ for the full subcategory of $\mathcal{X}$ of objects of the form $(d, x)$ for $x \in \mathcal{X}_d$, and we claim that $\mathcal{X}' \rightarrow \mathcal{D}$ is a cocartesian fibration classifying a functor as described in the proposition.

Indeed, for each arrow $f : d' \rightarrow d$ and $x \in X_{d'}$, we have a unit arrow $x \rightarrow f^* f_! x$ in $X^{d'}$ constructed from the adjunction isomorphism in the usual way. It corresponds to an arrow $(d', x) \rightarrow (d, f_! x)$ in $\mathcal{X}$. Exactly as in the case of actual adjunction (see the proof of “(2) $\Rightarrow$ (1)” of Proposition 5.2.2.8 of [15]), the adjunction isomorphism shows that this arrow is a locally $\pi$-cocartesian arrow in $\mathcal{X}$.

And Corollary 5.2.2.4 of [15] shows that, as $\pi$ is a Cartesian fibration, any locally $\pi$-coCartesian arrow is actually coCartesian, so this construction provide us with coCartesian lifts of any arrow $d' \rightarrow d$ for any object in $\mathcal{X}'$ over $d'$.

By the definition of $\mathcal{X}'$ its fiber over an object $d \in \mathcal{D}$ is indeed equivalent to $X_d$, and the way we constructed the cocartesian lift shows the functoriality is exactly the $f_!$ functor.

It immediately follows from Proposition 4.3 and Proposition 4.5 that:

**Corollary 4.6.** *The Kleisli category construction $T \mapsto \mathcal{C}_T$ defines a functor $\mathbf{Mnd}_{\mathcal{C}} \rightarrow \mathbf{Cat}_{\infty}$. Each morphism of monads $f : T \rightarrow M$ is sent to the partial left adjoint $f_! : \mathcal{C}_T \rightarrow \mathcal{C}_M$ to $f^*$.*

*Remark 4.7.* Because the initial object of $\mathbf{Mnd}_{\mathcal{C}}$ is the identity monad $I$ and the Kleisli category $\mathcal{C}_I$ of $I$ is equivalent to $\mathcal{C}$, it immediately follows that the Kleisli category construction can actually be seen as a functor from $\mathbf{Mnd}_{\mathcal{C}}$ to the coslice category $(\mathbf{Cat}_{\infty})_{\setminus \mathcal{C}}$, sending each monad $T$ to the free algebra functor $\mathcal{C} \rightarrow \mathcal{C}_T$.

28