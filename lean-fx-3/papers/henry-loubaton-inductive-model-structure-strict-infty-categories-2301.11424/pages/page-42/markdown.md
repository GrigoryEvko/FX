We then define the putative limit left semi-model structure as the left Bousfield localization of the lax-putative limit left semi-model structure by all sets $I_k$ (for all values of $k$). The existence of this localization is asserted by Theorem 7.3 of [24]. By Lemma A.9, fibrant objects correspond to morphisms having the right lifting property against iterated homotopy codiagonals of maps in $I_k$. Since weak equivalences between fibrant objects of the localized left semi-model structure correspond to weak equivalences in the unlocalized left semi-model structure, they also correspond to pointwise weak equivalences.

To show that the adjunction given in Definition 4.8 induces an adjunction between the putative limit left semi-model structure and the inductive left semi-model structure, one has to demonstrate that for any integer $k$, and $\phi \in I_k$, $c(\phi)$ is a weak equivalence of the inductive left semi-model structure. Let $i: A \mapsto B$ be the generating cofibration of $\infty$-$\mathbf{Cat}^{+k}$ such that $\phi$ is

$$\alpha_k(A \to B) \to \alpha_k(B \to I_A B).$$

The morphism $c(\phi)$ then corresponds to $B \to I_A B$, which is a weak equivalence by the definition of a relative cylinder object.

To conclude the characterization of fibrant objects of this left semi-model structure, we will show that for any fibrant object $(X_i, f_i)$ of the unlocalized left semi-model structure, the following conditions are equivalent:

1. $(X_i, f_i)$ has the right lifting property against all maps in $I_k$.
2. For any $k$, $f_k: X_k \to \tau_k X_{k+1}$ is a weak equivalence.
3. $(X_i, f_i)$ has the right lifting property against all maps of the form $\{\alpha_k(A \to B) \to \alpha_k(B \to I_A B)\}$ where $A \to B$ is an arbitrary cofibration in $\infty$-$\mathbf{Cat}^{+k}$.
4. $(X_i, f_i)$ has the right lifting property against iterated homotopy codiagonals of maps in $I_k$.

The implications $(1) \Rightarrow (2)$ and $(2) \Rightarrow (3)$ are a reformulation of Proposition A.7. The implication $(3) \Rightarrow (4)$ is Lemma 4.13. Finally, the implication $(4) \Rightarrow (1)$ is straightforward. $\square$

**4.14 Theorem.** *The Quillen adjunction between the putative limit left semi-model structure of Proposition 4.10 and the inductive left semi-model structure is a Quillen equivalence.*

$$\underset{n \in \mathbb{N}}{p \text{Lim}} \infty\text{-}\mathbf{Cat}_{\text{Sat-Ind}}^{+n} \simeq \infty\text{-}\mathbf{Cat}_{\text{Sat-Ind}}^{+\infty}$$

*Proof.* As the left adjoint preserves weak equivalence and fibrant objects of the unsaturated left semi-model structure by Proposition 4.9, one has to show that for every fibrant $\infty$-marked $\infty$-category $X$, and for every cofibrant and fibrant sequence $X_\bullet$ of the putative limit left semi-model structure, we have two weak equivalences:

$$c\tau X \to X \quad \text{and} \quad X_\bullet \to \tau c X_\bullet.$$

The first one is immediate because

$$X \cong \underset{n \in \mathbb{N}}{\text{Colim}} \tau_n X.$$

42