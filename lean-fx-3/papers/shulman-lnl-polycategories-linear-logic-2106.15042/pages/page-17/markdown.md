Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:17

Example 3.7. Let $\mathcal{E}$ be a symmetric multicategory; we can enhance it to an LNL multicategory with $\mathsf{F}$ by taking the nonlinear objects to be the commutative comonoids in $\mathcal{E}$. It may not be immediately obvious how to define a comonoid in a multicategory that lacks $\otimes$, but it is possible: $C$ is a comonoid when it is equipped with operations

$$\mathcal{E}(\Theta_1, C, C, \Theta_2; B) \to \mathcal{E}(\Theta_1, C, \Theta_2; B)$$

$$\mathcal{E}(\Theta_1, \Theta_2; B) \to \mathcal{E}(\Theta_1, C, \Theta_2; B)$$

that are associative, unital, and appropriately natural and equivariant. Such cocommutative comonoids form a cartesian multicategory with a forgetful multicategory functor to $\mathcal{E}$, so by Proposition 3.1 it yields an LNL multicategory.

If $\mathcal{E}$ is symmetric monoidal, then cocommutative comonoids form a cartesian monoidal category, so this LNL multicategory has $\times, 1, \otimes, \mathbb{1}, \mathsf{F}$. Thus, if $\mathsf{F}$ has a right adjoint $\mathsf{U}$, i.e. if cofree cocommutative comonoids exist, then it is an LNL adjunction, known as a Lafont category [Laf88] or a free exponential modality [MTT18]. But we get an LNL multicategory even without these assumptions.

In general, given a category with a linear exponential comonad, we prefer to regard it as an LNL multicategory via the Kleisli construction rather than the Eilenberg–Moore construction. The reason for this is the following folklore observation, showing that Kleisli adjunctions can be detected by a purely intrinsic condition:

Lemma 3.8. An adjunction $F: \mathcal{A} \rightleftarrows \mathcal{B}: G$ is equivalent to the Kleisli adjunction of the monad $GF$ if and only if its left adjoint $F$ is essentially surjective on objects, and isomorphic to that Kleisli adjunction if and only if $F$ is bijective on objects.

Proof. The “only if” direction is clear, so suppose $F$ is essentially surjective on objects, and let $F_T: \mathcal{A} \rightleftarrows \mathcal{A}_T: G_T$ be the Kleisli adjunction of the monad $T = GF$. Thus the objects of $\mathcal{A}_T$ are formal copies “$A_T$” of the objects $A \in \mathcal{A}$, with $\mathcal{A}_T(A_T, B_T) = \mathcal{A}(A, TB)$. There is a unique comparison functor $H: \mathcal{A}_T \to \mathcal{B}$ defined by $H(A_T) = FA$, which is essentially surjective on objects since $F$ is (and bijective on objects if $F$ is). But it is also fully faithful, since $\mathcal{B}(FA, FB) \cong \mathcal{A}(A, GFB) = \mathcal{A}(A, TB) = \mathcal{A}_T(A_T, B_T)$; hence it is an equivalence.

Thus, applying the Kleisli construction, we have the following locally full sub-2-categories of LNLPoly:

- Symmetric monoidal categories with linear exponential comonad. This includes Seely comonads (if the category has finite products) and Lafont comonads (if cofree cocommutative comonoids exist).
- Symmetric monoidal categories with linear exponential comonad and any desired limits and any desired colimits preserved by the tensor product in each variable.
- Closed symmetric monoidal categories with linear exponential comonad and any desired limits and colimits.

In each case the “strong” morphisms, corresponding to functors of LNL multicategories that preserve (among other things) the exponential modalities $\mathsf{F}, \mathsf{U}$, are those that preserve the comonad up to coherent isomorphism: $F(!A) \cong !(FA)$.

Note that all of these LNL polycategories have the following property.

Definition 3.9. An LNL polycategory is of Kleisli type if it is equipped with a choice of $\mathsf{U}$ that is bijective on objects.