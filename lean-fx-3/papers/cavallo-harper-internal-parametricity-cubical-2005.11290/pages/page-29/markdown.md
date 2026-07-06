Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:29

### Theorem 3.19. $\neg$WLEM.

Proof. Suppose we have $w \in \mathsf{WLEM}$. By Lemma 3.18, we know that $\mathsf{fst} \circ w$ is constant, so $\mathsf{fst}(w \top)$ and $\mathsf{fst}(w \bot)$ are equal. We obtain a contradiction by case analysis; clearly $\mathsf{fst}(w \top)$ must be $\mathsf{ff}$ and $\mathsf{fst}(w \bot)$ must be $\mathsf{tt}$.

For a deeper exploration of the relationship between parametricity and the excluded middle, we refer to Booij, Escardó, Lumsdaine, and Shulman [BELS16].

3.4. The smash product. Now we come to our motivating example: proving coherence laws for the smash product. In this section, we adopt some conventions for dealing with pointed types, elements of $\mathcal{U}_{\mathsf{pt}} := (A : \mathcal{U}) \times A$. We give pointed types names like $A_*, B_*, \ldots$ and write $A, B, \ldots$ and $a_0, b_0, \ldots$ for their first and second components respectively. Given two pointed types $A_*, B_*$, the type of basepoint-preserving functions between them is defined as $A_* \to B_* := (f : A \to B) \times \mathsf{Path}_B(f a_0, b_0)$. The identity function is a basepoint-preserving function $\langle \lambda a.a, \lambda^\parallel ..a_0 \rangle \in A_* \to A_*$, and there is a unique pointed constant function $\langle \lambda ..b_0, \lambda^\parallel ..b_0 \rangle \in A_* \to B_*$ between any pair of pointed types. The type of pointed functions can itself be made a pointed type $A_* \to_* B_*$ by taking the pointed constant function as basepoint, but we will not need this here. As with types, we write $f_*$ for basepoint-preserving functions, $f$ for the underlying function, and $f_0$ for the proof that it preserves the basepoint. Finally, we write $\mathsf{bool}_*$ for the booleans with basepoint $\mathsf{tt}$.

The underlying type of the smash product is given by the following higher inductive type.

data $A_* \land B_*$ where
$\mid \langle\langle a : A, b : B \rangle\rangle \in A_* \land B_*$$
$\mid \circledast^\mathsf{L} \in A_* \land B_*$$
$\mid \circledast^\mathsf{R} \in A_* \land B_*$$
$\mid \mathsf{spoke}^\mathsf{L}(b : B, x : \mathbb{I}) \in A_* \land B_* \ [x = 0 \hookrightarrow \circledast^\mathsf{L} \mid x = 1 \hookrightarrow \langle\langle a_0, b \rangle\rangle]$
$\mid \mathsf{spoke}^\mathsf{R}(a : A, x : \mathbb{I}) \in A_* \land B_* \ [x = 0 \hookrightarrow \circledast^\mathsf{R} \mid x = 1 \hookrightarrow \langle\langle a, b_0 \rangle\rangle]$

In words, $A_* \land B_*$ is the ordinary product $A \times B$ quotiented by the relation collapsing together all elements of the form $\langle a_0, b \rangle$ or $\langle a, b_0 \rangle$. Elements of the former form are identified with a new “hub” point $\circledast^\mathsf{L}$, while elements of the latter are identified with a separate point $\circledast^\mathsf{R}$, producing a shape shown in Figure 7. We write $A_* \land_* B_*$ for the smash product viewed as a pointed type with basepoint $\langle\langle a_0, b_0 \rangle\rangle$.

We will begin by focusing on the following theorem.

Theorem 3.20. Any family of pointed functions $(A_*, B_*: \mathcal{U}_{\mathsf{pt}}) \to (A_* \land_* B_* \to A_* \land_* B_*)$ is either the polymorphic identity or the polymorphic constant pointed function, up to a path.

In an effort to show we have nothing up our sleeves, we will avoid sweeping gory details—that is, coherence proofs—under the rug. However, we encourage the reader to focus on the broad strokes of the argument, and as such we will be less diligent about explaining the gory details.

The relations we use in the following will all be graphs of functions. As such, we introduce the following shorthand notation.

Definition 3.21. Given $f : A \to B$, write $\mathsf{Gr}_r(A, B, f) := \mathsf{Gel}_r(A, B, a.b.\mathsf{Path}_B(f a, b))$. Given $f_* : A_* \to B_*$, define $\mathsf{Gr}_r^*(A_*, B_*, f_*) := \langle \mathsf{Gr}_r(A, B, f), \mathsf{gel}_r(a_0, b_0, f_0) \rangle \in \mathcal{U}_{\mathsf{pt}}$.