CHAPTER 2. STUDY OF COMPLICIAL SETS

for any $a \in M$, $tX_a$ is a subset of $X_a$ including degeneracies, i.e the image of morphisms $X_p : X_b \to X_a$ for $p : b \to a$ in $B_-$.

A stratified morphism $f : (X, tX) \to (Y, tY)$ is the data of a morphism on the underlying presheaf such that $f(tX_n) \subset tY_n$. The category of stratified presheaves is denoted by $\mathrm{tPsh}_M(B)$.

Definition 2.1.2.2. A morphism between two stratified presheaves is entire if it is the identity on the underlying presheaves.

Construction 2.1.2.3. We have an adjunction

$$(\_)^\flat : \mathrm{Psh}(B) \xleftrightarrow{\perp} \mathrm{tPsh}_M(B) : (\_)^\sharp$$

where the left adjoint is a fully faithful inclusion that sends a presheaf $X$ onto $(X, S)$ where $S$ is the smaller stratification on $X$, and where the right adjoint is the obvious forgetful functor. We will identify presheaves on $B$ with their image by the functor $(\_)^\flat$.

Construction 2.1.2.4. If $b$ is an object of $M$, we denote by $b_t$ the stratified presheaf $(b, S)$, where $S$ is the smaller stratification that includes $id : b \to b$.

We then define $t_M B$ as the full subcategory of $\mathrm{tPsh}_M(B)$ spanned by the objects of shape $a$ or $b_t$ with $a \in B$ and $b \in M$. We then have equalities:

$$\mathrm{Hom}_{t_M B}(a, b) := \mathrm{Hom}_B(a, b),$$

$$\mathrm{Hom}_{t_M B}(a, b_t) := \mathrm{Hom}_B(a, b),$$

$$\mathrm{Hom}_{t_M B}(a_t, b) := \mathrm{Hom}_B(a, b) \cap B_- \setminus \{id_a\},$$

$$\mathrm{Hom}_{t_M B}(a_t, b_t) := \mathrm{Hom}_B(a, b) \cap B_-.$$

The canonical functor $B \to t_M B$ is then fully faithful and we will identify object of $B$ with their image through this functor.

The category of $M$-stratified presheaves is then equivalent to the fully faithful subcategory of presheaves $X$ on $t_M B$ such that for any $b \in M$, $X(b_t) \to X(b)$ is a monomorphism. In particular, we have an adjunction

$$\pi : \mathrm{Psh}(t_M B) \xleftrightarrow{\perp} \mathrm{tPsh}_M(B) : \iota \tag{2.1.2.5}$$

Proposition 2.1.2.6. The category $t_M B$ admits a structure of elegant Reedy category, that makes the inclusion $B \to t_M B$ a morphism of Reedy category. There is no non trivial negative morphism whose codomain is of shape $b_t$ for $b \in M$. There is no non trivial positive morphism whose domain is of shape $b_t$ for $b \in M$.

Proof. We define the degree degree function $ob(t_M B) \to \mathbb{N}$ by the assignment

$$d'(b) := 2d(b) \quad d'(b_t) := 2d(b) + 1$$

The category $(t_M B)_+$ is the smallest that includes $B_+$ and morphisms of shape $a \to a_t$. The category $(t_M B)_-$ is the smallest that includes $B_-$ and morphisms of shape $b_t \to a$.

To prove the axioms of Reedy category, we can replicate the strategy used in proposition C.2 of [OR20b] with obvious modification to this more general framework.

We still have to show that $tB$ is elegant. Let $X$ be a presheaf on $t_M B$, $a$ an element of $t_M B$, $f : a \to a'$ and $g : a \to a'$ two negative morphisms, an element $x$ of $X(a)$, two non degenerate elements $y \in X(a')$ and $z \in X(a'')$ such that $f^*y = x$, $g^*z = x$.

66