1:10

M. SHULMAN

Vol. 19:2

We will refer to such an $X \times Y$ as a **product** of $X$ and $Y$. There is an analogue for nullary products and terminal nonlinear objects, denoted 1 (not to be confused with the linear $\mathbb{1}$). By Proposition 2.11(iii), if all $\times, 1$ exist then $\mathcal{P}^{\mathrm{NL}}$ is a **cartesian monoidal category**. Note that these are essentially facts about cartesian multicategories, which extend automatically to an LNL polycategory $\mathcal{P}$ from $\mathcal{P}^{\mathrm{NL}}$.

**Corollary 2.12.** *Any functor of LNL polycategories preserves nonlinear products and terminal objects.*

*Proof.* The equations in Proposition 2.11(iv) are preserved by any functor. $\square$

**Remark 2.13.** If we changed notation as suggested in Remark 2.7 to regard the nonlinear objects (or the “right-hand” ones) as instead forming a co-cartesian co-multicategory, then the identical operations $\times$ and 1 would instead behave like a coproduct and an initial object (and hence would be better denoted $+$ and $\varnothing$).

We now consider the **exponential modalities** (a.k.a. **storage modalities**) that relate linear and nonlinear objects.

**Definition 2.14.** Let $X$ be a nonlinear object and $A$ a linear one.

- An **F-modality** is a universal morphism $\psi \in \mathcal{P}(X \mid \mathsf{FX})$.
- A **U-modality** is a universal morphism $\psi \in \mathcal{P}(\underline{\mathsf{UA}} \mid \mathsf{A})$.
- An $\mathsf{\perp}$-**modality** is a universal morphism $\psi \in \mathcal{P}(X \mid \mathsf{\perp}X;)$.
- A $\mathsf{\cap}$-**modality** is a universal morphism $\psi \in \mathcal{P}(\underline{\mathsf{UA}} \mid A;)$.

Thus, the exponential modalities are characterized by natural bijections

$$\begin{aligned} \mathcal{P}(\Theta, X \mid \Gamma; \Delta) &\cong \mathcal{P}(\Theta \mid \Gamma, \mathsf{FX}; \Delta) & \mathcal{P}(\Theta \mid \mathsf{A}) &\cong \mathcal{P}(\Theta; \mathsf{UA}) \\ \mathcal{P}(\Theta, X \mid \Gamma; \Delta) &\cong \mathcal{P}(\Theta \mid \Gamma; \Delta, \mathsf{\perp}X) & \mathcal{P}(\Theta \mid A;) &\cong \mathcal{P}(\Theta; \mathsf{\cap}A). \end{aligned}$$

Note that $\mathsf{F}$ and $\mathsf{U}$ are covariant, while $\mathsf{\perp}$ and $\mathsf{\cap}$ are contravariant. We will see below that these are adjoint in pairs, $\mathsf{F} \dashv \mathsf{U}$ and $\mathsf{\cap} \dashv \mathsf{\perp}$, and induce the usual comonad $! = \mathsf{FU}$ and monad $? = \mathsf{\perp}\mathsf{\cap}$.

We can also consider internal-homs of various sorts.

**Definition 2.15.** Let $X, Y$ be nonlinear objects and $A, B$ be linear objects.

- A **linear hom** is a universal morphism $\psi \in \mathcal{P}(\mid A \multimap B, A; B)$.
- A **linear co-hom** is a universal morphism $\psi \in \mathcal{P}(\mid B; B \triangleleft A, A)$.
- A **nonlinear hom** is a universal morphism $\psi \in \mathcal{P}(X \multimap Y, X; Y)$.
- A **mixed hom** is one of the following:$^3$
  - a universal morphism $\psi \in \mathcal{P}(X \mid X \multimap B; B)$.
  - a universal morphism $\psi \in \mathcal{P}(A \multimap B \mid A; B)$.
  - a universal morphism $\psi \in \mathcal{P}(X \multimap B, X \mid \mathsf{B})$.

$^3$As notational mnemonics, the arrowhead in $\to, \to, \to$ indicates the domain object is nonlinear, the open circle in $\multimap, \to$ indicates the codomain object and hom-object are both linear, and the closed circle in $\to, \to$ indicates the codomain object is linear but the hom-object is nonlinear.