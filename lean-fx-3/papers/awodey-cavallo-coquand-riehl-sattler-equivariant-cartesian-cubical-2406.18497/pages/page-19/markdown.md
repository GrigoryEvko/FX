is classified by a unique map $\zeta_c^y: Z \to Y^+$ defining a pullback square

$$\begin{array}{c} C \xrightarrow{y} Y \xrightarrow{!} 1 \\ \downarrow_c \quad \downarrow_{\text{丨}} \quad \eta_Y \downarrow_{\text{丨}} \\ Z \xrightarrow{\zeta_c^y} Y^+ \xrightarrow{\top_* Y} \Omega. \\ \downarrow_{\chi_c} \end{array}$$

Moreover, for any $X \in \mathsf{E}$, the same results are true in $\mathsf{E}_{/X}$, and these classifying squares are stable under pullback. $\square$

We refer to the monomorphism $\eta_Y: Y \mapsto Y^+$ as the partial map classifier for $Y$, since partial maps from $Z$ to $Y$ are classified by (total) maps $Z \to Y^+$. We write $f^+: Y^{+X} \to X$ for the codomain of the partial map classifier for $(Y, f) \in \mathsf{E}_{/X}$, so that we have $\eta_f: Y \to Y^{+X}$.

**Definition 2.2.4.** A **relative +-algebra** structure on $f: Y \to X$ is a retraction over $X$ to the map $\eta_f: Y \mapsto Y^{+X}$ over $X$:

$$\begin{array}{c} Y \xlongequal{\quad} Y \\ \eta_f \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_f \\ Y^{+X} \xrightarrow{f^+} X. \end{array} \tag{2.2.5}$$

The **category of relative +-algebras** has relative +-algebras as objects and, as morphisms $f' \to f$, squares as below-left such that the induced diagram below-right commutes:

$$\begin{array}{ccc} Y' \longrightarrow Y & & Y' \longrightarrow Y \\ f' \downarrow \quad \downarrow_f & & \uparrow_{\text{丨}} \\ X' \longrightarrow X & & Y'^{+X'} \longrightarrow Y^{+X}. \end{array}$$

*Remark 2.2.6.* The relative version of the construction of Proposition 2.2.3 defines a pullback-preserving functorial factorization:

$$\begin{array}{ccc} W \xrightarrow{f^* g} Y & & W \xrightarrow{f^* g} Y \\ g^* f \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_f & & \eta_{g^* f} \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_{\text{丨}} \\ Z \xrightarrow{g} X & & W^{+Z} \longrightarrow Y^{+X} \\ & & g^* f^+ \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_{f^+} \\ & & Z \xrightarrow{g} X \end{array}$$

satisfying the hypotheses of Example 2.1.6. This defines a weak factorization system whose left maps are the monomorphisms and whose right maps are those admitting a relative +-algebra structure.

*Remark 2.2.7.* The partial map classifier $\eta_Y: Y \mapsto Y^+$ is the component at $Y$ of a unit natural transformation which is part of a monad structure on the (fibred) endofunctor $(-)^+: \mathsf{E} \to \mathsf{E}$. Thus the object $Y^+ = \Omega_! \top_* Y$ is itself a (free) +-algebra. This can be used to show that the functorial factorization of Remark 2.2.6 underlies an algebraic weak factorization system. See [GS17, 9.5] or [Awo26, §3] for details.

By the following proposition, we can see a relative +-algebra structure as consisting of a uniform choice of lifts against all monomorphisms.

**Proposition 2.2.8.** *The category of relative +-algebras is isomorphic to the category whose*

19