cartesian lift in $\mathrm{FIB}(\mathcal{C})$ is a pullback square

$$\begin{array}{c} A \xrightarrow{k} B \\ f \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \xrightarrow{l} \Gamma. \end{array}$$

This comprehension category is not necessarily split, reflecting the fact that taking pullbacks is not strictly functorial. Nevertheless, we can replace it by a split one via the functor

$$(-)_! : \mathbf{CompCat}(\mathcal{C}) \to \mathbf{SplCompCat}(\mathcal{C})$$

from the category of comprehension categories over $\mathcal{C}$ to the category of split comprehension categories over $\mathcal{C}$, the description of this functor appears in [LW15, 3.1] which we now recall. This produces a split comprehension category $(\mathcal{C}_!, \mathrm{FIB}(\mathcal{C})_!, p_!, F_!)$ which is equivalent to the one we started with. Unfolding the result, we take the $\mathcal{C}_!$ to be simply $\mathcal{C}$.

The category $\mathrm{FIB}(\mathcal{C})_!$ has:

- Objects: for each $\Gamma \in \mathcal{C}$ an object is a tuple $A := (V_A, E_A, f_A)$ where $V_A \in \mathcal{C}$, $E_A \twoheadrightarrow V_A \in \mathrm{FIB}(\mathcal{C})_{V_A}$ and $f_A : \Gamma \to V_A \in \mathcal{C}$. We also employ the notation $[A] := f_A^* E_A$ given by taking the pullback of $E_A \twoheadrightarrow V_A$ along $f_A$, so we get a fibration $[A] \twoheadrightarrow \Gamma$. In addition, we write $(E_A)_{f_A}$ for the arrow $[A] \to E_A$. Thus, an object over $\Gamma$ is a diagram in $\mathcal{C}$ of the form

$$\begin{array}{c} E_A \\ \Big\downarrow \\ \Gamma \xrightarrow{f_A} V_A. \end{array}$$

- Morphisms: A map between $(V_B, E_B, f_B) \to (V_A, E_A, f_A)$ over $\sigma : \Delta \to \Gamma$ is a map in $\mathcal{E}$ between $[B] \twoheadrightarrow \Delta$ and $[A] \twoheadrightarrow \Gamma$, i.e., a commutative square

$$\begin{array}{c} [B] \longrightarrow [A] \\ \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \xrightarrow{\sigma} \Gamma. \end{array}$$

- Composition is induced by the composition in $\mathcal{E}$, consequently, given by pasting commutative squares.

138