where at each successor stage it is given as before, $f := \langle t_\beta \rangle_{\beta < \nu}$, the context

$$f^* B_\mu := [\{x_\alpha : \Delta_\alpha, x_\beta : \Omega_\beta[t_\delta \mid x_\delta]_{\delta < \beta}\}_{\substack{\alpha < \lambda \\ \nu < \beta < \mu}}]$$

is the limit of the sequence on the left-hand side, with the obvious display maps to each object in the sequence, and

$$q(f, B_\mu) := [\langle t_\beta, x_\gamma \rangle_{\beta < \nu < \gamma < \mu}].$$

This makes the outer rectangle in (3) commutative. Moreover, the map $q(f, B_\mu)$ is the unique cone map induced by the family of maps

$$\{[\langle t_\beta, x_\gamma \rangle_{\beta < \nu < \gamma < \delta} : f^* B_\mu \to B_\delta\}_{\nu < \delta < \mu}.$$

Using the same notation as in the lemma above, we have:

Remark A.36. 1. If $f = Id_{B_\nu}$ then $(Id_{B_\nu})^* B_\mu = B_\mu$ and $q(Id_{B_\nu}, B_\mu) = Id_{B_\mu}$.

2. For a diagram

$$D \xrightarrow{g} C \xrightarrow{f} B,$$

we have that $g^*(f^*(A)) = (fg)^*(A)$ and $q(fg, A) = q(f, A)(g, f^*A)$.

We will refer to the category $\mathbb{C}_T$ as the syntactic category associated to the generalized $\kappa$-algebraic theory $T$.

Observation A.37. We note that theorem A.35 give us an explicit construction of pullbacks in $\mathbb{C}_T$, as well as the pullback of the maps and an explicit description of $q(f, B_\mu)$.

We finish this section by characterizing the display maps in the category $\mathbb{C}_T$. This result says that display maps are somehow generic. We start with a preparatory result.

Lemma A.38. Let $T$ be a generalized $\kappa$-algebraic theory and $\mathbb{C}_T$ its syntactic $\kappa$-contextual category. Assume that there is a $f : \Delta \to \Gamma$, then any display map $B \twoheadrightarrow \Delta$ of length 1 can be obtained as a pullback of the form

$$\begin{array}{c} B \longrightarrow \Gamma' \\ \downarrow \quad \downarrow \\ \Delta \xrightarrow{f} \Gamma \end{array}$$

109