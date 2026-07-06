where $\Gamma' \rightarrow \Gamma$ is of length 1.

*Proof.* This is simply a reformulation of theorem A.13. Assume that

$$f = [\langle t_\beta \rangle_{\beta < \mu} ] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \rightarrow [\{x_\beta : \Gamma_\beta\}_{\beta < \mu}].$$

Therefore, when the display map is of the form

$$[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda+1}] \rightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}].$$

We can construct the square

$$\begin{array}{ccc} [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda+1}] & \xrightarrow{\langle t_\beta, x_\lambda \rangle_{\beta < \mu}} & [\{x : \Gamma_\beta, x_\lambda : \Delta_\lambda\}_{\beta < \mu}] \\ \downarrow & & \downarrow \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] & \xrightarrow{\langle t_\beta \rangle_{\beta < \mu}} & [\{x : \Gamma_\beta\}_{\beta < \mu}]. \end{array}$$

Since for all $\beta < \mu$, $x_\beta$ does not occur in $\Delta_\lambda$ we have that $\Delta_\lambda[t_\beta|x_\beta]_{\beta < \mu} \equiv \Delta_\lambda$. Hence, it follows from the construction of pullbacks in $\mathbb{C}_T$ (theorem A.35) that the square above is indeed a pullback diagram. $\square$

We are ready to give the full description of display maps.

**Proposition A.39.** *Every display map $B \rightarrow \Delta$ in $\mathbb{C}_T$ is a limit of a $\kappa$-small tower $V : \lambda \rightarrow \mathbb{C}_T$ where for each limit ordinal $\beta < \lambda$*

$$V(\beta) = \text{Lim}_{\alpha < \beta} V(\alpha)$$

*and the map $V(\alpha + 1) \rightarrow V(\alpha)$ is a pullback of a length one display map of the form $(\Gamma, A) \rightarrow \Gamma$ where $\Gamma \vdash A$ Type is a type axiom of the theory $T$.*

*Proof.* Each display map in $\mathbb{C}_T$ has a length $\lambda$. Just as in theorem A.32 it admits a decomposition into display maps. It will be enough to prove the second claim, and this follows by an inductive argument in conjunction with the previous theorem A.38. The inductive step provides us with the required map $f : V(\alpha) \rightarrow \Gamma$ in theorem A.38. $\square$

## B Contextual categories and Cartmell theories

This section is the most relevant part. We will show that from the syntax of a generalized $\kappa$-algebraic theory we can construct a category, called $\kappa$-contextual category, which we now introduce.

110