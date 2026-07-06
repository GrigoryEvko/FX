for all $\alpha < \lambda$ then we can simply take the map

$$[\langle t_\alpha \rangle_{\alpha < \lambda} : [\{x_\delta : \Gamma_\delta\}_{\delta < \gamma}] \rightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}].$$

This can be shown to be the cone map (which is unique). This verifies our claim.

Using theorem A.32 we can define a function:

$$\nu : Ob(\mathbb{C}_T) \longrightarrow \kappa$$

as $\nu([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]) := \lambda$. We call this the *length function*. We can use $\nu$ to construct a filtration on the objects of $\mathbb{C}_T$: we define

$$Ob_\lambda(\mathbb{C}_T) := \nu^{-1}(\lambda)$$

then $Ob(\mathbb{C}_T) = \coprod_{\lambda < \kappa} Ob_\lambda(\mathbb{C}_T)$, and so if $\alpha \leq \beta$ then $Ob_\alpha(\mathbb{C}_T) \subseteq Ob_\beta(\mathbb{C}_T)$. Furthermore, if $p : A \rightarrow B$ is a display morphism, then $\nu(B) \leq \nu(A)$. For $\alpha < \beta$ there are functions

$$\pi_\beta : Ob_\beta(\mathbb{C}_T) \rightarrow Ob_\alpha(\mathbb{C}_T)$$

that are defined in the obvious way. Additionally, $1 \in Ob_0(\mathbb{C}_T)$ is unique.

The proof of the following lemma is the same as in [Car78].

**Lemma A.35.** *The pullback of a display map along arbitrary morphisms in $\mathbb{C}_T$ exists, and it is also display.*

*Proof.* We use induction over the context length. Assume we have the following diagram in $\mathbb{C}_T$:

$$\begin{array}{c} [\{x_\beta : \Omega_\beta\}_{\beta < \mu+1}] \\ \downarrow [\langle x_\beta \rangle_{\beta < \mu}] \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \xrightarrow{[\langle t_\beta \rangle_{\beta < \mu}]} [\{x_\beta : \Omega_\beta\}_{\beta < \mu}] \end{array}$$

Then the pullback is given using theorem A.21, and the context is

$$[\{x_\alpha : \Delta_\alpha, x_\mu : \Omega_\mu[t_\beta \mid x_\beta]_{\beta < \mu}\}_{\alpha < \lambda}].$$

Therefore we have a commutative square

$$\begin{array}{c} [\{x_\alpha : \Delta_\alpha, x_\mu : \Omega_\mu[t_\beta \mid x_\beta]_{\beta < \mu}\}_{\alpha < \lambda}] \xrightarrow{[\langle t_\beta, x_\mu \rangle_{\beta < \mu}]} [\{x_\beta : \Omega_\beta\}_{\beta < \mu+1}] \\ [\langle x_\alpha \rangle_{\alpha < \lambda}] \downarrow \downarrow [\langle x_\beta \rangle_{\beta < \mu}] \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \xrightarrow{[\langle t_\beta \rangle_{\beta < \mu}]} [\{x_\beta : \Omega_\beta\}_{\beta < \mu}] \end{array} \quad (2)$$

107