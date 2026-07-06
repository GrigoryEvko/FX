*Remark A.31.* The category $\mathbb{C}_T$ has a unique object $1 := [\emptyset]$, the equivalence class of the empty context. Note that this is a terminal object.

*Remark A.32.* Let $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$ be an object of $\mathbb{C}_T$. Then for any $\mu < \lambda$ we get a morphism $[\langle x_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \rightarrow [\{x_\beta : \Delta_\beta\}_{\beta < \mu}]$. Indeed, since $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context then for any $\beta < \lambda$ we have $\{x_\beta : \Delta_\beta\}_{\beta < \beta} \vdash \Delta_\beta$ Type. Therefore, it follows from (theorem A.4, 9) that $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash x_\alpha : \Delta_\alpha$ for all $\alpha < \lambda$. In particular this is true for all $\beta < \mu$, which gives the morphism above.

Following the same argument, if $\nu < \mu$, then we also have a map $[\langle x_\gamma \rangle_{\gamma < \nu}] : [\{x_\beta : \Delta_\beta\}_{\beta < \mu}] \rightarrow [\{x_\gamma : \Delta_\gamma\}_{\gamma < \nu}]$. Furthermore, we get a commutative diagram:

$$\begin{array}{ccc} [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] & \xrightarrow{[\langle x_\beta \rangle_{\beta < \mu}]} & [\{x_\beta : \Delta_\beta\}_{\beta < \mu}] \\ & \searrow [\langle x_\gamma \rangle_{\gamma < \nu}] & \downarrow [\langle x_\gamma \rangle_{\gamma < \nu}] \\ & & [\{x_\gamma : \Delta_\gamma\}_{\gamma < \nu}] \end{array}$$

*Remark A.33.* Since these morphisms are somewhat canonical we will use the notation “ $\rightarrow$ ”, and whenever we use this arrow for a morphism it must be assumed that such map is of this form. These morphisms are called display, which is Cartmell's terminology. In contrast, our 'display' maps can be of arbitrary length, which we will often refer to as *generalized display* maps.

Suppose there is a context $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + \varepsilon}]$ with $\varepsilon \geq 0$. Then we can consider an $\varepsilon$-indexed sequence of display morphisms:

$$\cdots \quad [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 2}] \longrightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 1}] \longrightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$$

Also, there is a display map $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + \varepsilon}] \rightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$. This display morphism will be by definition the composition for the sequence. If $\varepsilon = 0$, then this map is simply the identity. We also get a factorization of the map $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \rightarrow 1$ via display maps for any $\lambda \geq 0$.

*Observation A.34.* From the previous theorem A.32 we can observe that if $\lambda$ is a limit ordinal then $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$ is the limit of the sequence

$$\cdots \quad [\{x_1 : \Delta_1, x_2 : \Delta_2\}] \longrightarrow [\{x_1 : \Delta_1\}] \longrightarrow 1.$$

If there is another context $[\{x_\delta : \Gamma_\delta\}_{\delta < \gamma}]$ and maps

$$[\langle t_\beta \rangle_{\beta < \alpha}] : [\{x_\delta : \Gamma_\delta\}_{\delta < \gamma}] \rightarrow [\{x_\beta : \Delta_\beta\}_{\beta < \alpha}]$$

106