Just as in the finite case, with the substitution as composition and the obvious identity, it can be shown that contexts form a category with morphisms as defined above. This is called the *category of realizations* of the theory $T$. The composition of

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$$

and

$$\langle s_\delta \rangle_{\delta < \nu} : \{x_\beta : \Omega_\beta\}_{\beta < \mu} \to \{x_\delta : \Omega'_\delta\}_{\delta < \nu}$$

is the map

$$\langle s_\delta \rangle_{\delta < \nu} \circ \langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\delta : \Omega'_\delta\}_{\delta < \nu}$$

defined as the sequence $\langle s_\delta [\langle t_\beta | x_\beta \rangle_{\beta < \mu}] \rangle_{\delta < \nu}$.

Using the previous relation $\approx$ on contexts and rules we induce one on morphisms between contexts. If we have morphisms

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu} \text{ and } \langle t'_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta'_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega'_\beta\}_{\beta < \mu}$$

Then

$$\langle t_\beta \rangle_{\beta < \mu} \approx \langle t'_\beta \rangle_{\beta < \mu}$$

if and only if

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \approx \{x'_\beta : \Omega'_\beta\}_{\beta < \mu}$$

and for all $\gamma < \mu$

$$\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash t_\gamma : \Omega_\gamma [t_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma} \approx \{x_\beta : \Delta'_\beta\}_{\beta < \mu} \vdash t'_\gamma : \Omega'_\gamma [t'_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma}.$$

Unfolding the definition this means that

$$\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash \Omega_\gamma [t_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma} \text{ Type} \approx \{x_\beta : \Delta'_\beta\}_{\beta < \mu} \vdash \Omega'_\gamma [t'_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma} \text{ Type}$$

and that $\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash t_\gamma \equiv t'_\gamma$ for all $\gamma < \mu$.

The following remarks are results from [Car78] whose proofs are completely similar. However, it is important to make them explicit, since they imply that we can define a composition operation of equivalence classes of morphisms between contexts.

*Remark* A.21. Let $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ and $\langle t'_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega'_\beta\}_{\beta < \mu}$ two morphisms between contexts with $\langle t_\beta \rangle_{\beta < \mu} \approx \langle t'_\beta \rangle_{\beta < \mu}$.

100