to define this functor, however again we omit the proofs since they are similar to the original ones given by Cartmell.

On objects $\mathbb{C} : \kappa$-GAT $\to \kappa$-CON is defined as $\mathbb{C}_T$ for $T$ a generalized $\kappa$-algebraic theory. For a map $[I] : T \to T'$ between theories, we need a functor $\mathbb{C}(I) : \mathbb{C}_T \to \mathbb{C}_{T'}$:

1. On objects; $\mathbb{C}(I)([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]) := [\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda}],
2. On morphisms: If $[\langle t_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : \Delta_\beta\}_{\beta < \mu}]$ then $\mathbb{C}(I)([\langle t_\beta \rangle_{\beta < \mu}]) := [\langle \widetilde{I}(\langle t_\beta \rangle_{\beta < \mu})]$.

If there is an interpretation $J$ in the equivalence class $[I]$, then by theorem A.28 any rule $r$ of $T$ we get $\widetilde{I}(r) \approx \widetilde{J}(r)$. Therefore, it follows that the definition of $\mathbb{C}(I)$ does not depend on the representative of $[I]$.

It remains to verify that $\mathbb{C}(I)$ is indeed a contextual functor. Firstly, it is essential to verify that it is well-defined.

**Lemma B.12.** *Let $[I] : T \to T'$ be a map in $\kappa$-GAT then the following hold:*

1. *The interpretation $I$ preserves contexts: If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context in the theory $T$ then $\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda}$ is a context in the theory $T'$.*
2. *The interpretation $I$ preserves the equivalence relation $\approx$ between contexts: If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ and $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda}$ are contexts in the theory $U$ with $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda}$ then $\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda} \approx \{x_\alpha : \widetilde{I}(\Omega_\alpha)\}_{\alpha < \lambda}$.*
3. *The interpretation $I$ preserves morphisms between contexts: If $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ is a morphism between contexts in the theory $T$ then $\langle \widetilde{I}(t_\beta) \rangle_{\beta < \mu} : \{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda} \to \{x_\beta : \widetilde{I}(\Omega_\beta)\}_{\beta < \mu}$ is a morphism between contexts in the theory $T'$.*
4. *The interpretation $I$ preserves the equivalence relation $\approx$ between morphisms of contexts: If $\langle s_\beta \rangle_{\beta < \mu}$, $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ are morphisms between contexts in the theory $T$ with $\langle s_\beta \rangle_{\beta < \mu} \approx \langle t_\beta \rangle_{\beta < \mu}$ then $\langle \widetilde{I}(s_\beta) \rangle_{\beta < \mu} \approx \langle \widetilde{I}(t_\beta) \rangle_{\beta < \mu}$.*

*Proof.* The proof of each statement is consequence of theorem A.26 or theorem A.25. Our enumeration of variables give us a notation simplification of the proof given by [Car78].

For example, to prove 4; we have by assumption that $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\gamma \equiv_{\Omega_\gamma [t_\beta | x_\beta]_{\beta < \gamma}} s_\gamma$ for all $0 < \gamma \leq \mu$. Therefore, since the interpretation preserves this rule $\circ T$ we get that $\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda} \vdash \widetilde{I}(t_\gamma) \equiv_{\widetilde{I}(\Omega_\gamma)[\widetilde{I}(t_\beta)|x_\beta]_{\beta < \gamma}}$

117