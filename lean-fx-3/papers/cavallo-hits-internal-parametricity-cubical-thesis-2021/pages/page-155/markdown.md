Elimination 143

Given an argument context $\Theta$, we define a telescope $(\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi)$ elementwise.

$$
\begin{aligned}
(\cdot)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\cdot) &:= \cdot \\
(\Theta, a: A)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi, M/a) &:= ((\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi), a: (\Theta.A)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi; \bar{v}_{(\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi)}; M))
\end{aligned}
$$

We can now state the criteria defining the well-formed lists of clauses $\mathcal{E}$ for the eliminator. To build these up inductively, we define a *partial* specification judgment $\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} \in [\mathcal{K}' \Rightarrow h.D]$, which states that the eliminator $\mathcal{E}$ contains clauses for eliminating from some prefix $\mathcal{K}'$ of a specification $\mathcal{K}$. A complete eliminator specification for $\mathcal{K}$ is then one satisfying $\Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} \in [\mathcal{K} \Rightarrow h.D]$. It is necessary to keep a reference to the complete $\mathcal{K}$ throughout, as recursive clauses should be able to handle arguments not from $\text{Ind}_{\mathcal{K}'}^{\Delta}(-)$ but from $\text{Ind}_{\mathcal{K}}^{\Delta}(-)$.

**Definition 6.4.3 (Eliminator specification).** The partial eliminator specification judgment, $\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} = \mathcal{E}' \in [\mathcal{K}' \Rightarrow h.D]$, is defined as follows.

$$
\begin{aligned}
\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \cdot = \cdot \in [\cdot \Rightarrow h.D] \\
\Gamma \gg \Delta \blacktriangleright \mathcal{K} @ \ell \Rightarrow (\mathcal{K}' \mid \mathcal{C}) \quad \Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} = \mathcal{E}' \in [\mathcal{K}' \Rightarrow h.D] \\
\mathcal{C} = [\Phi; \Omega; \delta; \Theta; \xi_i \hookrightarrow M_i] \quad R := (\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\bar{v}_{(\Theta)_{\mathcal{K}}^{\Delta}}) \\
H := (\Phi, \Omega, (\Theta)_{\mathcal{K}}^{\Delta}, R) \quad \Gamma, H \gg T = T' \in D[\delta, \text{intro}_{\ell}^{\mathcal{K}}(\bar{v}_{\Phi}; \bar{v}_{\Omega}; \bar{v}_{(\Theta)_{\mathcal{K}}^{\Delta}})/h] \\
(\forall i) \Gamma, H, \xi_i \gg T = (M_i)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\bar{v}_{(\Theta)_{\mathcal{K}}^{\Delta}}; \bar{v}_{R}) \in D[\delta, \text{intro}_{\ell}^{\mathcal{K}}(\bar{v}_{\Phi}; \bar{v}_{\Omega}; \bar{v}_{(\Theta)_{\mathcal{K}}^{\Delta}})/h] \\
\hline
\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright (\mathcal{E}, \ell: \bar{v}_{H}.T) = (\mathcal{E}', \ell: \bar{v}_{H}.T') \in [(\mathcal{K}', \ell: \mathcal{C}) \Rightarrow h.D]
\end{aligned}
$$

It is now straightforward to show that the dependent interpretation functions are well-behaved when supplied with a well-formed eliminator specification.

**Lemma 6.4.4 (Dependent interpretation).** Let $\Gamma \gg \Delta = \Delta'$ tel, $\Gamma \gg \Delta \blacktriangleright \mathcal{K} = \mathcal{K}'$ spec, $\Gamma, \Delta, h: \text{Ind}_{\mathcal{K}}^{\Delta}(\bar{v}_{\Delta}) \gg D = D'$ type, and $\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} = \mathcal{E}' \in [\mathcal{K} \Rightarrow h.D]$ be given. Then the following rules are validated.

$$
\begin{aligned}
\frac{\Gamma \gg \Delta \mid \mathcal{K} \blacktriangleright \Theta = \Theta' \text{ actx} \quad \Gamma \gg \chi = \chi' \in (\Theta)_{\mathcal{K}}^{\Delta}}{\Gamma \gg (\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi) = (\Theta')_{\mathcal{K}',\mathcal{E}'}^{\Delta'.h.D'}(\chi') \text{ tel}} \\
\frac{\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright A = A' \text{ atype}}{\Gamma \gg \chi = \chi' \in (\Theta)_{\mathcal{K}}^{\Delta} \quad \Gamma \gg \rho = \rho' \in (\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi) \quad \Gamma \gg M = M' \in (A)_{\mathcal{K}}^{\Delta}(\chi)} \\
\hline
\Gamma \gg (\Theta.A)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi; \rho; M) = (\Theta.A')_{\mathcal{K}',\mathcal{E}'}^{\Delta'.h.D'}(\chi'; \rho'; M') \text{ type}
\end{aligned}
$$