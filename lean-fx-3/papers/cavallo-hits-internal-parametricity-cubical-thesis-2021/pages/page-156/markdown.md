144

General higher inductive types

$$\frac{\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright \theta = \theta' \in \Theta \qquad \Gamma \gg \chi = \chi' \in (\Theta')_{\mathcal{K}}^{\Delta} \qquad \Gamma \gg \rho = \rho' \in (\Theta')_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi)}{\Gamma \gg (\Theta'.\theta)_{\Delta.h.D}^{\mathcal{K},\mathcal{E}}(\chi; \rho) = (\Theta'.\theta')_{\Delta'.h.D'}^{\mathcal{K}',\mathcal{E}'}(\chi'; \rho') \in (\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi)}$$

$$\frac{\Gamma \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \mathrm{M} = \mathrm{M}' \in \mathrm{A} \qquad \Gamma \gg \chi = \chi' \in (\Theta)_{\mathcal{K}}^{\Delta} \qquad \Gamma \gg \rho = \rho' \in (\Theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi)}{\Gamma \gg (\mathrm{M})_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi; \rho) = (\mathrm{M}')_{\mathcal{K}',\mathcal{E}'}^{\Delta'.h.D'}(\chi'; \rho') \in (\Theta.\mathrm{A})_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi; \rho; (\mathrm{M})_{\mathcal{K}}(\chi))}$$

Proof. Simultaneously by mutual induction on the argument contexts, types, substitutions, and terms. □

Now we show that the eliminator operator itself is well-typed. For the remainder of this section we fix $\Psi \Vdash \Delta$ tel, $\Psi \Vdash \Delta \blacktriangleright \mathcal{K}$ spec, $\Psi, \Delta, h : \operatorname{Ind}_{\mathcal{K}}^{\Delta}(\overline{v}_{\Delta}) \gg D = D'$ type, and $\Psi \Vdash \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} = \mathcal{E}' \in [\mathcal{K} \Rightarrow h.D]$. As with coercion, we define a PER of values that produces well-typed results when supplied to the eliminator, then show that this PER is closed under $Step^{\mathcal{K}}$.

Definition 6.4.5 (Eliminability relation). We define a value $(\Psi, \Delta)$-PER $Elim^{-1} \subseteq Ind_{\mathcal{K}}$ by declaring $V \approx V' \in Elim^{-1}\langle \psi, \delta \rangle$ to hold for $\Psi' \Vdash (\psi, \delta) \in (\Psi, \Delta)$ whenever the following hold.

- $V \approx V' \in Ind_{\mathcal{K}}\langle \psi, \delta \rangle$.

- $\Psi' \Vdash \operatorname{elim}(\overline{v}_{\Delta}.h.D\psi; \delta; W; \mathcal{E}\psi) = \operatorname{elim}(\overline{v}_{\Delta}.h.D'\psi; \delta'; W'; \mathcal{E}'\psi) \in D\psi[\delta, W/h]$ for all pairs $W, W' \in \{V, V'\}$ and $\delta'$ with $\Psi' \Vdash \delta = \delta' \in \Delta\psi$.

Lemma 6.4.6 (Extension to terms). For any $\Psi' \Vdash \psi \in \Psi$, $\Psi' \Vdash \delta = \delta' \in \Delta\psi$, and $M \approx M' \in \Downarrow Elim^{-1}\langle \psi, \delta \rangle$, we have the following.

$$\Psi' \Vdash \operatorname{elim}(\overline{v}_{\Delta}.h.D\psi; \delta; M; \mathcal{E}\psi) = \operatorname{elim}(\overline{v}_{\Delta}.h.D'\psi; \delta'; M'; \mathcal{E}'\psi) \in D\psi[\delta, M/h]$$

Proof. By Lemma 3.1.38 and the definition of $Elim^{-1}$, as the eliminator operator is eager. □

Lemma 6.4.7 (Reduction of elim on fcoe). The following rule is validated for any substitutions $\Psi' \Vdash (\psi, \delta) \in (\Psi, \Delta)$ and $\Psi', x : \mathbb{I} \Vdash \delta' \in \Delta\psi$ with $\Psi' \Vdash \delta'[s/x] = \delta \in \Delta\psi$.

$$\begin{array}{c c} \Psi' \Vdash r, s \in \mathbb{I} & M \in \Downarrow Elim^{-1}[\psi, \delta'[r/x]] \\ F_x := \operatorname{fcoe}_{x,\delta'}^{r \to x}(M) & E := \operatorname{elim}(\overline{v}_{\Delta}.h.D\psi; \delta'[r/x]; M; \mathcal{E}\psi) \\ \hline \Psi' \Vdash \operatorname{elim}(\overline{v}_{\Delta}.h.D\psi; \delta; F_s; \mathcal{E}\psi) = \operatorname{coe}_{x,D\psi[\delta',F_s/h]}^{r \to s}(E) \in D[\delta, F_s/h] \end{array}$$

Proof. Note that $\Psi' \Vdash E \in D[\delta'[r/x], M/h]$ holds by Lemma 6.4.6. We proceed by Lemma 3.1.35. For any $\Psi'' \Vdash \psi' \in \Psi'$, we are in one of two cases.