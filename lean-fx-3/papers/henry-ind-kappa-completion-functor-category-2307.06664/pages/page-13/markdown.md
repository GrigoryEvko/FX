a sequence of categories indexed by $\alpha^{\mathrm{op}}$, whose transition maps are cartesians fibrations. We need to show that the inclusion

$$\operatorname*{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma} \subset \operatorname*{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$$

identifies the right-hand side with the $\operatorname{Ind}_{\kappa}$ completion of the left-hand side. The proof has three parts: first one shows that the objects of $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma}$ are $\kappa$-presentable in the right hand side, mostly using the same sort of argument as in Proposition 2.1, the second step is to show that the functor

$$E: \operatorname{Ind}_{\kappa} \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma} \to \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$$

is fully faithful, using the exact same argument as in Corollary 2.2, and finally the third step is to show that this functor is essentially surjective, that is that every object of $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$ is a $\kappa$-filtered colimits of objects of $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma}$. Here the argument is to show that for all $Y$ in the limits, the diagram of all the $X \to Y$ with $X \in \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma}$ is $\kappa$-filtered and has colimit $Y$.

For the first part, we observe that in the limit $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$, all the transition functors preserve $\kappa$-filtered colimits, so all $\kappa$-filtered colimits are computed componentwise. The Hom set in the limits can be written as a $\kappa$-small limit

$$\operatorname{Hom}(X, Y) = \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Hom}(X_{\gamma}, Y_{\gamma}).$$

So, if for all $\gamma$, the objects $X_{\gamma}$ is in $\mathcal{C}_{\gamma}$, and hence $\kappa$-presentable, then each individual Hom functor preserves $\kappa$-filtered colimits in the second variable, and the limits being $\kappa$-small, it comutes to $\kappa$-filtered colimits, hence $\operatorname{Hom}(X, \cdot)$ preserves $\kappa$-filtered colimits. So that $(X_{\gamma}) \in \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$ is $\kappa$-presentable.

For the second part, we can just run the exact same argument as in Corollary 2.2. The functor $E$ preserves $\kappa$-filtered colimits by construction, and so we can do the exact same computation as in the proof of Corollary 2.2 to conclude that the functor $E$ is fully faithful.

Moving to the third part, we show that for any

$$Y = (Y_{\gamma})_{\gamma \in \alpha^{\mathrm{op}}} \in \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$$

the category of $X \to Y$ with $X_{\gamma} \in \mathcal{C}_{\gamma}$ is $\kappa$-filtered. So let $X^{(i)}$ be a $\kappa$-small diagram of such objects. We construct a cocone for it, that is a factorization $X^{(i)} \to E \to Y$ where all $E_{\gamma} \in \mathcal{C}_{\gamma}$ and the first arrow is natural in $i$. This is done by induction on $\gamma$. Indeed assuming such an $E_{\beta}$ has been constructed for all $\beta < \gamma$, that is we have our (natural) factorization $X^{(i)} \to E \to Y$ in the category $\operatorname{Lim}_{\beta < \gamma} \mathcal{C}_{\beta}$. First, as $Y_{\gamma} \in \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$, exists an object $E_{\gamma}^{0} \in \mathcal{C}_{\gamma}$ that factors the cocone $X_{\gamma}^{(i)} \to E_{\gamma}^{0} \to Y_{\gamma}$. The functor $\pi: \operatorname{Ind}_{\kappa} \mathcal{C}_{\gamma} \to \operatorname{Lim}_{\beta < \gamma} \operatorname{Ind}_{\kappa} \mathcal{C}_{\beta}$ preserves $\kappa$-filtered colimits, so we can further “enlarge” $E_{\gamma}^{0}$ so that its image $\pi(E_{\gamma}^{0})$ in this limit also factors the already existing map

$$X^{(i)} \to E \to \pi(E_{\gamma}^{0}) \to Y$$

while making sure that the composite $X^{(i)} \to E \to \pi(E_{\gamma}^{0})$ identifies with the image under $\pi$ of the cocone structure $X_{\gamma}^{(i)} \to E_{\gamma}^{0}$. Finally, we construct $E_{\gamma}$

13