$\kappa$-directed family of functors $F^j : I \rightarrow I^{(\kappa)}$ such that $E = \operatorname{Colim}_j F^j$ in the category of functors $I \rightarrow \operatorname{Ind}_{\kappa}(I^{(\kappa)})$.

$\operatorname{Ind}_{\kappa}(\pi_I)$ preserves $\kappa$-filtered colimit, so we also have that

$$\operatorname{Colim}_j \operatorname{Ind}_{\kappa}(\pi_I) F^j \simeq \operatorname{Ind}_{\kappa}(\pi_I) E$$

Identify with the canonical functor $I \rightarrow \operatorname{Ind}_{\kappa}(I)$. Now, applying our assumption (A2) to (the Cauchy completion of) $I$, we see that this implies that the canonical functor $I \rightarrow \operatorname{Ind}_{\kappa}(I)$ is a $\kappa$-presentable object of the category of all such functor, and hence because of the previous colimit it has to be a retract of one of the functors $\operatorname{Ind}_{\kappa}(\pi_I)F^j$, but then all the functors involved actually takes values in $I$ and hence we have shown that the identity of $I$ is a retract of $\pi_I \circ F^j$ for some $j$, which is exactly condition (W6) of Proposition 3.4. Hence proving that $I$ is well-founded.

### 3.3 Proof of (A4) $\Rightarrow$ (A1)

We are now showing that if $I$ is well-founded and $\kappa$-small and $\mathcal{C}$ is any category, then $E_{\mathcal{C},\kappa}^I : \operatorname{Ind}_{\kappa}(\mathcal{C}^I) \rightarrow \operatorname{Ind}_{\kappa}(\mathcal{C})^I$ is an equivalence. The strategy here is to show first that, for $I$ a $\kappa$-small category and $\alpha < \kappa$ an ordinal, the functor

$$E_{\mathcal{C},\kappa}^{I^{(\alpha)}} : \operatorname{Ind}_{\kappa}(\mathcal{C}^{I^{(\alpha)}}) \rightarrow \operatorname{Ind}_{\kappa}(\mathcal{C})^{I^{(\alpha)}}$$

is an equivalence, which we achieve by induction on $\alpha$, and then we exploit that when $I$ is well-founded it is a retract of one of the $I^{(\alpha)}$ to conclude the proof.

We start with the following proposition:

**3.5 Proposition.** *Let $\alpha < \kappa$ any $\kappa$-small ordinal. Let $\mathcal{C}_{\bullet} : \alpha^{op} \rightarrow \mathbf{Cat}$ be a tower of categories with the property that for each $\gamma < \alpha$ the functor*

$$\mathcal{C}_{\gamma} \rightarrow \operatorname{Lim}_{\beta < \gamma} \mathcal{C}_{\beta}$$

*is (equivalent to a) cartesian fibration. Then the limit $\operatorname{Lim}_{\beta < \alpha} \mathcal{C}_{\beta}$ is preserved by $\operatorname{Ind}_{\kappa}$.*

**3.6 Remark.** Here by limits, we mean pseudo-limits. As the $\operatorname{Ind}_{\kappa}$ functor is only well defined up to equivalence, asking for the preservation of strict limits does not really make sense. Because of this, it does not make sense either to ask the comparison functors in the proposition to be Grothendieck cartesian fibration in the strict sense, as they are only well defined up to equivalences of categories. This is why we only require that they are equivalent to cartesian fibration (equivalently, are Street fibrations). Of course, one could take all limits to be strict limits, and then one could ask these functors to be Grothendieck fibrations. As Grothendieck fibrations are in particular isofibrations, these strict limits would be equivalent to the corresponding pseudo-limits. The $\operatorname{Ind}_{\kappa}$ functor would then preserves the strict limit up to equivalences of categories.

*Proof.* We fix $\alpha$ a $\kappa$-small ordinal and

$$\mathcal{C}_0 \leftarrow \mathcal{C}_1 \leftarrow \cdots \leftarrow \mathcal{C}_{\gamma} \leftarrow \dots$$

12