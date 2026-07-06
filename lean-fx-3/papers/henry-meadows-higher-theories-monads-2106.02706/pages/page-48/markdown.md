*Proof.* Up to equivalence of $\infty$-categories, one can assume that $\mathcal{C}$ is a full subcategory of $\mathcal{D}$, in which case $\operatorname{Fun}(\mathcal{E}, \mathcal{C})$ is isomorphic (as a simplicial) set to the full subcategory of $\operatorname{Fun}(\mathcal{E}, \mathcal{D})$ of functors that sends all objects of $\mathcal{E}$ to $\mathcal{D}$.

Suppose that $\mathcal{B} \subseteq \mathcal{S}$ is either Set, Gpd. We write $\mu_{\mathcal{B}}^{(-)} \dashv \operatorname{Th}_{\mathcal{B}}$ for the adjunction of 5.9 coming from the inclusion of arities $\operatorname{Fin} \subseteq \mathcal{B}$.

**Theorem 8.9.** *Let $\mathcal{B} \subsetneq \mathcal{S}$ be as above. Let $\mathcal{O}^{\otimes}$ be a non-colored $\infty$-operad. Suppose that the free algebra functor $\mathcal{S} \rightarrow \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{S})$ takes elements of $\mathcal{B}$ to $\operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B})$. Then there exists a theory $(\operatorname{Fin} \rightarrow \mathcal{K}) \in \mathbf{PreTh}_{\operatorname{Fin}}$, so that*

$$\mathcal{S}^{\mu_{\mathcal{S}}^{\mathcal{K}}} \simeq \operatorname{Mod}_{\mathcal{K}}(\mathcal{S}) \simeq \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{S}) \qquad \mathcal{B}^{\mu_{\mathcal{B}}^{\mathcal{K}}} \simeq \operatorname{Mod}_{\mathcal{K}}(\mathcal{B}) \simeq \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}).$$

*Moreover, $\operatorname{Fin} \rightarrow \mathcal{K}$ is a theory with respect to both for $\operatorname{Fin} \subset \mathcal{S}$ and $\operatorname{Fin} \subset \mathcal{B}$.*

*Remark 8.10.* Note that in particular, if $\mathcal{B}$ is a 1-category, i.e. when $\mathcal{B} = \operatorname{Set}$, then $\mathcal{K}$ is a 1-category. To see this, note that $\operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B})$ can be identified with a full subcategory of $\operatorname{Fun}(\mathcal{O}^{\otimes}, \mathcal{B})$ by [16, Proposition 2.4.1.7], and is hence a 1-category by [15, Corollary 2.3.4.20]. But $\mathcal{K}$ is by definition a full subcategory of $\operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B})$, so the result follows. Similarly, if $\mathcal{B}$ is a 2-category, or rather a $(2, 1)$-category, i.e. when $\mathcal{B} = \operatorname{Gpd}$, then $\mathcal{K}$ is also itself a 2-category.

*Proof.* Let $\mathcal{S}^{\otimes} \rightarrow N(\operatorname{Fin}_{*})$ and $\mathcal{B}^{\otimes} \rightarrow N(\operatorname{Fin}_{*})$ be the $\infty$-operads corresponding to the cartesian monoidal structure on $\mathcal{S}$ and $\mathcal{B}$ (as explained in section 2.1.1 of [16]).

Consider the diagram

$$\begin{array}{ccc} \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}) & \longrightarrow & \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{S}) \\ F_1 \downarrow & & F_2 \downarrow \\ \mathcal{B} & \longrightarrow & \mathcal{S} \end{array} \quad (6)$$

First, we note that the top horizontal map is fully faithful. Indeed, the categories of $\mathcal{O}$-algebras are full subcategory of the categories of functor $\operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{B}^{\otimes})$ and $\operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{S}^{\otimes})$ over $\operatorname{Fin}_{*}$. But the functor $\operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{B}^{\otimes}) \rightarrow \operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{S}^{\otimes})$ is fully faithful because it is a pullback of $\operatorname{Fun}(\mathcal{O}^{\otimes}, \mathcal{B}^{\otimes}) \rightarrow \operatorname{Fun}(\mathcal{O}^{\otimes}, \mathcal{S}^{\otimes})$ which is fully faithfull by 8.8.

48