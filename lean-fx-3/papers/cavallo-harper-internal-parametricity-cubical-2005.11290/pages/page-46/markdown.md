5:46

E. CAVALLO AND R. HARPER

Vol. 17:4

$$\begin{array}{c} \Delta \vdash \gamma : \Gamma \qquad \Gamma \vdash \boldsymbol{r} : \mathbf{I} \qquad \Gamma . \backslash \boldsymbol{r}. \mathbf{I} \vdash A \text { type } \\ \Gamma . \backslash \boldsymbol{r} \vdash M_{0} : A[\mathbf{0}_{\mathbf{I}}] \qquad \Gamma . \backslash \boldsymbol{r} \vdash M_{1} : A[\mathbf{1}_{\mathbf{I}}] \qquad \Gamma . \backslash \boldsymbol{r} \vdash P : \operatorname{Bridge}_{A}(M_{0}, M_{1}) \\ \hline \Gamma \vdash (P @ \boldsymbol{r})[\gamma] = P[\gamma \backslash \boldsymbol{r}] @ \boldsymbol{r}[\gamma] : A[\operatorname{id}. \boldsymbol{r}][\gamma] \end{array}$$

Finally, the $\beta$-, $\eta$-, and boundary rules for Bridge-types can be expressed as follows. Note that these rules respectively make use of the unit $\Gamma \vdash \operatorname{id}. \boldsymbol{r} : \Gamma . \backslash \boldsymbol{r}. \mathbf{I}$ and counit $\Gamma . \mathbf{I} . \backslash \mathbf{q}_{\mathbf{I}} \vdash \operatorname{id}^{\dagger} : \Gamma$ of the adjunction between $-\backslash-$ and $-\mathbf{I}$.

$$\begin{array}{c} \frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \qquad \Gamma . \backslash \boldsymbol{r}. \mathbf{I} \vdash A \text { type } \qquad \Gamma . \backslash \boldsymbol{r}. \mathbf{I} \vdash M : A}{\Gamma \vdash \lambda . M @ \boldsymbol{r} = M[\operatorname{id}. \boldsymbol{r}] : A[\operatorname{id}. \boldsymbol{r}]} \\ \frac{\Gamma . \mathbf{I} \vdash A \text { type } \qquad \Gamma \vdash M_{0} : A[\mathbf{0}_{\mathbf{I}}] \qquad \Gamma \vdash M_{1} : A[\mathbf{1}_{\mathbf{I}}] \qquad \Gamma \vdash P : \operatorname{Bridge}_{A}(M_{0}, M_{1})}{\Gamma \vdash P = \lambda^{\mathbf{I}} . P[\operatorname{id}^{\dagger}] @ \mathbf{q}_{\mathbf{I}} : \operatorname{Bridge}_{A}(M_{0}, M_{1})} \\ \frac{\Gamma . \mathbf{I} \vdash A \text { type } \qquad \Gamma \vdash M_{0} : A[\mathbf{0}_{\mathbf{I}}] \qquad \Gamma \vdash M_{1} : A[\mathbf{1}_{\mathbf{I}}] \qquad \Gamma \vdash P : \operatorname{Bridge}_{A}(M_{0}, M_{1})}{\Gamma \vdash P[\varepsilon_{\mathbf{I}}^{\dagger}] @ \mathbf{q}_{\mathbf{I}}[\varepsilon_{\mathbf{I}}] = M_{\varepsilon} : A[\varepsilon_{\mathbf{I}}]} \end{array}$$

## 6. A SEMANTICS IN BICUBICAL SETS

We now describe a second semantics for the formal type theory of Section 5 in a presheaf category of bicubical sets, adapting Angiuli et al.'s presheaf semantics for cubical type theory [ABC$^{+}$19].

**Definition 6.1.** We define the cartesian-affine bicube category $\square_{ca}$ to have as objects interval contexts $\Psi$ and as morphisms interval substitutions $\Psi' \Vdash \psi \in \Psi$, as specified in Definition 4.1.

**Remark 6.2.** The category $\square_{ca}$ is equivalent to a product $\square_{c} \times \square_{a}$ of two cube categories, the cartesian cube category $\square_{c}$ consisting of path interval contexts and the affine cube category $\square_{a}$ consisting of bridge interval contexts.

The presheaf category $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ is the category of contravariant functors from $\square_{ca}$ to $\mathbf{Set}$, meaning that its objects are families of sets indexed by interval contexts with transition maps for each interval substitution. This parallels the situation in the computational interpretation, where types are given meaning by families of relations indexed by such contexts. We use $\mathcal{L}$ (hiragana 'yo') to denote the Yoneda embedding $\square_{ca} \to [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$.

**Remark 6.3.** Bernardy, Coquand, and Moulin instead interpret their type theory in a category of refined presheaves on $\square_{a}$ [BCM15]. Roughly, a refined presheaf is a $\Psi$-indexed family where for each $\Psi \in \square_{a}$, we have not merely a set but a $\Psi$-set, a family of sets indexed by sub-contexts $\Psi' \subseteq \Psi$. This refinement is used to validate the equivalents in their setting of equations $\operatorname{Bridge}_{\boldsymbol{x}. \operatorname{Gel}_{\boldsymbol{x}}(A_{0}, A_{1}, R)} = R$ and $C = \lambda^{\mathbf{I}} \boldsymbol{x}. \operatorname{Gel}_{\boldsymbol{x}}(A_{0}, A_{1}, \operatorname{Bridge}_{\boldsymbol{x}, C @ \boldsymbol{x}})$, as mentioned in Section 2.4. When we build parametric type theory on a cubical base, we no longer need these equations to hold exactly, as we can prove they hold up to a path using univalence (Theorem 2.4).