Shulman

18–7

for any sinister $\mu : p \to q$, the functor $\mathcal{D}^{\mu^{\dagger}}$ has a dependent right adjoint [4], i.e. there is a pullback square

$$\begin{array}{c} (\mathcal{D}^{\mu^{\dagger}})^* \mathrm{Tm}_q \longrightarrow \mathrm{Tm}_p \\ (\mathcal{D}^{\mu^{\dagger}})^* \tau_q \Big\downarrow \quad \text{↵} \quad \Big\downarrow \tau_p \\ (\mathcal{D}^{\mu^{\dagger}})^* \mathrm{Ty}_q \longrightarrow \mathrm{Ty}_p. \end{array}$$

Example 3.6 Let $\mathcal{M}$ be the adjoint mode theory for Two-Level Type Theory from Example 2.5, and let $\mathcal{C}$ be a two-level model as in [1, Definition 2.8]. If we ignore universes, this means it has two natural models $\tau^{\mathrm{f}} : \mathrm{Tm}^{\mathrm{f}} \to \mathrm{Ty}^{\mathrm{f}}$ and $\tau^{\mathrm{e}} : \mathrm{Tm}^{\mathrm{e}} \to \mathrm{Ty}^{\mathrm{e}}$, and that $\tau^{\mathrm{f}}$ is a pullback of $\tau^{\mathrm{e}}$. Let $\mathcal{D} : \mathcal{M}^{\mathrm{coop}} \to \mathcal{C}at$ be constant at $\mathcal{C}$, but where $\mathcal{D}_{\mathrm{f}} = \mathcal{C}$ is equipped with $\tau^{\mathrm{f}}$ while $\mathcal{D}_{\mathrm{e}} = \mathcal{C}$ is equipped with $\tau^{\mathrm{e}}$. This is an adjoint modal natural model with negative modalities, since the assumption that $\tau^{\mathrm{f}}$ is a pullback of $\tau^{\mathrm{e}}$ says exactly that the identity functor $(\mathcal{C}, \tau^{\mathrm{e}}) \to (\mathcal{C}, \tau^{\mathrm{f}})$ has a dependent right adjoint.

## 4 Co-dextrification

Assumption 4.1 For all of this section, let $\mathcal{L}$ be an arbitrary 2-category, let $\mathcal{C} : \mathcal{L} \to \mathcal{C}at$ be a pseudo-functor, and let $\kappa$ be an infinite regular cardinal such that $\mathcal{L}$ is $\kappa$-small, each category $\mathcal{C}_p$ has $\kappa$-small limits, and each functor $\mathcal{C}_{\mu} : \mathcal{C}_p \to \mathcal{C}_q$ preserves $\kappa$-small limits. Often, $\kappa$ will be $\omega$.

Definition 4.2 For $r \in \mathcal{L}$, let $\mathcal{L} \mathbin{//} r$ denote the lax slice 2-category:

- Its objects are morphisms $\mu : p \to r$ in $\mathcal{L}$.
- Its morphisms from $\mu : p \to r$ to $\nu : q \to r$ are pairs $(\varrho : p \to q, \alpha : \mu \Rightarrow \nu \circ \varrho)$.
- Its 2-cells from $(\varrho, \alpha)$ to $(\sigma, \beta)$ are 2-cells $\gamma : \varrho \Rightarrow \sigma$ such that $(\nu \triangleleft \gamma) \circ \alpha = \beta$.

By postcomposition, we have a 2-functor $\mathcal{L} \mathbin{//} - : \mathcal{L} \to 2\text{-}\mathcal{C}at$, with projection functors $\pi_r : \mathcal{L} \mathbin{//} r \to \mathcal{L}$.

Definition 4.3 For $r \in \mathcal{L}$, let $\widehat{\mathcal{C}}_r$ denote the oplax limit of the $(\mathcal{L} \mathbin{//} r)$-shaped diagram $\mathcal{C} \circ \pi_r : \mathcal{L} \mathbin{//} r \to \mathcal{C}at$ in $\mathcal{C}at$. Thus, an object $\Gamma \in \widehat{\mathcal{C}}_r$ consists of:

(i) For each $\mu : p \to r$ in $\mathcal{L}$, an object $\Gamma^{\mu} \in \mathcal{C}_p$.
(ii) For each $\varrho : p \to q$ and $\alpha : \mu \Rightarrow \nu \circ \varrho$, a morphism $\Gamma^{\alpha} : \Gamma^{\nu} \longrightarrow \mathcal{C}_{\varrho}(\Gamma^{\mu})$ in $\mathcal{C}_q$. (The notation is abusive, as $\Gamma^{\alpha}$ depends not just on $\alpha$ but on the decomposition of its codomain as a composite.)
(iii) For $\alpha = 1_{\mu} : \mu \Rightarrow \mu \circ 1_p$, we have $\Gamma^{1_{\mu}} = 1_{\Gamma^{\mu}}$.
(iv) For $\alpha : \mu \Rightarrow \nu \circ \varrho$ and $\beta : \nu \Rightarrow \varpi \circ \sigma$, we have $\mathcal{C}_{\sigma}(\Gamma^{\alpha}) \circ \Gamma^{\beta} = \Gamma^{(\beta \circ \varrho) \circ \alpha}$, modulo pseudofunctoriality.
(v) For $\alpha : \mu \Rightarrow \nu \circ \varrho$ and $\beta : \varrho \Rightarrow \sigma$, we have $\mathcal{C}_{\beta}(\Gamma^{\mu}) \circ \Gamma^{\alpha} = \Gamma^{(\nu \triangleleft \beta) \circ \alpha}$.

Similarly, a morphism $\boldsymbol{\theta} : \boldsymbol{\Gamma} \to \boldsymbol{\Delta}$ in $\widehat{\mathcal{C}}_r$ consists of:

(vi) For each $\mu : p \to r$, a morphism $\boldsymbol{\theta}^{\mu} : \boldsymbol{\Gamma}^{\mu} \to \boldsymbol{\Delta}^{\mu}$.

(vii) For $\alpha : \mu \Rightarrow \nu \circ \varrho$, we have $\mathcal{C}_{\varrho}(\boldsymbol{\theta}^{\mu}) \circ \boldsymbol{\Gamma}^{\alpha} = \boldsymbol{\Delta}^{\alpha} \circ \boldsymbol{\theta}^{\nu}$.

Lemma 4.4 The categories $\widehat{\mathcal{C}}_p$ are the action on objects of a modal context structure $\widehat{\mathcal{C}} : \mathcal{L}^{\mathrm{coop}} \to \mathcal{C}at$.

Proof. The functorial action is by composition: $(\widehat{\mathcal{C}}^{\mu}(\Gamma))^{\nu} = \Gamma^{\mu \circ \nu}$ and $(\widehat{\mathcal{C}}^{\beta}(\Gamma))^{\varrho} = \Gamma^{\beta \circ \varrho}$.

For $\mu : p \to q$, write $\mathsf{L}^{\mu} : \widehat{\mathcal{C}}_q \to \mathcal{C}_p$ for the functor defined by $\mathsf{L}^{\mu}(\Gamma) = \Gamma^{\mu}$.

Lemma 4.5 Each $\widehat{\mathcal{C}}_p$ has $\kappa$-small limits, and each functor $\mathsf{L}^{\mu}$ and $\widehat{\mathcal{C}}^{\mu}$ preserves them. Furthermore:

(i) If each $\mathcal{C}_p$ has some shape of colimits, then so does each $\widehat{\mathcal{C}}_p$, and each $\mathsf{L}^{\mu}$ and $\widehat{\mathcal{C}}^{\mu}$ preserves them.
(ii) If each $\mathcal{C}_p$ is locally cartesian closed or an elementary topos, so is each $\widehat{\mathcal{C}}_p$.
(iii) If each $\mathcal{C}_p$ is locally presentable, and each $\mathcal{C}_{\mu}$ is accessible, then each $\widehat{\mathcal{C}}_p$ is also locally presentable.
(iv) If each $\mathcal{C}_p$ is a Grothendieck topos, and each $\mathcal{C}_{\mu}$ is an inverse or direct image, then so is each $\widehat{\mathcal{C}}_p$.