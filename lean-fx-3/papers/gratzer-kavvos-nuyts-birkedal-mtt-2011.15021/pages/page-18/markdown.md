11:18

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

$$\boxed{\Gamma \vdash \gamma = \delta : \Delta @ m}$$

$$\begin{array}{c} \Gamma_0, \Gamma_1 \text{ ctx } @ n \qquad \Delta \text{ ctx } @ n \qquad \Delta . \mathbf{\Omega}_\mu \vdash A \text{ type}_1 @ m \\ \mu : \text{Hom}_{\mathcal{M}}(m, n) \qquad \Gamma_0 \vdash \gamma : \Gamma_1 @ n \qquad \Gamma_1 \vdash \delta : \Delta @ n \qquad \Gamma_1 . \mathbf{\Omega}_\mu \vdash M : A[\delta . \mathbf{\Omega}_\mu] @ m \\ \hline \Gamma_0 \vdash (\delta . M) \circ \gamma = (\delta \circ \gamma) . M[\gamma . \mathbf{\Omega}_\mu] : \Delta . (\mu \mid A) @ n \end{array}$$

$$\frac{\Gamma, \Delta \text{ ctx } @ o \qquad \mu : \text{Hom}_{\mathcal{M}}(m, n) \qquad \nu : \text{Hom}_{\mathcal{M}}(n, o) \qquad \Gamma \vdash \delta : \Delta @ m}{\Gamma . \mathbf{\Omega}_{\nu \circ \mu} \vdash \delta . \mathbf{\Omega}_{\nu \circ \mu} = \delta . \mathbf{\Omega}_\nu . \mathbf{\Omega}_\mu : \Delta . \mathbf{\Omega}_{\nu \circ \mu} @ m}$$

$$\frac{\Gamma, \Delta \text{ ctx } @ m \qquad \Gamma \vdash \delta : \Delta @ m}{\Gamma \vdash \delta . \mathbf{\Omega}_1 = \delta : \Delta @ m} \qquad \frac{\Gamma \text{ ctx } @ n \qquad \mu : \text{Hom}_{\mathcal{M}}(m, n)}{\Gamma . \mathbf{\Omega}_\mu \vdash \text{id} . \mathbf{\Omega}_\mu = \text{id} : \Gamma . \mathbf{\Omega}_\mu @ m}$$

$$\frac{\Gamma, \Delta, \Xi \text{ ctx } @ n \qquad \mu : \text{Hom}_{\mathcal{M}}(m, n) \qquad \Gamma \vdash \delta : \Delta @ n \qquad \Delta \vdash \xi : \Xi @ n}{\Gamma . \mathbf{\Omega}_\mu \vdash (\xi \circ \delta) . \mathbf{\Omega}_\mu = \xi . \mathbf{\Omega}_\mu \circ \delta . \mathbf{\Omega}_\mu : \Xi . \mathbf{\Omega}_\mu @ m}$$

$$\frac{\Gamma \text{ ctx } @ n \qquad \mu : \text{Hom}_{\mathcal{M}}(m, n)}{\Gamma . \mathbf{\Omega}_\mu \vdash \text{id} = \mathbf{\alpha}_{\Gamma}^{1_\mu} : \Gamma . \mathbf{\Omega}_\mu @ m}$$

$$\frac{\Gamma, \Delta \text{ ctx } @ n \qquad \mu, \nu : \text{Hom}_{\mathcal{M}}(m, n) \qquad \Gamma \vdash \delta : \Delta @ n \qquad \alpha : \nu \Rightarrow \mu}{\Gamma . \mathbf{\Omega}_\mu \vdash \mathbf{\alpha}_{\Gamma}^\alpha \circ (\delta . \mathbf{\Omega}_\mu) = (\delta . \mathbf{\Omega}_\nu) \circ \mathbf{\alpha}_{\Delta}^\alpha : \Delta . \mathbf{\Omega}_\nu @ m}$$

$$\frac{\Gamma \text{ ctx } @ m \qquad \mu_0, \mu_1, \mu_2 : \text{Hom}_{\mathcal{M}}(n, m) \qquad \alpha_0 : \mu_0 \Rightarrow \mu_1 \qquad \alpha_1 : \mu_1 \Rightarrow \mu_2}{\Gamma . \mathbf{\Omega}_{\mu_2} \vdash \mathbf{\alpha}_{\Gamma}^{\alpha_1 \circ \alpha_0} = \mathbf{\alpha}_{\Gamma}^{\alpha_0} \circ \mathbf{\alpha}_{\Gamma}^{\alpha_1} : \Gamma . \mathbf{\Omega}_{\mu_0} @ n}$$

$$\frac{\Gamma \text{ ctx } @ m \qquad \nu_0, \nu_1 : \text{Hom}_{\mathcal{M}}(o, n) \qquad \mu_0, \mu_1 : \text{Hom}_{\mathcal{M}}(n, m) \qquad \beta : \nu_0 \Rightarrow \nu_1 \qquad \alpha : \mu_0 \Rightarrow \mu_1}{\Gamma . \mathbf{\Omega}_{\mu_0 \circ \nu_0} \vdash \mathbf{\alpha}_{\Gamma}^{\alpha * \beta} = \mathbf{\alpha}_{\Gamma}^{\alpha} . \mathbf{\Omega}_{\nu_1} \circ \mathbf{\alpha}_{\Gamma . \mathbf{\Omega}_{\mu_0}}^{\beta} : \Gamma . \mathbf{\Omega}_{\mu_1 \circ \nu_1} @ o}$$

Figure 9: Equality of Substitutions

**Modal substitutions.** In addition to the usual rules, MTT features substitutions corresponding to the 1-cells and 2-cells of the mode theory. First, recall that for each modality $\mu : n \to m$ we have the operation $\mathbf{\Omega}_\mu$ on contexts. Its action extends to substitutions:

$$\frac{\text{SB/LOCK}}{\mu : n \to m \qquad \Gamma \vdash \delta : \Delta @ m} \\ \frac{\Gamma . \mathbf{\Omega}_\mu \vdash \delta . \mathbf{\Omega}_\mu : \Delta . \mathbf{\Omega}_\mu @ n}{}$$

Second, each 2-cell $\alpha : \mu \Rightarrow \nu$ induces a *natural transformation* between $\mathbf{\Omega}_\nu$ and $\mathbf{\Omega}_\mu$, whose component at $\Gamma$ is the 'key' substitution

$$\frac{\text{SB/KEY}}{\frac{\alpha : \mu \Rightarrow \nu}{\Gamma . \mathbf{\Omega}_\nu \vdash \mathbf{\alpha}_{\Gamma}^\alpha : \Gamma . \mathbf{\Omega}_\mu @ n}}$$

Recalling that $\mathcal{M}^{\text{coop}}$ is the 2-category with morphisms and 2-cells opposite from $\mathcal{M}$, we see that these substitutions come with equations postulating that $-\mathbf{\Omega}_\mu$ is a functor, $\mathbf{\alpha}_{\Gamma}^\alpha$ is a natural transformation, and that together they form a 2-functor $\mathcal{M}^{\text{coop}} \to \mathbf{Cat}$. As a consequence, our type theory is forced to contain a calculus of (strict) 2-categories. Indeed,