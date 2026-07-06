Further, if we have $b : \mathbb{B}^{(n),\langle m\rangle}$, then $\Gamma^b : \Gamma_n \to \Gamma_m$, and this assignment is contravariantly functorial on the nose. We also sometimes write $\gamma^b$ for $\Gamma^b \gamma$. Morphisms of simplicial objects are natural transformations. The data of $\sigma : \Delta \to \Gamma$ thus consists of a morphism $\sigma_n : \Delta_n \to \Gamma_n$ for each $n$, such that for any $b : \mathbb{B}^{(n),\langle m\rangle}$, we have:

$$\Delta^b \circ \sigma_n \equiv \sigma_m \circ \Gamma^b$$

There are two additional functors of relevance relating the truncated simplicial models at different dimensions: truncation and décalage.

$$\begin{array}{ll} \pi : \mathcal{C}^{\Delta_{n+1}^+} \to \mathcal{C}^{\Delta_n^+} & (-)^D : \mathcal{C}^{\Delta_{n+1}^+} \to \mathcal{C}^{\Delta_n^+} \\ (\pi\Gamma)_{m+1} \equiv \Gamma_{m+1} & (\Gamma^D)_{m+1} \equiv \Gamma_{m+2} \\ (\pi\Gamma)^b \equiv \Gamma^b & (\Gamma^D)^b \equiv \Gamma^{\sharp b} \\ (\pi\sigma)_{m+1} \equiv \sigma_{m+1} & (\sigma^D)_{m+1} \equiv \sigma_{m+2} \end{array}$$

There is a natural transformation between them:

$$\begin{array}{l} \rho : (-)^D \Rightarrow \pi \\ (\rho_\Gamma)_{m+1} \equiv \Gamma^{\wp 1_{(m+1)}} \end{array}$$

Note that $\rho_\Gamma : \Gamma^D \to \pi\Gamma$ is a morphism of presheaves since for $b : \mathbb{B}^{(n+1),\langle m+1\rangle}$, we have:

$$\begin{array}{l} (\pi\Gamma)^b \circ (\rho_\Gamma)_{n+1} \equiv \Gamma^b \circ \Gamma^{\wp 1_{(n+1)}} \equiv \Gamma^{\wp 1_{(n+1)}\circ b} \equiv \Gamma^{\wp(1_{(n+1)}\circ b)} \equiv \Gamma^{\wp b} \\ \equiv \Gamma^{\wp(b\circ 1_{(m+1)})} \equiv \Gamma^{\sharp b\circ \wp 1_{(m+1)}} \equiv \Gamma^{\wp 1_{(m+1)}} \circ \Gamma^{\sharp b} \equiv (\rho_\Gamma)_{m+1} \circ (\Gamma^D)^b \end{array}$$

A similar proof shows that $\rho$ is natural, as its components arise from morphisms in $\Delta_n^+$, and any morphism of presheaves must respect these.

### 4.2.3 Intuition

We will now construct the type-theoretical/fibrant structure of the truncated simplicial model. This will be done concretely through a series of mutually inductive definitions that will require substantially strengthening the inductive hypothesis for the sake of making everything well-typed.

However, before we launch into that, it would be useful to keep in mind where we are headed. At the most basic level, we would like to define the judgement

$$\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{ type}_\ell$$

A simplicial type consists entirely of the data of its discrete $m$-simplex types for $m \leqslant n + 1$, all of which live at the same level $\ell$:

$$\begin{array}{c} \gamma_{-1} : \Gamma_{-1} \vdash_{dm} A_{-1} \gamma_{-1} \text{ type}_\ell \\ \gamma_0 : \Gamma_0, \mathfrak{z}: A_{-1} \gamma_0^\wp \vdash_{dm} A_0 \gamma_0 \mathfrak{z} \text{ type}_\ell \\ \gamma_1 : \Gamma_1, \mathfrak{z}: A_{-1} \gamma_1^{\wp 0}, x_0 : A_0 \gamma_1^{\wp 1} \mathfrak{z}, x_0 : A_0 \gamma_1^{\sharp 0} \mathfrak{z} \vdash_{dm} A_1 \gamma_1 \mathfrak{z} x_0 x_0 \text{ type}_\ell \\ \vdots \end{array}$$

52