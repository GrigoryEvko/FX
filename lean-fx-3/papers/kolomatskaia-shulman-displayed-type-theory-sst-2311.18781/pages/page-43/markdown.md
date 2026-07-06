and, conversely, for $\tau : \Delta \to (\gamma : \Gamma, a : A \gamma)$, we have:

$$[ \mathrm{pt}^A \circ \tau, (\mathrm{zv}^A)^\tau ] \equiv \tau. \tag{4.4}$$

As a corollary of this we have that the following diagram is a pullback:

$$\begin{array}{c} (\delta : \Delta, a : A (\sigma \delta)) \xrightarrow{[\sigma \circ \mathrm{pt}^{A^\sigma}, \mathrm{zv}^{A^\sigma}]} (\gamma : \Gamma, a : A \gamma) \\ \mathrm{pt}^{A^\sigma} \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Delta \xrightarrow{\sigma} \Gamma \end{array}$$

So, in particular, in a CwF we have a distinguished pullback of any parent map along an arbitrary morphism, as another parent map, and this choice of pullbacks is definitionally functorial. We will often omit the superscripts from pt and zv.

The map constructed from $\sigma$ in the top row of the diagram above will occur frequently in the exposition that follows, and we shall refer to it as the weakening two of $\sigma$ by $A$. Formally, given $\sigma : \Delta \to \Gamma$, and $\gamma : \Gamma \vdash A \gamma \text{ type}_\ell$, we have:

$$W_2^A \sigma : (\theta : \Theta, a : A (\sigma \theta)) \to (\gamma : \Gamma, a : A \gamma)$$

$$W_2^A \sigma = [\sigma \circ \mathrm{pt}, \mathrm{zv}]$$

Finally, when working with hypothetical judgments in an extended context, we can also treat the variables more traditionally. Instead of $\delta : (\gamma : \Gamma, a : A \gamma) \vdash B \delta \text{ type}_{\ell_1}$, we write $\gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}$, and so on. In particular, the zero variable zv can be written more simply as

$$\gamma : \Gamma, a : A \gamma \vdash a : A \gamma$$

As before, this can be justified formally as an interpretation in the internal type theory of $\mathsf{Set}^{\mathrm{true}}$.

### 4.1.3 $\Pi$-Types

All the basic type-forming operations in syntax translate into structure on a CwF. For instance, a $\Pi$-structure on a CwF with levels consists of the following structure and properties:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_{\ell_0} \qquad \gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash (\Pi A B) \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma, a : A \gamma \vdash t \gamma a : B \gamma a}{\gamma : \Gamma \vdash (\lambda t) \gamma : (\Pi A B) \gamma}$$

$$\frac{\gamma : \Gamma \vdash f \gamma : (\Pi A B) \gamma \qquad \gamma : \Gamma \vdash s \gamma : A \gamma}{\gamma : \Gamma \vdash (\mathrm{app} f s) \gamma : B^{[1_r, s]} \gamma}$$

The above notation lets us talk about types in point-free notation, e.g. $\Pi A B : \mathsf{Ty}_\ell \Gamma$. When the explicit dependence on $\gamma$ is written, we can propagate the notation as follows:

$$(\Pi A B) \gamma \equiv (a : A \gamma) \to B \gamma a$$

$$(\lambda t) \gamma \equiv \lambda a . t \gamma a$$

$$(\mathrm{app} f s) \gamma \equiv \mathrm{app} \gamma (f \gamma) (s \gamma)$$

43