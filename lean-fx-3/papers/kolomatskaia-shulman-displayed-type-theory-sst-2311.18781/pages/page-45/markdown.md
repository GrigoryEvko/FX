(i.e. judgment) X, morphisms $\mathcal{X} \to P_{\mathrm{pr}}(X)$ (i.e. elements of the presheaf $P_{\mathrm{pr}}(X)$) are bijectively related to pairs consisting of a type $A \in \mathrm{Ty}(\Gamma)$ in context $\Gamma$ and a morphism $\mathcal{X}(\gamma : \Gamma, a : A\gamma) \to X$ (i.e. an element of $X(\gamma : \Gamma, a : A\gamma)$). In syntax, this is a bidirectional rule, indicating a bijection between the data above and below the lines:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type } \quad \gamma : \Gamma, a : A \gamma \vdash \xi \gamma a : X}{\gamma : \Gamma \vdash \bar{\xi} \gamma : P_{\mathrm{pr}}(X)}$$

Thus, for instance, $P_{\mathrm{pr}_{\ell_0}}(\mathrm{Ty}_{\ell_1})$ represents families of types of level $\ell_1$ indexed by a type of level $\ell_0$. Therefore, formation rules such as those for $\Pi$-types and $\Sigma$-types:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash (\Pi A B) \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash (\Sigma A B) \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

are represented by morphisms $\Pi, \Sigma : P_{\mathrm{pr}_{\ell_0}}(\mathrm{Ty}_{\ell_1}) \to \mathrm{Ty}_{\ell_0 \sqcup \ell_1}$.

The rules for terms can also be represented in this language. For instance, a natural model has $\Pi$-types if and only if there is a pullback square

$$\begin{array}{ccc} P_{\mathrm{pr}_{\ell_0}}(\mathrm{Tm}_{\ell_1}) & \longrightarrow & \mathrm{Tm}_{\ell_0 \sqcup \ell_1} \\ P_{\mathrm{pr}_{\ell_0}}(\mathrm{pr}_{\ell_1}) \downarrow & \downarrow & \downarrow \mathrm{pr}_{\ell_0 \sqcup \ell_1} \\ P_{\mathrm{pr}_{\ell_0}}(\mathrm{Ty}_{\ell_1}) & \xrightarrow[\Pi]{} & \mathrm{Ty}_{\ell_0 \sqcup \ell_1}, \end{array}$$

meaning that there is a bijection

$$\frac{\gamma : \Gamma, a : A \gamma \vdash t \gamma a : B \gamma a}{\gamma : \Gamma \vdash (\lambda t) \gamma : (\Pi A B) \gamma}$$

Polynomial functors can also be composed, yielding another polynomial functor. For instance, in a CwF without levels, $P_{\mathrm{pr}} \circ P_{\mathrm{pr}}$ is the functor such that $(P_{\mathrm{pr}} \circ P_{\mathrm{pr}})(X)$ represents elements of $X$ in a doubly-extended context ($\gamma : \Gamma, a : A\gamma, b : B\gamma a$), which means that it is the polynomial functor associated to the map $\mathrm{pr}^2 : \mathrm{Tm}^2 \to P_{\mathrm{pr}}(\mathrm{Ty})$ where the fiber of $\mathrm{Tm}^2(\Gamma)$ over $(A, B)$ consists of a pair of terms $\gamma : \Gamma \vdash a : A\gamma$ and $\gamma : \Gamma \vdash b : B\gamma a$. In particular, a CwF $\mathcal{C}$ has $\Sigma$-types if and only if $\Sigma : P_{\mathrm{pr}}(\mathrm{Ty}) \to \mathrm{Ty}$ represents any such pair by a single term, i.e. there is a pullback square

$$\begin{array}{ccc} \mathrm{Tm}^2 & \longrightarrow & \mathrm{Tm} \\ \mathrm{pr}^2 \downarrow & \downarrow & \downarrow \mathrm{pr} \\ P_{\mathrm{pr}}(\mathrm{Ty}) & \xrightarrow[\Sigma]{} & \mathrm{Ty}, \end{array}$$

This is equivalent to a (cartesian) morphism of polynomial functors $P_{\mathrm{pr}} \circ P_{\mathrm{pr}} \to P_{\mathrm{pr}}$. Of course, there is an analogous version for a CwF with levels.

45