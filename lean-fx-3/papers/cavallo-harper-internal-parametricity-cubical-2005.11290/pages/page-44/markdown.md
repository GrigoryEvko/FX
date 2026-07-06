5:44

E. CAVALLO AND R. HARPER

Vol. 17:4

We defer serious metatheoretic analysis of the formalism we present, such as normalization or decidability of equality, to future work.

5.1. The bridge interval. The main novelty is our treatment of bridge interval restriction. Rather than relying on an operation $-\backslash r$ on raw contexts—which would destroy the algebraic character of the theory—we treat context restriction as a primitive context-forming operation.

$$\begin{array}{c c c c} \text {CTX - NIL} & \text {CTX - TERM} & \text {CTX - I} & \text {CTX - RESTRICT} \\ \hline \cdot \text {ctx} & \frac {\Gamma \vdash A \text {type}}{\Gamma . A \text {ctx}} & \frac {\Gamma \text {ctx}}{\Gamma . I \text {ctx}} & \frac {\Gamma \text {ctx} \quad \Gamma \vdash r : I}{\Gamma . \backslash r \text {ctx}} \end{array}$$

As is usual for ordinary terms, interval terms include variables and are closed under (explicit) substitutions. We defer the matter of the constants 0 and 1 for the moment.

$$\frac {\mathbf {I} \text {-VAR}}{\Gamma . \mathbf {I} \vdash \mathbf {q} _ {\mathbf {I}} : \mathbf {I}} \quad \frac {\Delta \vdash r : \mathbf {I} \quad \Gamma \vdash \delta : \Delta}{\Gamma \vdash r [ \delta ] : \mathbf {I}}$$

Restriction is characterized by its relationship with extension by a bridge interval variable. Given an interval term $\Gamma \vdash r: \mathbf{I}$ and substitution $\Gamma \backslash r \vdash \delta: \Delta$, we may build a substitution $\Gamma \vdash \delta.r: \Delta.\mathbf{I}$. Conversely, given $\Gamma \vdash \delta: \Delta.\mathbf{I}$, we may project a term $\Gamma \vdash \mathbf{q}_{\mathbf{I}}[\delta]: \mathbf{I}$ and substitution $\Gamma \backslash \mathbf{q}_{\mathbf{I}}[\delta] \vdash \delta^{\dagger}: \Delta$. This sets up an adjunction between the category of contexts $\Gamma$ and its slice over the bridge interval, which is to say the category of substitutions $\Gamma \vdash r: \mathbf{I}$, with $-\backslash-$ as the left adjoint and $-\cdot.\mathbf{I}$ as the right.

$$\begin{array}{c c} \text {SUBST - I} & \text {SUBST - RESTRICT} \\ \frac {\Gamma \vdash r : \mathbf {I} \quad \Gamma . \backslash r \vdash \delta : \Delta}{\Gamma \vdash \delta . r : \Delta . \mathbf {I}} & \frac {\Gamma \vdash \delta : \Delta . \mathbf {I}}{\Gamma . \backslash q _ {\mathbf {I}} [ \delta ] \vdash \delta^ {\dagger} : \Delta} \end{array}$$

$$\begin{array}{c c} \text {SUBST - EQ - I} & \text {SUBST - EQ - RESTRICT} \\ \Delta \text {ctx} \quad \Gamma \vdash \delta : \Delta . \mathbf {I} & \frac {\Gamma \vdash r : \mathbf {I} \quad \Gamma . \backslash r \vdash \delta : \Delta}{\Gamma . \backslash r \vdash \delta = (\delta . r) ^ {\dagger} : \Delta} \\ \hline \Gamma \vdash \delta = \delta^ {\dagger}. q _ {\mathbf {I}} [ \delta ]: \Delta . \mathbf {I} & \end{array}$$

These rules induce a functorial action by interval extension, $\Gamma.\mathbf{I}\vdash\delta^{\mathbf{I}}:=(\delta\circ\mathrm{id}^{\dagger}).\mathbf{q}_{\mathbf{I}}:\Delta.\mathbf{I}$, as well as an action by restriction, $\Gamma.\backslash r[\delta]\vdash\delta\backslash r:=(\mathrm{id}.r\circ\delta)^{\dagger}:\Delta.\backslash r$. Using these, we additionally require that the correspondence is natural.

$$\begin{array}{c c} \text {SUBST - I - NATURAL} & \text {SUBST - RESTRICT - NATURAL} \\ \frac {\Gamma \vdash \delta : \Delta \quad \Xi \vdash r : \mathbf {I} \quad \Xi . \backslash r \vdash \gamma : \Gamma}{\Xi \vdash (\delta \circ \gamma) . r = \delta^ {\mathbf {I}} \circ (\gamma . r) : \Delta . \mathbf {I}} & \frac {\Gamma \vdash \delta : \Delta . \mathbf {I} \quad \Xi \vdash \gamma : \Gamma}{\Xi . \backslash q _ {\mathbf {I}} [ \delta \circ \gamma ] \vdash (\delta \circ \gamma) ^ {\dagger} = \delta^ {\dagger} \circ (\gamma \backslash q _ {\mathbf {I}} [ \delta ]) : \Delta} \end{array}$$

The structural laws and constants are then given as generating substitutions (together with the expected equations between them, such as $p_{I} \circ \varepsilon_{I} = id$ and naturality laws).

$$\begin{array}{c c} \text {SUBST - FACE} & \text {SUBST - DEGEN} \\ \varepsilon \in \{0, 1 \} & \frac {\Gamma . \mathbf {I} \vdash p _ {\mathbf {I}} : \Gamma}{\Gamma . \mathbf {I} \vdash p _ {\mathbf {I}} : \Gamma} \end{array} \quad \begin{array}{c c} \text {SUBST - EXCHANGE} \\ \frac {\Gamma \text {ctx}}{\Gamma . \mathbf {I} . \mathbf {I} \vdash \mathrm{ex} _ {\mathbf {I}} : \Gamma . \mathbf {I} . \mathbf {I}} \end{array}$$

Note that the existence of a substitution $\Gamma \vdash \varepsilon_{\mathbf{I}}: \Gamma.\mathbf{I}$ is slightly stronger than the existence of a term $\Gamma \vdash \overline{\varepsilon_{\mathbf{I}}}: \mathbf{I}$; the latter would only give us a substitution $\Gamma \vdash \mathrm{id}.\overline{\varepsilon_{\mathbf{I}}}: \Gamma.\backslash q_{\mathbf{I}}[\overline{\varepsilon_{\mathbf{I}}}].\mathbf{I}$.

We note that the rules for I we have presented so far are consistent with an interpretation by a structural interval, in which case context restriction would be the identity function. It