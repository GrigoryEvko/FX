5.2. CARTESIAN FIBRATIONS

This induces a square

$$\begin{array}{c} \operatorname{LCart}^{c}(C) \xrightarrow{\mathbf{R}j^{*}} \operatorname{LCart}^{c}(A) \\ \downarrow_{\mathbf{L}u} \quad \swarrow \quad \downarrow_{\mathbf{L}v} \\ \operatorname{LCart}(D^{\sharp}) \xrightarrow{\mathbf{R}i^{*}} \operatorname{LCart}(B^{\sharp}) \end{array} \tag{5.2.4.19}$$

that commutes up to a natural transformation

$$\begin{array}{l} \mathbf{L}v_{!} \circ \mathbf{R}j^{*} \rightarrow \mathbf{L}v_{!} \circ \mathbf{R}j^{*} \circ \mathbf{R}u^{*} \circ \mathbf{L}u_{!} \\ \quad \sim \quad \mathbf{L}v_{!} \circ \mathbf{R}v^{*} \circ \mathbf{R}i^{*} \circ \mathbf{L}u_{!} \\ \quad \rightarrow \quad \mathbf{R}i^{*} \circ \mathbf{L}u_{!} \end{array} \tag{5.2.4.20}$$

A square (5.2.4.26) verifies the *Beck-Chevaley condition* if this natural transformation (5.2.4.20) is an equivalence. This square verifies the *weak Beck-Chevaley condition* if the natural transformation once composed with $\perp$ becomes an equivalence.

**Proposition 5.2.4.21.** *If the square (5.2.4.26) is cartesian and $i$ is smooth, then it verifies the Beck-Chevaley condition.*

*Proof.* By construction, $\mathbf{L}v_{!} \circ \mathbf{R}j^{*}$ sends an object $E$ of $\operatorname{LCart}^{c}(C)$ onto the fibrant replacement of $v_{!}j^{*}E$. As $i$ is smooth, $\mathbf{R}i^{*} \circ \mathbf{L}u_{!}$ sends an object $E$ of $\operatorname{LCart}(C)$ onto the fibrant replacement of $i^{*}u_{!}E$. As pullbacks are stable under composition, we have $i^{*}u_{!} \sim v_{!}j^{*}$. $\square$

**Lemma 5.2.4.22.** *A square (5.2.4.26) where both $j$ and $i$ are final verifies the weak Beck-Chevaley condition.*

*Proof.* As $\perp$ sends initial and final morphisms to equivalences, for any $E: \operatorname{LCart}^{c}(A)$ and any $F: \operatorname{LCart}^{c}(C)$, we have equivalences

$$\perp\mathbf{L}v_{!}E \sim \perp E \quad \text{and} \quad \perp\mathbf{L}v_{!}F \sim \perp F.$$

Moreover, as classified left cartesian fibrations are proper, for any $G: \operatorname{LCart}^{c}(C)$ and $H: \operatorname{LCart}(D^{\sharp})$, we have equivalences

$$\perp\mathbf{L}j^{*}G \sim \perp G \quad \text{and} \quad \perp\mathbf{L}i^{*}H \sim \perp H.$$

This implies the result. $\square$

**Lemma 5.2.4.23.** *Suppose given a cartesian square*

$$\begin{array}{c} A \xrightarrow{j} C \\ v \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B^{\sharp} \xrightarrow{i} D^{\sharp} \end{array}$$

287