Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:41

Lemma 4.22 (Gel formation candidate). If we have $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon} = A_{\varepsilon}'$ pretype for $\varepsilon \in \{0,1\}$, and $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ pretype, then $\Psi \Vdash \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R) \sim \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R') \downarrow \gamma \in \tau$ with $\gamma$ defined on $\Psi' \Vdash \psi \in \Psi$ as follows.

$$\gamma_{\psi} := \left\{ \begin{array}{ll} \{(\operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P), \operatorname{gel}_{\boldsymbol{x}}(M_0', M_1', P')) \mid \\ \forall \varepsilon. (\Psi' \backslash \boldsymbol{x} \Vdash M_{\varepsilon} = M_{\varepsilon}' \in A\psi) \\ \wedge \Psi' \backslash \boldsymbol{x} \Vdash P = P' \in R[M_0, M_1/a_0, a_1]\}, & \text{if } \boldsymbol{r}\psi = \boldsymbol{x} \\ \alpha^{\varepsilon}\psi, & \text{if } \boldsymbol{r}\psi = \boldsymbol{\varepsilon} \in \{\mathbf{0}, \mathbf{1}\} \end{array} \right.$$

Proof. By Lemma 4.16. For every $\Psi' \Vdash \psi \in \Psi$, either $\boldsymbol{r}\psi = \boldsymbol{x}$ for some $\boldsymbol{x}$, in which case we have $\tau(\Psi', \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)\psi, \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R')\psi, \gamma_{\psi})$ by definition of the value type system, or $\boldsymbol{r}\psi = \boldsymbol{\varepsilon} \in \{\mathbf{0}, \mathbf{1}\}$, in which case we have $\operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)\psi \sim A_{\varepsilon}\psi \sim A_{\varepsilon}'\psi \sim \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R')\psi$ by way of GEL-FORM-$\partial$.

Rule 4.23 (GEL-INTRO-$\partial$). For any $\varepsilon \in \{0,1\}$, $\Psi \Vdash A_{\varepsilon}$ pretype, and $\Psi \Vdash M_{\varepsilon} \in A_{\varepsilon}$, and terms $M_{1-\varepsilon}$, $P$, we have $\Psi \Vdash \operatorname{gel}_{\boldsymbol{\varepsilon}}(M_0, M_1, P) = M_{\varepsilon} \in A_{\varepsilon}$.

Proof. By Lemma 4.19, taking $M_{\psi} := M_{\varepsilon}\psi$.

Rule 4.24 (GEL-INTRO). If we have $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash M_{\varepsilon} = M_{\varepsilon}' \in A_{\varepsilon}$ for $\varepsilon \in \{0,1\}$, $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ pretype, and $\Psi \backslash \boldsymbol{r} \Vdash P = P' \in R[M_0, M_1/a_0, a_1]$, then $\Psi \Vdash \operatorname{gel}_{\boldsymbol{r}}(M_0, M_1, P) \sim \operatorname{gel}_{\boldsymbol{r}}(M_0', M_1', P') \in \gamma$ for $\gamma$ as in the statement of Lemma 4.22.

Proof. By Lemma 4.17, proceeding as in Lemma 4.22 by cases on $\boldsymbol{r}\psi$ for each $\psi$: we use the definition of $\gamma$ when $\boldsymbol{r}\psi$ is a variable and GEL-INTRO-$\partial$ when $\boldsymbol{r}\psi$ is a constant.

Lemma 4.25 (Gel formation pretype). If we have $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon} = A_{\varepsilon}'$ pretype for $\varepsilon \in \{0,1\}$, and $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ pretype, then $\Psi \Vdash \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R) = \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R')$ pretype.

Proof. A combination of Lemma 4.22 and GEL-INTRO, the latter of which shows that the relation for Gel is value-coherent.

Rule 4.26 (GEL-$\beta$). If $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash P \in R[M_0, M_1/a_0, a_1]$, then

$$\Psi \Vdash \operatorname{ungel}(\boldsymbol{x} \cdot \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P)) = P \in R[M_0, M_1/a_0, a_1].$$

Proof. By Lemma 4.19: we have $\operatorname{ungel}(\boldsymbol{x} \cdot \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P))\psi \longmapsto P\psi$ for all $\psi$.

Rule 4.27 (GEL-ELIM). If $\Psi \Vdash A_{\varepsilon}$ pretype for $\varepsilon \in \{0,1\}$, $\Psi, a_0 : A_0, a_1 : A_1 \gg R$ pretype, and $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q = Q' \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, R)$, then we have the following.

$$\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = \operatorname{ungel}(\boldsymbol{x}, Q') \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$$

Proof. For every $\Psi' \Vdash \psi \in \Psi$, we have by Lemma 4.20 that $Q\psi \Downarrow Q_{\psi}$ and $Q'\psi \Downarrow Q'_{\psi}$ for some $\Psi', \boldsymbol{x} : \mathbf{I} \Vdash Q\psi = Q_{\psi} = Q'_{\psi} = Q'\psi \in \operatorname{Gel}_{\boldsymbol{x}}(A_0\psi, A_1\psi, a_0, a_1, R\psi)$. By definition of the relation for Gel-types, we have $Q_{\psi} = \operatorname{gel}_{\boldsymbol{x}}(M_{0,\psi}, M_{1,\psi}, P_{\psi})$ and $Q'_{\psi} = \operatorname{gel}_{\boldsymbol{x}}(M'_{0,\psi}, M'_{1,\psi}, P'_{\psi})$ for some terms such that $\Psi' \Vdash P_{\psi} = P'_{\psi} \in R\psi[M_{0,\psi}, M_{1,\psi}/a_0, a_1]$. By GEL-INTRO-$\partial$ and functionality of $R$, it follows that also $\Psi' \Vdash P_{\psi} = P'_{\psi} \in R\psi[Q[\mathbf{0}/\boldsymbol{x}]\psi, Q[\mathbf{1}/\boldsymbol{x}]\psi/a_0, a_1]$. We have $\operatorname{ungel}(\boldsymbol{x}, Q)\psi \longmapsto^* P_{\psi}$ for each $\psi$, thus $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = P_{\mathrm{id}} \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$ by Lemma 4.19; likewise, $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q') = P'_{\mathrm{id}} \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$. We conclude by transitivity that $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = P_{\mathrm{id}} = P'_{\mathrm{id}} = \operatorname{ungel}(\boldsymbol{x}, Q') \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$.

Rule 4.28 (GEL-$\eta$). If $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon}$ pretype for $\varepsilon \in \{0,1\}$, $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R$ pretype, and $\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash Q \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0, a_1, R)$, then we have the following.

$$\Psi \Vdash Q[\boldsymbol{r}/\boldsymbol{x}] = \operatorname{gel}_{\boldsymbol{r}}(Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}], \operatorname{ungel}(\boldsymbol{x}, Q)) \in \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)$$