5:42

E. CAVALLO AND R. HARPER

Vol. 17:4

Proof. By Lemma 4.20, we have $\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash Q = V \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$ for some $Q \Downarrow V$. By definition of the relation for Gel-types, we know $V = \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P)$ for some suitably-typed $M_0$, $M_1$, and $P$. By GEL-INTRO-$\partial$, GEL-$\beta$, and GEL-INTRO, we conclude the following.

$$\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash V = \operatorname{gel}_{\boldsymbol{x}}(V[\mathbf{0}/\boldsymbol{x}], V[\mathbf{1}/\boldsymbol{x}], \operatorname{ungel}(\boldsymbol{x}.V)) \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$$

We can replace $V$ with $Q$ everywhere in this equation using GEL-INTRO and GEL-ELIM. Substituting $\boldsymbol{r}$ for $\boldsymbol{x}$ then gives the result.

It only remains to show that Gel-types support the Kan operations. We will go through the proof for hcom; the proof for coe has an identical structure. We will begin by proving reduction lemmas for the constant and variable cases.

Lemma 4.29. Let $\Psi \Vdash A_{\varepsilon}$ type for some $\varepsilon \in \{0, 1\}$. If $\Psi \Vdash r, s \in \mathbb{I}, n \in \mathbb{N}$, $\Psi \Vdash \xi_i$ constraint, $\Psi \Vdash Q \in A_{\varepsilon}$, $\Psi, y : \mathbb{I} \Vdash Q_i = Q_j \in A_{\varepsilon}$ for all $i, j < n$, and $\Psi \Vdash Q = Q_i[r/y] \in A_{\varepsilon}$ for all $i < n$, then $\Psi \Vdash \operatorname{hcom}_{\operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) \in A_{\varepsilon}$.

Proof. By Lemma 4.19: every substitution instance of the left-hand side steps to the corresponding instance of the right-hand side, which is well-typed because $A_{\varepsilon}$ is Kan.

Lemma 4.30. Let $\Psi \Vdash A_{\varepsilon}$ type for $\varepsilon \in \{0, 1\}$ and $\Psi, a_0 : A_0, a_1 : A_1 \gg R$ type. Abbreviate $G := \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$. For any $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash r, s \in \mathbb{I}, n \in \mathbb{N}$, $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash \xi_i$ constraint, $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q \in G$, $\Psi, \boldsymbol{x} : \mathbf{I}, y : \mathbb{I} \Vdash Q_i = Q_j \in G$ for all $i, j < n$, and $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q = Q_i[r/y] \in G$ for all $i < n$, we have $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash \operatorname{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P) \in G$ where $M_{\varepsilon,-}$ and $P$ are defined as follows.

$$\begin{array}{l} M_{\varepsilon,y} := \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow y}(Q[\varepsilon/\boldsymbol{x}]; \overline{\xi_i[\varepsilon/\boldsymbol{x}] \hookrightarrow y.Q_i[\varepsilon/\boldsymbol{x}])} \\ P := \operatorname{com}_{y.R[M_{0,y}, M_{1,y}/a_0,a_1]}^{r \rightsquigarrow s}(\operatorname{ungel}(\boldsymbol{x}.Q); \overline{\forall \boldsymbol{x}.\xi_i \hookrightarrow y.\operatorname{ungel}(\boldsymbol{x}.Q_i)}) \end{array}$$

Proof. By Lemma 4.19. For every $\Psi' \Vdash \psi \in (\Psi, \boldsymbol{x} : \mathbf{I})$, we have two cases.

$\triangleright \boldsymbol{x}\psi = \varepsilon \in \{\mathbf{0}, \mathbf{1}\}$. Then $\operatorname{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi \longmapsto \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi$, and we have $\Psi' \Vdash \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi = \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P)\psi \in G\psi$ by GEL-INTRO-$\partial$ and the assumption that $A$ is Kan.

$\triangleright \boldsymbol{x}\psi$ is a variable. Then $\operatorname{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi \longmapsto \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P)\psi$, and we have $\Psi' \Vdash \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P)\psi \in G\psi$ by GEL-INTRO-$\partial$, GEL-ELIM, and the assumption that the $A_{\varepsilon}$ and $R$ are Kan. We use here that the capture of $\boldsymbol{x}$ by ungel in the definition of the reduct commutes with $\psi$, which relies on the affinity of bridge interval substitution.

Rule 4.31 (GEL-FORM). If $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon} = A_{\varepsilon}'$ type for each $\varepsilon \in \{0, 1\}$, and $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ type, then we have the following.

$$\Psi \Vdash \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0.a_1.R) = \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0.a_1.R') \text{ type}$$

Proof. We must check that Gel supports the Kan operations. We give the proof for hcom. Abbreviate $G := \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0.a_1.R)$ and $G' := \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0.a_1.R')$. Let $\Psi' \Vdash \psi \in \Psi$, $\Psi' \Vdash r, s \in \mathbb{I}$, $n \in \mathbb{N}$, $\Psi' \Vdash \xi_i$ constraint for all $i < n$, $\Psi' \Vdash Q = Q' \in G\psi$, $\Psi', y : \mathbb{I} \Vdash Q_i = Q_j' \in G\psi$ for all $i, j < n$, and $\Psi' \Vdash Q = Q_i[r/y] \in G\psi$ for all $i < n$ be given. If $\boldsymbol{r}\psi$ is a constant, then we simply apply GEL-FORM-$\partial$ and Lemma 4.29 everywhere.