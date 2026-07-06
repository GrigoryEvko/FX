A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

15

*Proof.* The marked $\omega$-functors

$$f: \mathcal{C}_1^\sharp \to (\mathcal{A}, t\mathcal{A}) \quad \text{and} \quad f: \mathcal{C}_1^\sharp \to (\mathcal{B}, t\mathcal{B})$$

can be recognized as equation inclusions (in the sense of [HL23, Definition 3.1]), so they are by [HL23, Corollary 3.24] acyclic cofibrations in the inductive left semi-model structure from [HL23, Corollary 2.38], hence in the left semi-model structure $\omega\mathcal{C}at_{\text{coind}}^+$, which was constructed as a left Bousfield localization of it (cf. Theorem 2.4). Furthermore, since acyclic cofibrations are closed under pushouts, the marked $\omega$-functor

$$(\mathcal{A}, t\mathcal{A}) \to (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$$

is also an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$, and hence so is the composite

$$f: \mathcal{C}_1^\sharp \to (\mathcal{A}, t\mathcal{A}) \to (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}),$$

as desired. $\square$

**Construction 2.11.** Let $(\overline{\omega\mathcal{E}}^{(0)}, t\overline{\omega\mathcal{E}}^{(0)}) := \mathcal{C}_1^\sharp$. For $k > 0$, we define inductively $(\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$ to be a marked $\omega$-category coming with a triple of marked $\omega$-functors

$$\overline{\tau}_k: (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}),$$

$$\alpha_k, \beta_k: \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}).$$

- For $k = 1$, we let $(\overline{\omega\mathcal{E}}^{(1)}, t\overline{\omega\mathcal{E}}^{(1)}) := (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$, we let $\overline{\tau}_1$ be the marked $\omega$-functor

$$f: \mathcal{C}_1^\sharp \to (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$$

and $\alpha_1, \beta_1$ be defined by

$$\alpha_1: \Sigma p \mapsto g \begin{smallmatrix} \mathbb{Z} \\ 0\end{smallmatrix} f, \; \Sigma q \mapsto \text{id}_p, \; \Sigma f \mapsto \alpha \quad \text{and} \quad \beta_1: \Sigma p \mapsto f \begin{smallmatrix} \mathbb{Z} \\ 0\end{smallmatrix} g', \; \Sigma q \mapsto \text{id}_q, \; \Sigma f \mapsto \beta.$$

- For $k > 1$, we let $(\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$, $\overline{\tau}_k, \alpha_k$, and $\beta_k$ be defined by the pushout in $\omega\mathcal{C}at^+$ (2.12)

$$\begin{array}{ccc} \Sigma(\overline{\omega\mathcal{E}}^{(k-2)}, t\overline{\omega\mathcal{E}}^{(k-2)}) & \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-2)}, t\overline{\omega\mathcal{E}}^{(k-2)}) & \xrightarrow{[\alpha_{k-1}, \beta_{k-1}]} (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \\ \Sigma(\overline{\tau}_{k-1}) \amalg \Sigma(\overline{\tau}_{k-1}) \updownarrow & & \updownarrow \overline{\tau}_k \\ \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) & \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) & \xrightarrow{[\alpha_k, \beta_k]} (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}). \end{array}$$

**Lemma 2.13.** *For all $k \geq 0$ the marked $\omega$-functor*

$$\overline{\tau}_k: (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \hookrightarrow (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. In particular, $(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)})$ is cofibrant in $\omega\mathcal{C}at_{\text{coind}}^+$.

*Proof.* One can deduce this by induction on $k \geq 1$. The base case is Lemma 2.10, and the inductive step is a consequence of the induction hypothesis and (2.12). $\square$

**Construction 2.14.** We denote by $(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$ the colimit in $\omega\mathcal{C}at^+$ given by

$$(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) := \text{colim}[\cdots \leftrightarrow (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \leftrightarrow \cdots \leftrightarrow (\overline{\omega\mathcal{E}}^{(0)}, t\overline{\omega\mathcal{E}}^{(0)})].$$