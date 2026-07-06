16

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

**Lemma 2.15.** *Given $k \geq 0$, the marked $\omega$-functor*

$$\overline{\tau}_{k,\infty} : (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \hookrightarrow (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$$

*obtained as a structure map in the colimit cone from Construction 2.14, is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^{+}$. In particular, $(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$ is cofibrant in $\omega\mathcal{C}at_{\text{coind}}^{+}$.*

*Proof.* This follows from Lemma 2.13, the fact that the class of acyclic cofibrations is closed under transfinite composition, and the fact that acyclic cofibrations are cofibrations. $\square$

We can understand the underlying $\omega$-category of $(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$:

**Lemma 2.16.** *Given $k \geq 0$, there exist $\omega$-functors*

$$\eta^{(k)} : \widehat{\omega\mathcal{E}}^{(k)} \to \overline{\omega\mathcal{E}}^{(k)} \quad \text{and} \quad \mu^{(k)} : \overline{\omega\mathcal{E}}^{(k)} \to \widehat{\omega\mathcal{E}}^{(k+1)}$$

*that make the following diagram in $\omega\mathcal{C}at$ commute:*

$$(2.17) \quad \begin{array}{c} \widehat{\omega\mathcal{E}}^{(k)} \xrightarrow{\iota_k} \widehat{\omega\mathcal{E}}^{(k+1)} \xrightarrow{\iota_{k+1}} \widehat{\omega\mathcal{E}}^{(k+2)} \\ \searrow_{\eta^{(k)}} \searrow_{\overline{\omega\mathcal{E}}^{(k)}} \searrow_{\eta^{(k)}} \searrow_{\eta^{(k+1)}} \searrow_{\overline{\omega\mathcal{E}}^{(k+1)}} \end{array}$$

*Proof.* We construct the $\omega$-functors $\eta^{(k)}$ and $\mu^{(k)}$ by induction on $k \geq 0$. For the base cases, we set $\eta^{(0)}$ and $\mu^{(0)}$ to be the $\omega$-functors

$$\eta^{(0)} : \widehat{\omega\mathcal{E}}^{(0)} = \partial\mathcal{C}_1 \hookrightarrow \mathcal{C}_1 = \overline{\omega\mathcal{E}}^{(0)} \quad \text{and} \quad \mu^{(0)} : \overline{\omega\mathcal{E}}^{(0)} = \mathcal{C}_1 \xrightarrow{f_1} \mathcal{Q} = \widehat{\omega\mathcal{E}}^{(1)},$$

and we set $\eta^{(1)}$ and $\mu^{(1)}$ to be the unique $\omega$-functors

$$\eta^{(1)} : \widehat{\omega\mathcal{E}}^{(1)} = \mathcal{Q} \hookrightarrow \overline{\mathcal{Q}} = \overline{\omega\mathcal{E}}^{(1)} \quad \text{and} \quad \mu^{(1)} : \overline{\omega\mathcal{E}}^{(1)} = \overline{\mathcal{Q}} \to \widehat{\omega\mathcal{E}}^{(2)},$$

which are identity on underlying 1-categories and such that

$$\mu^{(1)} : \alpha \mapsto \alpha_1(\Sigma f) \quad \text{and} \quad \mu^{(1)} : \beta \mapsto \beta_1(\Sigma f).$$

For the inductive step, we assume that $\eta^{(k)}$ and $\mu^{(k)}$ have been constructed, and we now construct $\eta^{(k+1)}$ and $\mu^{(k+1)}$. Using Remark 2.7 and Proposition 2.3 and (2.12), we see that there is a commutative diagram in $\omega\mathcal{C}at$:

$$\begin{array}{ccc} \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) & \longleftarrow & \Sigma(\widehat{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k-1)}) \longrightarrow \widehat{\omega\mathcal{E}}^{(k)} \\ & \downarrow \Sigma\eta^{(k)} \amalg \Sigma\eta^{(k)} & \downarrow \Sigma\eta^{(k-1)} \amalg \Sigma\eta^{(k-1)} & \downarrow \eta^{(k)} \\ \Sigma(\overline{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k)}) & \longleftarrow & \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \longrightarrow \overline{\omega\mathcal{E}}^{(k)} \end{array}$$

and, using (2.12), we define $\eta^{(k+1)}$ as the $\omega$-functor

$$\eta^{(k+1)} : \widehat{\omega\mathcal{E}}^{(k+1)} \to \overline{\omega\mathcal{E}}^{(k+1)}$$

induced at the level of colimits by this map of spans in $\omega\mathcal{C}at$. Similarly, using again Remark 2.7 and Proposition 2.3 and (2.12), we see that there is a commutative