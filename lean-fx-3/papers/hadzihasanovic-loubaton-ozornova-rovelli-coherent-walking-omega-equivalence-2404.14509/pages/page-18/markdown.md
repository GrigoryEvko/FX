18

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

Proof. The existence of the marked $\omega$-functor follows from Lemma 2.19 and the adjunction $U \dashv (-)^\sharp$, and the fact that it is an acyclic cofibration follows from Lemma 2.5 and Proposition 2.18. $\square$

**Lemma 2.21.** Given $k \geq 0$, the marked $\omega$-functor

$$f_k \colon \mathcal{C}_1^\sharp \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. In particular, by two-out-of-three for weak equivalences in $\omega\mathcal{C}at_{\text{coind}}^+$, we obtain that the marked $\omega$-functor

$$\overline{\iota}_k \colon (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \to (\overline{\omega\mathcal{E}}^{(k+1)}, t\overline{\omega\mathcal{E}}^{(k+1)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$.

Proof. We prove this by induction on $k \geq 1$. The base case $k = 1$ is Lemma 2.10, and we now show the induction step, assuming the statement to be true for $k - 1$. We have that the marked $\omega$-functor

$$f_{k-1} \colon \mathcal{C}_1^\sharp \to (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. By Proposition 2.8, we obtain that the marked $\omega$-functor

$$\Sigma\mathcal{C}_1^\sharp \amalg \Sigma\mathcal{C}_1^\sharp \to \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. By closure of the class of acyclic cofibrations under pushouts, we obtain that the marked $\omega$-functor

$$(\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. By Lemma 2.10, we obtain that the composite marked $\omega$-functor

$$f_k \colon \mathcal{C}_1^\sharp \xrightarrow{f_1} (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$, as desired. $\square$

**Proposition 2.22.** The unique marked $\omega$-functor

$$(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \to \mathcal{C}_0^\sharp$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$.

Proof. The marked $\omega$-functor

$$i_0^+ \colon \mathcal{C}_0^\sharp \hookrightarrow \mathcal{C}_1^\sharp$$

is by Theorem 2.4 a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$. The marked $\omega$-functor

$$f_1 \colon \mathcal{C}_1^\sharp \hookrightarrow (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$ by Lemma 2.10. The marked $\omega$-functor

$$(\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \to (\overline{\omega\mathcal{E}}^{(k+1)}, t\overline{\omega\mathcal{E}}^{(k+1)}) \to \dots \to (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$ by Lemma 2.21, using the fact that acyclic cofibrations are closed under transfinite composition. So the composite marked $\omega$-functor

$$\mathcal{C}_0^\sharp \xrightarrow{i_0^+} \mathcal{C}_1^\sharp \xrightarrow{f_1} (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$. By two-out-of-three, the unique $\omega$-functor

$$(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \to \mathcal{C}_0^\sharp$$