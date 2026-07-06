30

E. Cavallo and C. Sattler

Proof Define $u(i, a) := (i \lor r(m(a)), a) : \mathbb{I} \times A \to \mathbb{I} \times A$. Take a pushout of $\delta_0 \widehat{\times} m$:

$$\begin{array}{c} \mathrm{M}_{0}(m) \xrightarrow{u \sqcup \mathrm{id}} \mathrm{M}_{r}(m) \\ \delta_{0} \widehat{\times} m \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \times B \xrightarrow{b} C. \end{array}$$

Define a map $v : \mathrm{M}_{1}(r \widehat{\times}_{B} m) \to C$ like so:

$$\begin{array}{c} \mathrm{M}_{r}(m) \xrightarrow{r \widehat{\times}_{B} m} \mathbb{I} \times B \xrightarrow{\varepsilon \times B} B \\ \delta_{1} \times \mathrm{M}_{r}(m) \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \times B \\ \mathbb{I} \times \mathrm{M}_{r}(m) \xrightarrow{d_{1}} \mathrm{M}_{1}(r \widehat{\times}_{B} m) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \times B \\ u \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \\ \mathrm{M}_{r(\varepsilon \times B)}(\mathbb{I} \times m) \xrightarrow{[nd_{r}(\vee \times A), b]} C. \end{array}$$

Take the pushout of $\delta_{1} \widehat{\times} (r \widehat{\times}_{B} m)$ by this map:

$$\begin{array}{c} \mathrm{M}_{1}(r \widehat{\times}_{B} m) \xrightarrow{\nu} C \\ \delta_{1} \widehat{\times} (r \widehat{\times}_{B} m) \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \\ \mathbb{I} \times \mathbb{I} \times B \xrightarrow{b'} D. \end{array}$$

Then we can exhibit $r \widehat{\times}_{B} m$ as a retract of $n' n$:

$$\begin{array}{c} \mathrm{M}_{r}(m) \xrightarrow{\mathrm{id}} \mathrm{M}_{r}(m) \xrightarrow{\mathrm{id}} \mathrm{M}_{r}(m) \\ r \widehat{\times}_{B} m \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \\ \mathbb{I} \times B \xrightarrow{\delta_{0} \times \mathbb{I} \times B} \mathbb{I} \times \mathbb{I} \times B \xrightarrow{b'} D \xrightarrow{[\varepsilon \times \mathbb{I} \times B, [\mathrm{id}, r \widehat{\times}_{B} m]]} \mathbb{I} \times B. \end{array}$$

As a retract of a trivial cofibration, $r \widehat{\times}_{B} m$ is thus a trivial cofibration.

Corollary 4.23 A map is a fibration in $\overline{\Omega}_{\vee}^{\mathrm{ty}}$ if and only if it is an unbiased fibration.

Proof If $f : Y \to X$ is an unbiased fibration, then lifting against any $\delta_{k} \widehat{\times} m$ is obtained as lifting against $(\delta_{k}!_{B}) \widehat{\times}_{B} m$. The converse is Lemma 4.22.

Remark 4.24 For the reader more comfortable with cubical type theories, we give the type-theoretic analogue to the proof of Corollary 4.23. The ABCHFL type theory equips

2025/10/16 00:43