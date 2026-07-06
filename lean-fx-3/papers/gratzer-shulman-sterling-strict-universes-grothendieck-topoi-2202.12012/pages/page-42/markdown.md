42

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

sending $b : B$ to the identity equivalence $X[b] \to X[b]$:

$$\begin{array}{c} B \xrightarrow{\delta_X} \mathsf{Eq}(X) \\ \Bigg\downarrow \quad \Bigg\downarrow \langle \partial_0, \partial_1 \rangle \\ B \xrightarrow[\delta]{} B \times B \end{array}$$

6.2.5. DEFINITION. A Kan fibration $X \to B$ is called univalent when $\delta_X : B \to \mathsf{Eq}(X)$ is a trivial cofibration.

We will now sketch the proof that $\pi_{\mathcal{U}_0}$ is univalent. Just as with Theorem 6.2.3, the proof decomposes into two pieces: a homotopy-theoretic result and a careful analysis and application of (U8) to parlay this result into the appropriate result on the universe. For univalence, the relevant homotopy-theoretic fact is the equivalence extension property, apparently first isolated by Kapulkin, Lumsdaine, and Voevodsky [KL21], named by Awodey, and further developed by several authors including Awodey, Coquand, Sattler, and Shulman [Awo21; Coh+17; Sat17; Shu15; Shu19].

6.2.6. LEMMA (EQUIVALENCE EXTENSION PROPERTY). We consider a diagram of the following shape, in which the downward maps are Kan fibrations, $i : A \to B$ is a cofibration, and $w : X \to i^*Y$ is a weak equivalence:

$$\begin{array}{c} X \xrightarrow{w} i^*Y \xrightarrow{} Y \\ A \xrightarrow{i} B \end{array} \tag{38}$$

Then Diagram 38 can be extended to a diagram of the following shape, in which $\bar{w} : \bar{X} \to Y$ is a weak equivalence and $\bar{X} \to B$ is a fibration, and all three squares are cartesian:

$$\begin{array}{c} X \xrightarrow{w} i^*Y \xrightarrow{} \bar{X} \xrightarrow{\bar{w}} Y \\ A \xrightarrow{i} B \end{array}$$

Moreover, if $X \to A$ and $Y \to B$ both belong to $\mathcal{U}_0$, so does $\bar{X} \to B$.

6.2.7. THEOREM. The family $\pi_{\mathcal{U}_0} : E_{\mathcal{U}_0} \to U_{\mathcal{U}_0}$ is univalent.