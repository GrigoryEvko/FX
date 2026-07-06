56

E. Cavallo and C. Sattler

Any automorphism $g \in H$ preserves maximum elements, so we have a diagram like so:

$$\begin{array}{c} [1] \times A \xrightarrow{\uparrow} A \\ [1] \times g \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \times A \xrightarrow{\uparrow} A \end{array}$$

We thus obtain a contracting homotopy $\mathbb{I} \times (N_i A / N_i H) \to (N_i A / N_i H)$, using that $N_i([1] \times A) \cong \mathbb{I} \times N_i A$ and that $\mathbb{I} \times (-)$ commutes with colimits.

Lemma 7.5 The counit map $\varepsilon_X: \blacktriangle_! \blacktriangle^* X \to X$ is a weak equivalence for every $X \in \mathrm{PSh}(\overline{\square}_V)$.

Proof Recall that both $\blacktriangle_!$ and $\blacktriangle^*$ are left Quillen (Corollary 4.53 and Lemma 4.54). By Theorem 5.47 and Corollary 7.3, it suffices to show that $\varepsilon_X: \blacktriangle_! \blacktriangle^* X \to X$ is a weak equivalence whenever $X$ is an automorphism quotient of an object in the image of $N_i$. In this case $X$ is weakly contractible by Lemma 7.4. As $\blacktriangle_! \blacktriangle^*$ preserves the terminal object, it preserves weak contractibility by Ken Brown's lemma; thus $\blacktriangle_! \blacktriangle^* X$ is weakly contractible and so $\varepsilon_X$ is a weak equivalence by 2-out-of-3.

Theorem 7.6 $\blacktriangle_!: \widehat{\Delta}^{\mathrm{kq}} \xleftarrow{\longleftrightarrow} \widehat{\square}_V^{\mathrm{ty}}: \blacktriangle^*$ is a Quillen equivalence.

Proof By Corollary 4.53 and Lemmas 4.55 and 7.5.

Corollary 7.7 $\blacktriangle^*: \widehat{\square}_V^{\mathrm{ty}} \xleftarrow{\longleftrightarrow} \widehat{\Delta}^{\mathrm{kq}}: \blacktriangle_*$ is a Quillen equivalence.

Proof Write $\eta'$ and $\varepsilon'$ for the unit and counit of this adjunction. The counit is an isomorphism, so trivially valued in weak equivalences. To check the derived unit, let $X \in \mathrm{PSh}(\square_V)$ and let $m: \blacktriangle^* X \hookrightarrow (\blacktriangle^* X)^{\mathrm{fib}}$ be a fibrant replacement. We have the following naturality square:

$$\begin{array}{c} \blacktriangle_! \blacktriangle^* X \xrightarrow[\cong]{\blacktriangle_! \blacktriangle^* \eta_X'} \blacktriangle_! \blacktriangle^* \blacktriangle_* \blacktriangle^* X \xrightarrow{\blacktriangle_! \blacktriangle^* \blacktriangle_* m} \blacktriangle_! \blacktriangle^* \blacktriangle_* (\blacktriangle^* X)^{\mathrm{fib}} \\ \varepsilon_X \downarrow_! \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \xrightarrow{\eta_X'} \blacktriangle_* \blacktriangle^* X \xrightarrow{\blacktriangle_* m} \blacktriangle_* (\blacktriangle^* X)^{\mathrm{fib}}. \end{array}$$

It follows by 2-out-of-3 that the bottom composite is a weak equivalence.

Theorem 7.8 T: $\widehat{\square}_V^{\mathrm{ty}} \xleftarrow{\longleftrightarrow} \widehat{\Delta}^{\mathrm{kq}}: N_{\square}$ is a Quillen equivalence.

Proof By the decomposition $T \cong \blacktriangle^* \blacksquare$: (Lemma 4.48).

In particular, both $\widehat{\square}_V^{\mathrm{ty}}$ and $\widehat{\square}_V^{\mathrm{ty}}$ present $\infty$-Gpd.

2025/10/16 00:43