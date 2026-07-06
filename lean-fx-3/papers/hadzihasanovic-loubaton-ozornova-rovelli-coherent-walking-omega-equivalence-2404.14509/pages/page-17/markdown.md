A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

17

diagram in $\omega\mathcal{C}at$:

$$\begin{array}{c} \Sigma(\overline{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k)}) \longleftarrow \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \longrightarrow \overline{\omega\mathcal{E}}^{(k)} \\ \downarrow_{\Sigma\mu^{(k)}\amalg\Sigma\mu^{(k)}} \qquad \qquad \downarrow_{\Sigma\mu^{(k-1)}\amalg\Sigma\mu^{(k-1)}} \qquad \qquad \downarrow_{\mu^{(k)}} \\ \Sigma(\widehat{\omega\mathcal{E}}^{(k+1)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k+1)}) \longleftarrow \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) \longrightarrow \widehat{\omega\mathcal{E}}^{(k+1)} \end{array}$$

and, using (2.12), we define $\mu^{(k+1)}$ as the $\omega$-functor

$$\mu^{(k+1)}: \overline{\omega\mathcal{E}}^{(k+1)} \to \widehat{\omega\mathcal{E}}^{(k+2)}$$

induced at the level of colimits by this map of spans in $\omega\mathcal{C}at$. One can finally show, by induction on $k \ge 0$, that the $\omega$-functors $\eta^{(k)}$, $\mu^{(k)}$, $\eta^{(k+1)}$ and $\mu^{(k+1)}$ fit into the desired commutative diagram in $\omega\mathcal{C}at$. $\square$

**Proposition 2.18.** *There is an isomorphism in $\omega\mathcal{C}at*

$$\mu: \overline{\omega\mathcal{E}} = U(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \cong \widehat{\omega\mathcal{E}}: \eta.$$

*Proof.* From the property (2.17), one can deduce that the $\omega$-functors $\eta^{(k)}$ and $\mu^{(k)}$ from Lemma 2.16 define by construction the components of two natural transformations with respect to $k \in \mathbb{N}$. By taking the $\omega$-functor induced at the level of colimits over $n \in \mathbb{N}$ we then obtain $\omega$-functors

$$\underset{k \in \mathbb{N}}{\text{colim}} \eta^{(k)}: \underset{k \in \mathbb{N}}{\text{colim}} \widehat{\omega\mathcal{E}}^{(k)} \to \underset{k \in \mathbb{N}}{\text{colim}} \overline{\omega\mathcal{E}}^{(k)}, \quad \underset{k \in \mathbb{N}}{\text{colim}} \mu^{(k)}: \underset{k \in \mathbb{N}}{\text{colim}} \overline{\omega\mathcal{E}}^{(k)} \to \underset{k \in \mathbb{N}}{\text{colim}} \widehat{\omega\mathcal{E}}^{(k+1)},$$

which can be identified with $\omega$-functors

$$\eta: \widehat{\omega\mathcal{E}} \to \overline{\omega\mathcal{E}} \quad \text{and} \quad \mu: \overline{\omega\mathcal{E}} \to \widehat{\omega\mathcal{E}}.$$

From the property (2.17), one can also deduce that $\mu$ and $\eta$ are inverse to each other, concluding the proof. $\square$

**Lemma 2.19.** *The inverse isomorphisms $\mu$ and $\eta$ in $\omega\mathcal{C}at$ induce inverse isomorphisms in $\omega\mathcal{C}at^{+}$*

$$\mu: \overline{\omega\mathcal{E}}^{\sharp} = \overline{\omega\mathcal{E}}^{\sharp} \cong \widehat{\omega\mathcal{E}}^{\sharp} = \widehat{\omega\mathcal{E}}^{\sharp}: \eta.$$

*Proof.* Since $(-)^{\sharp}$ is a functor we obtain inverse isomorphisms in $\omega\mathcal{C}at^{+}$

$$\mu: \overline{\omega\mathcal{E}}^{\sharp} \cong \widehat{\omega\mathcal{E}}^{\sharp}: \eta.$$

By Propositions 1.19 and 1.32, all cells of $\widehat{\omega\mathcal{E}}$ above dimension 0 are $\omega$-equivalences, which implies that

$$\widehat{\omega\mathcal{E}}^{\sharp} = \widehat{\omega\mathcal{E}}^{\sharp}.$$

By Proposition 2.18 we obtain that

$$\overline{\omega\mathcal{E}}^{\sharp} = \overline{\omega\mathcal{E}}^{\sharp}.$$

This concludes the proof. $\square$

**Proposition 2.20.** *The $\omega$-functor $\mu$ determines an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^{+}$*

$$\mu: (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \hookrightarrow \overline{\omega\mathcal{E}}^{\sharp} \cong \widehat{\omega\mathcal{E}}^{\sharp}$$