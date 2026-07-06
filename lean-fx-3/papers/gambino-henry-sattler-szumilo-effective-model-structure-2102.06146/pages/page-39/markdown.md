**Corollary 7.5.** Let $f \colon X \to Y$ be a Kan fibration with $X$ cofibrant. The pullback functor $f^* \colon \mathcal{E} \downarrow Y \to \mathcal{E} \downarrow X$ preserves maps that in $\mathfrak{s}\mathcal{E}$ are strong homotopy equivalences with cofibrant target.

*Proof.* This follows from Lemma 7.4 using part (ii) of Lemma 1.5 and stability of cofibrant objects under pullback along maps with cofibrant source using part (ii) of Proposition 5.9. $\square$

**Proposition 7.6** (Frobenius property). Let $f \colon X \to Y$ be a Kan fibration with $X$ cofibrant. The pullback functor $f^* \colon \mathcal{E} \downarrow Y \to \mathcal{E} \downarrow X$ preserves trivial cofibrations.

*Proof.* Let $j$ be a trivial cofibration over $Y$. By Proposition 3.17, its underlying map in $\mathfrak{s}\mathcal{E}$ can be written as a retract of a $J_{\mathfrak{s}\mathcal{E}}$-cell complex $j'$. The retraction (including $j'$) lifts uniquely to the slice over $Y$. Since functors preserve retracts, this makes $f^*j$ a retract of $f^*j'$. By Lemma 3.9, it will thus suffice to show that $f^*j'$ is a trivial cofibration.

Recall that $J_{\mathfrak{s}\mathcal{E}}$ consists of levelwise complemented inclusions. By countable lextensivity, Lemma 3.8, and Corollary 2.12, the pullback functor $f^*$ preserves the colimits (countable coproducts, pushouts, sequential colimit) forming the cell complex $j'$. By Lemma 3.9, it thus remains to show that $f^*$ sends to a trivial cofibration any map that in $\mathfrak{s}\mathcal{E}$ is of the form $E \times j''$ where $E \in \mathfrak{s}\mathcal{E}$ and $j'' \in J_{\mathfrak{s}\mathcal{E}}$. Using Lemma 5.4, this simplifies to $j'' \cdot E$. Here, we see $E$ as a constant simplicial object in $\mathcal{E}$.

By part (i) of Corollary 7.3, $j'' \cdot E$ is a strong homotopy equivalence and cofibration between cofibrant objects. By Corollary 7.5, $f^*(j'' \cdot E)$ is a strong homotopy equivalence (using that $f$ is a Kan fibration). By part (i), $f^*(j'' \cdot E)$ is a cofibration between cofibrant objects. By part (ii) of Corollary 7.3, we conclude that $f^*(j'' \cdot E)$ is a trivial cofibration. $\square$

## 8 Fibration extension properties

In this section, we establish two important ingredients in the construction of the effective model structure: the trivial fibration extension property (Proposition 8.5) and the fibration extension property (Proposition 8.13). These arguments are based on the equivalence extension property (Proposition 8.3). We work purely within the cofibrant fragment $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ of $\mathfrak{s}\mathcal{E}$. Our earlier preliminaries allow us to prove the equivalence extension property in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ following [Sat17, Proposition 5.1] and [GSS19, Proposition 3.2.1].

We begin with some observations on homotopy equivalences, which we introduced in Section 1, and an analysis of the restriction of the fibration category structure on $\mathfrak{s}\mathcal{E} \downarrow X$ established in Theorem 1.9 to cofibrant objects. Since the tensor of $X \in \mathfrak{s}\mathcal{E}$ with a finite simplicial set exists and is defined by the formula in (2.1), we may equivalently write a homotopy $H$ between $f_0, f_1 \colon X \to Y$ in $\mathfrak{s}\mathcal{E}$ or one of its slices, which was defined using cotensors in (1.3), via a map

$$H \colon \Delta[1] \cdot X \to Y. \tag{8.1}$$

In $\mathcal{E}$ and its slices, the homotopy relation between maps with cofibrant source and fibrant target is an equivalence relation. This is a formal consequence of part (i) of Lemma 1.5 and Lemma 1.8. It follows that homotopy equivalences between cofibrant and fibrant objects compose as usual.

### Proposition 8.1.

- (i) *For every $X \in \mathfrak{s}\mathcal{E}$, trivial cofibrations in $\mathfrak{s}\mathcal{E} \downarrow X$ are homotopy equivalences.*
- (ii) *Trivial fibrations $X \to Y$ in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ are homotopy equivalences over $Y$.*

39