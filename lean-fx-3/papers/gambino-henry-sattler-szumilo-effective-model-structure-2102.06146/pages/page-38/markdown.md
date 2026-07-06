the enrichment of $\mathfrak{sE}$ in $\mathfrak{sSet}$. Recall that pushout tensors with levelwise complemented inclusions between finite simplicial sets such as $!$, $\lambda_1^0$, $\lambda_1^0$ exist by Proposition 5.5.

**Lemma 7.1.** *Let $f: X \to Y$ be a map in $\mathfrak{sE}$. For $k \in \{0, 1\}$, the following are equivalent:*

- (i) $f$ is a $k$-oriented strong homotopy equivalence,
- (ii) $\theta_k \widehat{\cap} f: f \to \lambda_1^k \widehat{\cap} f$ is a split monomorphism,
- (iii) $\theta_k \widehat{\cap} f: \lambda_1^k \widehat{\cap} f \to f$ is a split epimorphism.

*Proof.* Identical to [GS17, Lemma 4.3] and [GSS19, Lemma 3.1.1].

**Corollary 7.2.** *Let $i$ be a levelwise complemented inclusion between finite simplicial sets that is a strong homotopy equivalence. For any map $f$ in $\mathfrak{sE}$, the pushout tensor $i \widehat{\cap} f$ is a strong homotopy equivalence in $\mathfrak{sE}$.*

*Proof.* This is a formal consequence of the characterisation (ii) of strong homotopy equivalences given by Lemma 7.1. We have $\theta_k \widehat{\cap} (i \widehat{\cap} f) \cong (\theta_k \widehat{\times} i) \widehat{\cap} f$, a formal consequence of the isomorphism $A \cdot (B \cdot X) \cong (A \times B) \cdot X$ natural in $A, B \in \mathfrak{sSet}$ and $X \in \mathfrak{sE}$. By assumption, $\theta_k \widehat{\times} i$ has a retraction, hence also its image under $(-\widehat{\cap}) \widehat{\cap} f$.

Strong homotopy equivalences can be used to relate cofibrations and trivial cofibrations.

### Corollary 7.3.

- (i) *For a horn inclusion $j \in J_{\mathfrak{sSet}}$ and $E \in \mathcal{E}$, the map $j \cdot E$ is a strong homotopy equivalence and cofibration between cofibrant objects.*
- (ii) *Any cofibration that is a strong homotopy equivalence is a trivial cofibration.*

*Proof.* For part (i), recall from [GZ67, Chapter IV, Section 2, Paragraph 2.1.3] that the horn inclusion $j$ in $\mathfrak{sSet}$ is a strong homotopy equivalence. By Corollary 7.2, it follows that $j \cdot E$ is a strong homotopy equivalence. The object $E \in \mathfrak{sE}$ is cofibrant by part (i) of Proposition 5.9. By Proposition 5.5, it follows that $j \cdot E$ is a cofibration between cofibrant objects.

Part (ii) follows from the characterisation of strong homotopy equivalences in condition (ii) of Lemma 7.1, closure of trivial cofibrations under retracts (Lemma 3.9), and Proposition 5.5 (using that $\lambda_1^0$ and $\lambda_1^1$ are trivial cofibrations).

### Lemma 7.4. Let

$$\begin{array}{c} B \longrightarrow A \\ g \downarrow \quad \downarrow \quad \downarrow f \\ X \longrightarrow Y \end{array}$$

*be a pullback square with $X$ cofibrant. If, $f$ is a $k$-oriented strong homotopy equivalence, where $k \in \{0, 1\}$, then so is $g$.*

*Proof.* This is identical to [GSS19, Lemma 3.1.3], but played out in $\mathfrak{sE}_{\mathrm{cof}}$ instead of $\mathfrak{sSet}_{\mathrm{cof}}$. The pushout product with $\{1\} \to \Delta[1]$ (for $k = 0$) becomes a pushout tensor, which sends the cofibration $\varnothing \to X$ to a trivial cofibration by Proposition 5.5.

38