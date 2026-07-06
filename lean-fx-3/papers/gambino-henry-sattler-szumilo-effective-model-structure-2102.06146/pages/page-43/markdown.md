with lower square a pullback. Here, the weak equivalences over $A$ is given by Lemma 8.6. We then complete the diagram using Proposition 8.3, making the back square a pullback. Note that $Z|_{\{1\} \cdot A}$ is isomorphic to $X$ over $A$ by the retract (8.4). The extension in (8.3) is then given by $Y \rightarrow B$. $\square$

**Corollary 8.8.** *For a horn inclusion $j \in J_{\mathfrak{sSet}}$ and $E \in \mathcal{E}$, we have $j \cdot E \in \mathcal{H}$.*

*Proof.* This is the application of Lemma 8.7 to part (i) of Corollary 7.3. $\square$

**Lemma 8.9.** *The class $\mathcal{H}$ is closed under countable coproducts.*

*Proof.* Let $A_i \rightarrow B_i$ be a family of maps in $\mathcal{H}$ for $i \in I$ countable. Note that $\coprod_{i \in I} A_i \rightarrow \coprod_{i \in I} B_i$ is a cofibration between cofibrant objects by Lemma 3.9. Suppose we are given a fibration $X \rightarrow \coprod_{i \in I} A_i$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. We aim to extend it along $\coprod_{i \in I} A_i \rightarrow \coprod_{i \in I} B_i$. Note that $\coprod_{i \in I} B_i$ is a van Kampen colimit since $\mathfrak{s}\mathcal{E}$ is countably lextensive.

For each $i \in I$, we pull it back to a fibration $X_i \rightarrow A_i$ (with $X_i$ cofibrant by part (ii)) and extend it to a fibration $Y_i \rightarrow B_i$. We take their coproduct $\coprod_{i \in I} Y_i \rightarrow \coprod_{i \in I} B_i$. This is a fibration by part (i) of Lemma 3.18. Its domain is cofibrant by Lemma 3.9. By effectivity, it pulls back along $A_i \rightarrow \coprod_{i \in I} B_i$ to the map $X_i \rightarrow A_i$ for $i \in I$. By universality, it thus pulls back along $\coprod_{i \in I} A_i \rightarrow \coprod_{i \in I} B_i$ to the original fibration $X \rightarrow \coprod_{i \in I} A_i$. $\square$

**Lemma 8.10.** *The class $\mathcal{H}$ is closed under pushouts in $\mathfrak{s}\mathcal{E}$ along maps with cofibrant target.*

*Proof.* Consider a pushout square

$$\begin{array}{c} A \longrightarrow A' \\ \downarrow \in \mathcal{H} \quad \downarrow \\ B \longrightarrow B'. \end{array}$$

with $A'$ cofibrant. Note that $A' \rightarrow B'$ is a cofibration between cofibrant objects by Lemma 3.9. The pushout is van Kampen by part (i) of Corollary 2.12. Suppose we are given a fibration $X' \rightarrow A'$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. We aim to extend it along $A' \rightarrow B'$.

We pull the given fibration back along $A \rightarrow A'$ to a fibration $X \rightarrow A$ (here, $X$ is cofibrant by part (ii)) and extend it to a fibration $Y \rightarrow B$. Let $Y' \rightarrow B'$ be the pushout in the arrow category of these three maps. By effectivity, it pulls back to them. It is a fibration by part (ii) of Lemma 3.18. By part (i), $X \rightarrow Y$ is a cofibration, hence so is $X' \rightarrow Y'$ by Lemma 3.9. This makes $Y'$ cofibrant.

We check that $Y' \rightarrow B'$ is a fibration using Proposition 3.4. For each horn inclusion $j \in J_{\mathfrak{sSet}}$, we construct a section of $\widehat{\mathrm{ev}}_j(Y' \rightarrow B')$ given sections of $\widehat{\mathrm{ev}}_j(X' \rightarrow A')$ and $\widehat{\mathrm{ev}}_j(Y \rightarrow B)$. We pull the section of $\widehat{\mathrm{ev}}_j(X' \rightarrow A')$ back to a section of $\widehat{\mathrm{ev}}_j(X \rightarrow A)$ and then extend it using Lemma 3.13 to a section of $\widehat{\mathrm{ev}}_j(Y \rightarrow B)$. The goal follows by Lemma 2.15 and functoriality of colimits. $\square$

**Lemma 8.11.** *The class $\mathcal{H}$ is closed under sequential colimits.*

*Proof.* Consider the colimit $B$ of a sequential diagram

$$A_0 \xrightarrow{\in \mathcal{H}} A_1 \xrightarrow{\in \mathcal{H}} \dots.$$

Note that it is van Kampen by part (ii) of Corollary 2.12. Suppose we are given a fibration $X_0 \rightarrow A_0$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. We aim to extend it along $A_0 \rightarrow B$.

43