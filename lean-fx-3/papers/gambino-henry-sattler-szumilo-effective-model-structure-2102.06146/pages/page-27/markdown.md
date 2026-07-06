where $\mathrm{Sk}_A^{-1}B = A$ and for $k \geq 0$ the square

$$\begin{array}{ccc} B_k \times \partial \Delta[k] \cup (A_m \sqcup_{L_m A} L_m B) \times \Delta[k] & \longrightarrow & \mathrm{Sk}_A^{k-1}B \\ \downarrow & & \downarrow \\ B_k \times \Delta[k] & \longrightarrow & \mathrm{Sk}_A^k B \end{array}$$

is a pushout. These statements are justified analogously to the proofs of [GSS19, Lemma 2.3.1, Corollary 2.3.3]. The colimits used in the construction exist by Corollary 2.12 since they are colimits of sequences of levelwise complemented inclusions and pushouts along levelwise complemented inclusions which is ensured by the assumption that $A \rightarrow B$ is a cofibration. $\square$

Our next goal is to provide a characterisation of cofibrations in terms of actions of degeneracy operators, stated in Theorem 4.6 below. This is a generalisation of [Hen18, Proposition 5.1.4] or [GSS19, Proposition 1.4.4] to a setting without arbitrary colimits. The proof is made significantly more complex by the fact that $\mathcal{E}$ is not assumed to be a Grothendieck topos. Instead, the required exactness properties are substituted by Lemma 2.14. We also need the following statement. For this, we observe that our discussion of Reedy theory and latching objects for the case of $\Delta$ applies just as well to arbitrary countable Reedy categories of countable height. Note that the assumption of a Reedy cofibrant diagram includes the hypothesis that all latching objects exist.

**Lemma 4.5.** *Let $D$ be a finite direct category. Let $F: D \rightarrow \mathfrak{s}\mathcal{E}$ be a Reedy cofibrant diagram. Then the colimit of $F$ exists and is van Kampen.*

*Proof.* We proceed by induction on the height of $D$. For height 0, note that $D$ is the empty and the claim holds because initial objects are van Kampen since $\mathfrak{s}\mathcal{E}$ is lextensive.

Now assume the claim for height $n$ and let $D$ have height $n+1$. Let $D'$ of height $n$ denote the restriction of $D$ to objects of degree below $n$. Let $I$ be the collection of objects of $D$ of degree $n$. As per usual Reedy theory, we may compute the colimit of $F$ as the following pushout:

$$\begin{array}{ccc} \coprod_{i \in I} L_i F & \longrightarrow & \operatorname{colim}_{D'} F|_{D'} \\ \downarrow & & \downarrow \\ \coprod_{i \in I} F(i) & \longrightarrow & \operatorname{colim}_D F. \end{array}$$

Here, the left map is a cofibration because it is a finite coproduct of cofibrations, and hence the pushout exists and is van Kampen by Lemma 2.9. By the inductive hypothesis, the colimit computing the latching object $L_i F$ for $i \in I$ is van Kampen, and so is the colimit of $F|_{D'}$. The finite coproducts are van Kampen since $\mathfrak{s}\mathcal{E}$ is lextensive. Using the characterisation of van Kampen colimits given by Lemma 2.2, one sees that $\operatorname{colim}_D F$ is van Kampen. $\square$

**Theorem 4.6** (Characterisation of cofibrations). *Let $i: A \rightarrow B$ be a map in $\mathfrak{s}\mathcal{E}$. Then the following are equivalent:*

- (i) *the map $i$ is a cofibration;*
- (ii) *the map $i$ is a levelwise complemented inclusion and the map $A_m \sqcup_{A_n} B_n \rightarrow B_m$ is a complemented inclusion for every degeneracy operator $[m] \rightarrow [n]$.*

27