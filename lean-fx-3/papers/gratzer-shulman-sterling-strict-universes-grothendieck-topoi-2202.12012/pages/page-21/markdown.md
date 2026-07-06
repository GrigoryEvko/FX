STRICT UNIVERSES FOR GROTHENDIECK TOPOI

21

PROOF. Let $g$ be a relatively $\kappa$-compact morphism equipped with a cartesian epimorphism $g \to f$ as below:

$$\mathcal{S}_\kappa \ni g \begin{array}{c} C \xrightarrow{a} A \\ \downarrow \\ D \xrightarrow{b} B \end{array} \begin{array}{c} f \\ \downarrow \\ \end{array}$$

We must show that $f$ is relatively $\kappa$-compact. We will use the fact that both $a: C \to A$ and $b: D \to B$ are coequalizers of their kernel pairs, and that kernel pairs are stable:

$$\begin{array}{c} C \times_A C \xrightarrow[q_1]{q_2} C \xrightarrow[a]{a} A \\ \downarrow \\ D \times_B D \xrightarrow[p_2]{p_1} D \xrightarrow[b]{b} B \end{array} \begin{array}{c} f \\ \downarrow \\ \end{array} \tag{14}$$

By Proposition 3.2.6 it suffices to check that $b^*f$, $(b \circ p_0)^*f$, and $(b \circ p_1)^*f$ are relatively $\kappa$-compact. But each of these is a pullback of $g$ (Diagram 14) and therefore by stability (U1), $f$ is relatively $\kappa$-compact. ■

3.3. RELATING SMALL AND RELATIVELY COMPACT MAPS. For this subsection, fix a presentation $\mathcal{E} = \text{Sh}(\mathcal{E}, J)$ and write $i^* \dashv i_*$ for the geometric embedding $\text{Sh}(\mathcal{E}, J) \hookrightarrow \text{Pr}(\mathcal{E})$. Recall that a presheaf $P \in \text{Pr}(\mathcal{E})$ is $\kappa$-small when each $P(C)$ is a $\kappa$-small set. Under mild assumptions, small presheaves precisely correspond to compact presheaves. We reproduce a proof due to Adámek and Rosický [AR94, Example 1.31]:

3.3.1. LEMMA. Given a regular cardinal $\kappa > |\mathcal{E}|$ and a presheaf $P \in \text{Pr}(\mathcal{E})$, the latter is $\kappa$-compact if and only if it is valued in $\kappa$-small sets.

PROOF. First express $P$ as the colimit of representables: $P = \text{colim}_{(c,p) \in \text{Elt}(P)} \mathbf{y}(c) = \text{colim}_{\text{Elt}(P)} \mathbf{y} \circ \pi$. On one hand, if $P$ is valued in $\kappa$-small sets, then $\text{Elt}(P)$ is $\kappa$-small, while each $\mathbf{y}(c)$ is $\kappa$-compact. Thus, $P$ is a $\kappa$-small colimit of $\kappa$-compact objects, hence $\kappa$-compact.

On the other hand, suppose instead that $P$ is $\kappa$-compact; we will show that it is valued in $\kappa$-small sets. By completing $\text{Elt}(P)$ under $\kappa$-small colimits and extending $\mathbf{y} \circ \pi$ by colimits, we obtain a $\kappa$-filtered diagram $\mathcal{D}$ and a map $F: \mathcal{D} \to \text{Pr}(\mathcal{E})$ which sends a formal colimit to a $\kappa$-small colimit of representables. Observe that each $F(d)$ is $\kappa$-small as a $\kappa$-small colimit of representables. Moreover, the canonical map $p: \text{colim}_{\mathcal{D}} F \to P$ is an isomorphism [AR94, Theorem 1.20] so that, in particular, $P$ is the $\kappa$-filtered colimit of $\kappa$-small objects.