and so in particular, any fibration between fibrant objects. It follows that $\pi_{n+1}E_{n+1} \to \pi_n E_{n+1}$ is an acyclic cofibration. $\square$

**4.40 Lemma.** *For all $n$, $\pi_n P_n \to \mathbb{D}_0$ is a weak equivalence in $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+\infty}$.*

*Proof.* We will proceed by induction. The case $n = 0$ is obvious. Suppose proven that $\pi_n P_n \to \mathbb{D}_0$ is a weak equivalence. We define $\tilde{P}_{n+1}$ as the pushouts:

$$\begin{array}{c} \coprod_{(P_n)_{n+1}} \mathbb{D}_{n+1} \longrightarrow P_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_n E_{n+1} \longrightarrow \tilde{P}_{n+1} \end{array}$$

By [23, Corollary 2.4.4], and Lemmas 4.39 and 4.38, all morphisms labeled by $\sim$ in the following diagrams are acyclic cofibrations, and hence weak equivalences:

$$\begin{array}{c} \coprod_{(P_n)_{n+1}} \mathbb{D}_{n+1} \longrightarrow P_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_{n+1} E_{n+1} \longrightarrow \pi_{n+1} P_{n+1} \\ \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_n E_{n+1} \longrightarrow \tilde{P}_{n+1} \end{array}$$

$$\begin{array}{c} \coprod_{(P_n)_{n+1}} \mathbb{D}_{n+1} \longrightarrow P_{n+1} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} (\mathbb{D}_{n+1}, \overline{\{e_n\}}) \longrightarrow \pi_n P_n \\ \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_n E_{n+1} \longrightarrow \tilde{P}_{n+1} \end{array}$$

By two out of three, and using the assumption that $\pi_n P_n \to \mathbb{D}_0$ is a weak equivalence, the map $\tilde{P}_{n+1} \to \mathbb{D}_0$ is a weak equivalence, and by stability by composition, so is the map $\pi_{n+1} P_{n+1} \to \mathbb{D}_0$. $\square$

**4.41 Lemma.** *For all $n$, the induced morphism $\pi_n C_\infty \to \pi_n D_\infty$ is a weak equivalence in $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+n}$*

*Proof.* By Proposition 4.4, it is sufficient to show that $\pi_n C_\infty \to \pi_n D_\infty$ is a weak equivalence in $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+\infty}$.

Using Lemma 4.40 and since weak equivalences between cofibrant objects are stable by pushout, we have a diagram where all morphisms labeled by $\sim$ are weak equivalences:

$$\begin{array}{c} \coprod_{k \in \mathbb{N}} \pi_n \mathbb{D}_1 \longrightarrow \coprod_{k \in \mathbb{N}} \pi_n P_k \xrightarrow{\sim} (\coprod_{k < n} P_k) \coprod (\coprod_{k \geq n} \mathbb{D}_0) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \pi_n \mathbb{D}_1 \xrightarrow{\sim} \pi_n C_\infty \xrightarrow{\sim} D_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{D}_0 \xrightarrow{\sim} \pi_n D_\infty \xrightarrow{\sim} D_n \end{array}$$

By two out of three, this shows the result. $\square$

*Proof of Proposition 4.31.* We choose $f$ to be the morphism $C_\infty^b \to D_\infty^b$. The first point follows from Lemma 4.37 and the second from Lemma 4.41. $\square$

51