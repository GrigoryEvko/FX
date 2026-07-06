apply Lemma 4.34 to obtain a sequence $(g_m)_{m \in \mathbb{N}}$ of generators of $C_\infty$. Eventually shifting the sequence, one can freely assume that $g_0$ is of dimension strictly greater than 1. The generators of $C_\infty$ are obtained by gluing the generators of $P_n$ for all $n$ at the unique generator of $\mathbb{D}_1$, so this $g_0$ must be in one of the $P_n$. It then follows by induction that all the $g_m$ are in the same $P_n$, but this leads to a contradiction as the dimension of the generators of $P_n$ is bounded above. $\square$

**4.36 Corollary.** *The marked $\infty$-categories $C_\infty^0$ and $D_\infty^0$ are fibrant in the coinductive left semi-model structure.*

*Proof.* It is immediate that $C_\infty^0$ and $D_\infty^0$ fulfills the conditions of Definition 3.18 and hence they are fibrant in the inductive left semi-model structure by Proposition 3.25. Hence, by Proposition 4.26, we only need to check that all their coinductively invertible arrows are marked. By the previous corollary, only their identity arrows are coinductively invertible, which concludes the proof. $\square$

**4.37 Lemma.** *The morphism $C_\infty \rightarrow D_\infty$ is not a weak equivalence in $\infty\text{-Cat}_{\text{Coind}}^{+\infty}$.*

*Proof.* As both $C_\infty$ and $D_\infty$ are fibrant in the coinductive left semi-model structure, which is a Bousfield localization of the inductive left semi-model structure, this map is a coinductive equivalence if and only if it is an inductive equivalence. Hence, one can test whether it is an equivalence using Definition 3.32 and Proposition 3.33, but this map fails to satisfy condition (1) of Definition 3.32, as the 1-arrow of $C_\infty$ corresponding to the vertical map $\mathbb{D}_1 \rightarrow C_\infty$ is not marked and maps to an identity arrow (hence marked) in $D_\infty$. $\square$

Let us now show the second point, namely that for any integer $n$, $\pi_n C_\infty \rightarrow \pi_n D_\infty$ is a weak equivalence of $\infty\text{-Cat}_{\text{Sat-Ind}}^{+n}$.

**4.38 Lemma.** *For any $n > 0$, the map $(\mathbb{D}_n, \overline{\{e_n\}}) \rightarrow \pi_{n-1} E_n$ is an acyclic cofibration of $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$.*

*Proof.* This map is the composition of pushouts along the equations $(\mathbf{eq}_{n,n}^{-\circ})^{d_{n+1}}$, $(\mathbf{eq}_{n,n}^{-\circ})^{d_{n+1}^*}$ and the saturations $(\mathbf{sat}_{n,n}^{-\circ})^{d_{n+1}}$, $(\mathbf{sat}_{n,n}^{-\circ})^{d_{n+1}^*}$, where $(-)^{d_n}$ is the duality that inverts the direction of $(n+1)$-arrows, and $(-)^{d_{n+1}^*}$ is the duality that inverts the direction of both $n$-arrows and $(n+1)$-arrows. By Corollary 3.31, this concludes the proof. $\square$

**4.39 Lemma.** *For any $n > 0$, the map $\pi_{n+1} E_{n+1} \rightarrow \pi_n E_{n+1}$ is an acyclic cofibration in $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$.*

*Proof.* One should first note that this map is an isomorphism of the underlying $\infty$-categories and corresponds to marking all the $n$-arrows. In particular, it is a cofibration. Moreover, $\pi_{n+1} E_{n+1}$ is cofibrant as its underlying $\infty$-category is a polygraph. Using the characterization of fibrant objects in the saturated inductive left semi-model structure (see Lemma 3.37 and Theorem 3.38), one easily sees that fibrant objects have the unique left lifting property against $\pi_{n+1} E_{n+1} \rightarrow \pi_n E_{n+1}$.

The class of morphisms having the unique left lifting property against this map then contains every morphism $C \rightarrow 1$ where $C$ is fibrant. As this class is closed under left cancellation, it includes any map between fibrant objects,

50