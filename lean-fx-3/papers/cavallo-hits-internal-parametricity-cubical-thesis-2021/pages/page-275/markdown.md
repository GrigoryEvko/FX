Modal types

263

$\text{coe}_{x.\text{Disc}(A')\psi_x}^{r\to s}(\text{fhcom}^{t\to u}(M'; \overline{\xi_i \hookrightarrow y.N'_i}))$ to the latter. Thus the two formal composites are coercible, and we can also see that coercion $r \to r$ produces an term equal to the input. Hence $Fhcom(Coe^{-1}) \subseteq Coe^{-1}$ as required. $\square$

**Rule 14.4.12 (Type formation).**

$$\frac{\Psi.\text{cc} \gg A = A' \text{ type @ } m}{\Psi \Vdash \text{Disc}(A) = \text{Disc}(A') \text{ type @ } n}$$

*Proof.* By Lemmas 14.4.10 and 14.4.11. $\square$

Finally, we have the elimination rule for the discrete type.

**Rules 14.4.13 (Discrete elimination).** The following hold for any $\Psi.\text{cc} \gg A$ type @ pt and $\Psi, d : \text{Disc}(A) \gg B = B'$ type @ par.

$$\begin{array}{l} \frac{\Psi \Vdash P = P' \in \text{Disc}(A) \text{ @ par} \qquad \Psi, (\text{cc} \mid a : A) \gg N = N' \in B[\text{mod}(a)/d] \text{ @ par}}{\Psi \Vdash \text{letdisc}(d.B, P, a.N) = \text{letdisc}(d.B', P', a.N') \in B[P/d] \text{ @ par}} \\ \frac{\Psi.\text{cc} \Vdash M \in A \text{ @ pt} \qquad \Psi, (\text{cc} \mid a : A) \gg N \in B[\text{mod}(a)/d] \text{ @ par}}{\Psi \Vdash \text{letdisc}(d.B, \text{mod}(M), a.N) = N[M/a] \in B[\text{mod}(M)/d] \text{ @ par}} \\ \begin{array}{c} \Psi \gg r, s \in \mathbb{I} \text{ @ par} \qquad \Psi \Vdash P \in \text{Disc}(A) \text{ @ par} \\ (\forall i) \Psi \Vdash \xi_i \in \mathbb{F} \text{ @ par} \qquad (\forall i, j) \Psi, x : \mathbb{I}, \xi_i, \xi_j \gg P_i = P_j \in \text{Disc}(A) \text{ @ par} \\ (\forall i) \Psi, \xi_i \gg P = P_i[r/x] \in \text{Disc}(A) \text{ @ par} \end{array} \\ F_x := \text{fhcom}^{r\to s}(P; \overline{\xi_i \hookrightarrow x.P_i}) \qquad \Psi, (\text{cc} \mid a : A) \gg N \in B[\text{mod}(a)/d] \text{ @ par} \\ T := \text{com}_{x.B[F_x/d]}^{r\to s}(\text{letdisc}(d.B, P, a.N); \overline{\xi_i \hookrightarrow \text{letdisc}(d.B, P_i, a.N)}) \\ \hline \Psi \Vdash \text{letdisc}(d.B, F_s, a.N) = T \in B[F_s/d] \text{ @ par} \end{array}$$

*Proof.* We define a $\Psi$-relation $Elim^{-1}$ by declaring that $V \approx V' \in Elim^{-1}\langle\psi\rangle$ whenever $\Psi \Vdash \text{letdisc}(d.B\psi, V, a.N\psi) = \text{letdisc}(d.B'\psi, V', a.N'\psi) \in B\psi[V/d] \text{ @ par}$ and $\Vdash V = V' \in \text{Disc}(A)\psi \text{ @ par}$ hold. By Lemma 3.1.38, we have that $\Psi \Vdash \text{letdisc}(d.B\psi, P, a.N\psi) = \text{letdisc}(d.B'\psi, P', a.N'\psi) \in B\psi[P/d] \text{ @ par}$ for $P \approx P' \in \biguplus Elim^{-1}\psi$. To prove the first rule, it therefore suffices to show that $[\text{Disc}(A)] \subseteq Elim^{-1}$, which by universal property of $[\text{Disc}(A)]$ means showing that $Mod_{cc}([A]) \subseteq Elim^{-1}$ and $Fhcom(Elim^{-1}) \subseteq Elim^{-1}$.

To show that $Mod_{cc}([A]) \subseteq Elim^{-1}$, we observe that the second rule above holds immediately by coherent head expansion. It follows that any equal values in $Mod_{cc}([A])$ are also equal in $Elim^{-1}$.