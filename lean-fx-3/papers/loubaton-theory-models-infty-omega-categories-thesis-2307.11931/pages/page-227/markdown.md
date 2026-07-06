4.3. GRAY OPERATIONS

**Lemma 4.3.3.3.** *For any $n$, $\mathbf{D}_n \otimes [1]$, $\mathbf{D}_n \star 1$ and $1 \stackrel{co}{\star} \mathbf{D}_n$ are strict.*

*Proof.* We proceed by induction on $n$. The result is obviously true for $n = 0$. Suppose it is true as the stage $n$. According to equation (4.3.1.7), $\mathbf{D}_n \otimes [1]$ is the colimit of the following diagram

$$[1] \vee \mathbf{D}_n \longleftarrow \mathbf{D}_n \longrightarrow [\mathbf{D}_{n-1} \otimes [1], 1] \longleftarrow \mathbf{D}_n \longrightarrow \mathbf{D}_n \vee [1] \tag{4.3.3.4}$$

The induction hypothesis and proposition 4.3.3.2 implies that all the objects are strict. The proposition 1.2.3.15 then implies that the diagram

$$\begin{array}{ccc} \mathbf{D}_{n-1} & \longrightarrow & \mathbf{D}_{n-1} \otimes [1] \longleftarrow \mathbf{D}_{n-1} \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [1] \longleftarrow \{1\} \end{array}$$

verifies the hypothesis of proposition 4.2.1.30. The proposition *op. cit.* then states that the colimit of (4.3.3.4) is special, which implies, according to lemma 4.1.1.6, that its colimit, which is $\mathbf{D}_n \otimes [1]$, is also strict.

We proceed similarly for the Gray cone and the Gray o-cone.

We now recall the following fundamental result of strictification:

**Theorem 4.3.3.5** (Gagna, Ozornova, Rovelli). *For any globular sum $a$, $a \star 1$ and $1 \stackrel{co}{\star} a$ are stricts.*

*Proof.* The fact that $a \star 1$ is strict is a particular case of theorem 5.2 of [GOR21]. For the second assertion, remark that we have a canonical comparison, natural in $a : \Theta$:

$$1 \stackrel{co}{\star} a \to \mathrm{N} \, \pi_0 (1 \stackrel{co}{\star} a) \sim \mathrm{N} \, \pi_0 (a^\circ \star 1)^\circ \sim (\mathrm{N} \, \pi_0 (a^\circ \star 1))^\circ \sim (a^\circ \star 1)^\circ$$

where the first equivalence is a consequence of [AM20, proposition A.22], the second comes from the commutativity of $\pi_0$ and $\mathrm{N}$ with dualities, and the last one is the (already demonstrated) first assertion. The subset of object of $\Theta$ making this comparison an equivalence is closed by colimits and, according to lemma 4.3.3.3, contains globes. This subset then contains all the globular sums. As strict objects are stable by dualities, this concludes the proof of the second assertion.

**Lemma 4.3.3.6.** *Let $\alpha$ be $-$ if $n$ is even (resp. odd) and $+$ if $n$ is odd (resp. even). Consider a cartesian square*

$$\begin{array}{ccc} C_0 & \longrightarrow & D \\ \downarrow_p & \downarrow_{\perp} & \downarrow_{p'} \\ \mathbf{D}_n & \xrightarrow{i_n^\alpha} & \mathbf{D}_{n+1} \end{array} \tag{4.3.3.7}$$

217