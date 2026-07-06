4.3. GRAY OPERATIONS

functors $[i_{n-1}^{-}, 1]^{*}$, $[i_{n-1}^{+}, 1]^{+}$ preserve colimits according to theorem 4.2.2.9. We then have two cartesian squares:

$$\begin{array}{ccc} C \coprod_{a} a \star 1 & \longrightarrow & C \coprod_{b} b \star 1 \\ \downarrow & & \downarrow \\ [\mathbf{D}_{n-1}, 1] & \xrightarrow{[i_{n-1}^{\alpha}, 1]} & [\mathbf{D}_{n}, 1] \end{array} \qquad \begin{array}{ccc} C \coprod_{a'} a' \star 1 & \longrightarrow & C \coprod_{b} b \star 1 \\ \downarrow & & \downarrow \\ [\mathbf{D}_{n-1}, 1] & \xrightarrow{[i_{n-1}^{-\alpha}, 1]} & [\mathbf{D}_{n}, 1] \end{array} \tag{4.3.3.13}$$

and by the induction hypothesis, the two top left objects are strict. Eventually, remark that we have a cocartesian square

$$\begin{array}{ccc} \mathbf{D}_{n} \coprod_{\mathbf{D}_{n-1}} \mathbf{D}_{n-1} \star 1 & \longrightarrow & \mathbf{D}_{n} \star 1 \\ \downarrow & & \downarrow \\ C \coprod_{a} a \star 1 & \longrightarrow & C \coprod_{b} b \star 1 \end{array}$$

and the proposition 4.3.2.5 then implies that the left square of (4.3.3.13) is a left $(n+1)$-Gray retract, and the lemma 4.3.3.6 implies that $C \coprod_{b} b \star 1$ is strict. This proves the first assertion. The second one is proved similarly.

4.3.3.14. We now want to give an analogue of proposition 4.3.3.12 for the Gray cylinder. In what follows, we will use the results of sections 5.2.3 and 5.2.2 (more precisely the proposition 5.2.3.8, the theorem 5.2.3.10 and the corollaries 5.2.3.11, 5.2.3.12). We assure the reader that this is not a tautology, as the proofs of these results are not based on the following propositions and theorems

**Proposition 4.3.3.15.** Let $a$ be a globular sum. The two following canonical squares are cartesian

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \stackrel{co}{\star} a \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [a, 1] \end{array} \qquad \begin{array}{ccc} 1 & \longrightarrow & a \star 1 \\ \downarrow & & \downarrow \\ \{1\} & \longrightarrow & [a, 1] \end{array}$$

The five squares appearing in the following canonical diagram are both cartesian and cocartesian:

$$\begin{array}{ccc} & a \otimes \{0\} & \longrightarrow & 1 \\ & \downarrow & & \downarrow \\ a \otimes \{1\} & \longrightarrow & a \otimes [1] & \longrightarrow & a \star 1 \\ \downarrow & & \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{co}{\star} a & \longrightarrow & [a, 1] \end{array}$$

221