1.2. GRAY OPERATIONS

**Lemma 1.2.5.20.** Let $A$, $B$ be presheaves on $\Delta$, and $k, m, n, l$ be integers. There exists a natural morphism

$$\beta : \operatorname{Hom}([A, k], 1 \star [m]) \times \operatorname{Hom}([B, m], 1 \star [n]) \to \operatorname{Hom}([B \times A, k], 1 \star [n])$$

such that for any $f : [A, k] \to 1 \star [m]$, $g : [B, m] \to 1 \star [n]$ and $h : [B, n] \to 1 \star [l]$,

$$\beta(\beta(f, g), h) = \beta(f, \beta(g, h)) \tag{1.2.5.21}$$

*Proof.* Similar to the proof of lemma 1.2.5.11.

**Theorem 1.2.5.22.** *The functor*

$$1 \star \_ : \operatorname{Psh}(\Delta) \to \operatorname{Psh}(\Theta_2)$$

sends $\mathrm{W}_1$ onto $\overline{\mathrm{W}_2}$.

*Proof.* Similar to the proof of theorem 1.2.5.3.

**Proposition 1.2.5.23.** *Let $K$ be a simplicial set. The canonical morphism*

$$1 \coprod_{\{0\} \otimes K} [1] \otimes K \to 1 \star K$$

is in $\overline{\mathrm{W}_2}$.

*Proof.* As $K$ is a colimit of representables indexed by the Reedy cofibrant diagram $\Delta_{/K} \to \operatorname{Psh}(\Delta)$ (definition 1.1.3.1), and as $1 \coprod_{\{0\} \otimes \_} [1] \otimes \_$ and $1 \star \_$ preserve cofibrations, it is sufficient to demonstrate the result when $K := [n]$ for $n$ an integer. By theorems 1.2.5.3 and 1.2.5.22, the functors $1 \coprod_{\{0\} \otimes \_} [1] \otimes \_$ and $1 \star \_$ send $\operatorname{Sp}_{[n]} \to [n]$ to $\overline{\mathrm{W}_2}$. It is then sufficient to demonstrate the result when $[n] = [1]$. By propositions 1.2.5.4 and 1.2.5.17, the morphism

$$1 \coprod_{\{0\} \otimes [1]} [1] \otimes [1] \to 1 \star [1]$$

fits in the cocartesian square

$$\begin{array}{ccc} [0] \coprod_{[1]} [2] & \longrightarrow & 1 \coprod_{\{0\} \otimes [1]} [1] \otimes [1] \\ \downarrow & & \downarrow \\ [1] & \longrightarrow & 1 \star [1] \end{array}$$

As the canonical morphism $[0] \coprod_{[1]} [2] \to [1]$ is in $\overline{\mathrm{W}_2}$, this concludes the proof.

59