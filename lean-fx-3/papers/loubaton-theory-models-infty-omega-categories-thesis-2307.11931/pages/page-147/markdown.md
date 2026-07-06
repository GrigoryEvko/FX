3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

where the left adjoint sends $[n]$ to $e \star e \star \ldots \star e$.

In section 3.3.1, we show that this assignment extends to a left adjoint. In sections 3.3.2, 3.3.3, and 3.3.4, we show that this left adjoint sends complicial horn inclusions, complicial thinness extensions, and saturation extensions to weak equivalences.

### 3.3.1 Cosimplicial object

3.3.1.1. We consider the following span:

$$\Delta^2_{/[n]} \longleftarrow \underset{\Delta^2_{/[n]}}{\text{colim}} \Delta^2_{/[n_1]} \longrightarrow \underset{\Delta^2_{/[n]}}{\text{colim}} \Delta^2_{/[1+n_1]}$$

where the right functor is induced by $1 + \_ : [n_1] \to [1 + n_1]$ and where the left one sends an element $([n_0]^{op} \star [n_1] \to [n], [n_2]^{op} \star [n_3] \to [n_1])$ to the composite: $h : [n_2]^{op} \star [n_3] \to [n_1] \to [n]$. We define $H^2(a, n)$ as the pushout:

$$\begin{array}{c} \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/[n_1]}}{\text{colim}} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow \underset{\Delta^2_{/[n]}}{\text{colim}} [[n_2] \otimes a, 1] \vee [a, n_3] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/[1+n_1]}}{\text{colim}} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \end{array}$$

By construction, we have a cocartesian square

$$\prod_{l \le 1+n_1} \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/l}}{\text{colim}} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \to H^2(a, n) \prod_{H^2(a, \Pi_{p \le n}\{p\})} H^2(e, \Pi_{p \le n}\{p\}) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \prod_{l \le 1+n_1} \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/l}}{\text{colim}} [[n_2] \otimes e, 1] \vee [e, n_3] \longrightarrow e \star e \star [a, n] \end{array} \tag{3.3.1.2}$$

Let $x := ([n_0]^{op} \star [n_1] \to [n], [n_2]^{op} \star [n_3] \to [1 + n_1])$ be an element of $\underset{\Delta^2_{/[n]}}{\text{colim}} \Delta^2_{/[1+n_1]}$. We define two integers $-1 \le \tilde{n}_2 \le n_2$ and $-1 \le \tilde{n}_3 \le n_3$ as the ones fitting in the following pullbacks in $\Delta_+$

$$[\tilde{n}_2]^{op} \xrightarrow{\quad} [n_1] \xleftarrow{\quad} [\tilde{n}_3] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [n_2]^{op} \longrightarrow [n_2]^{op} \star [n_3] \longrightarrow [1 + n_1] \xleftarrow{\quad} [n_2]^{op} \star [n_3] \xleftarrow{\quad} [n_3]$$

137