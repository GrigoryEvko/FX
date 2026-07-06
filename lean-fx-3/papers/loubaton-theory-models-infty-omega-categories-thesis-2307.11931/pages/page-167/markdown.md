3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

As the morphism $[[1] \otimes a, 1] \vee [a, 1] \to [e \star a, 1] \vee [a, 1]$ factors through $[[1] \otimes a, 1] \vee [\tau_n^i([1] \otimes a), 1]$, we get the desired inequality.

**Proposition 3.3.3.13.** *Let $a$ be an object such that $\tau_n^i(a) = a$. Let $x : [a, 1] \to C, y : [a', 1] \to C$ be two morphisms, such that $x \ge_n y$, then if we denote by $\bar{x} := e \star x \circ \alpha_a$ and $\bar{y} := e \star y \circ \alpha_{a'}$, we have $\bar{x} \ge_{n+1} \bar{y}$.*

*Proof.* First, we suppose that we are in the first case of the definition 3.3.3.5. We can then suppose without loss of generality that $C = [a, 1] \vee [\tau_{n-1}^i(a), 1]$. We denote by $\pi$ the projection of $[a, 2]$ on $[a, 1] \vee [\tau_{n-1}^i(a), 1]$. Using the diagrams (3).3.3.3.2, (4).3.3.3.2 and (5).3.3.3.2, we have a diagram:

$$\begin{array}{c} [[1] \otimes a, 1] \xrightarrow{[d^0 \otimes a, 1]} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^1 \bar{\otimes} a, 1]} [e \star a, 1] \\ [[1] \otimes a, d^1] \Big\downarrow \qquad \qquad \qquad \Big\downarrow \epsilon_a \qquad \qquad \qquad \Big\downarrow \alpha_a \\ [e \star a, 1] \vee [a, 1] \xrightarrow{\delta_a} e \star [a, 2] \xleftarrow{e \star [a, d^1]} e \star [a, 1] \\ [e \star a, d^2] \Big\uparrow \qquad \qquad \qquad e \star [a, d^2] \Big\uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e \star a, 1] \xrightarrow{\alpha_a} e \star [a, 1] \qquad \qquad \qquad e \star ([a, 1] \vee [\tau_{n-1}^i(a), 1]) \end{array}$$

Thanks to lemmas 3.3.3.11 and 3.3.3.12, this implies the result.

If we are in the second case of 3.3.3.5, we can suppose that $C = [\tau_{n-1}^i(a), 1] \vee [a, 1]$, and we note by $\pi'$ the projection from $[a, 2] \to [\tau_{n-1}^i(a), 1] \vee [a, 1]$. Using the diagrams (4).3.3.3.2 and (6).3.3.3.2, we have a diagram:

$$\begin{array}{c} [e \star a, 1] \xrightarrow{[d^2 \bar{\otimes} a, 1]} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^1 \bar{\otimes} a, 1]} [e \star a, 1] \\ \alpha_a \Big\downarrow \qquad \qquad \qquad \Big\downarrow \epsilon_a \qquad \qquad \qquad \Big\downarrow \alpha_a \\ e \star [a, 1] \xrightarrow{e \star [a, d^0]} e \star [a, 2] \xleftarrow{e \star [a, d^1]} e \star [a, 1] \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star ([\tau_{n-1}^i(a), 1] \vee [a, 1]) \end{array}$$

Thanks to lemmas 3.3.3.11, this implies the result.

If we are in the third case, it is a direct consequence of the naturality of $\alpha$, of the definition of $n$-reliability and of the fact that $(e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}}$ as remarked in 3.3.2.1.

**Proposition 3.3.3.14.** *Let $x : [a, 1] \to C$, $y : [a', 1] \to C$ and $z : [a'', 1]$ be three morphisms, such that $(x, y) \ge_n z$, then if we denote by $\bar{x} := e \star x \circ \alpha_a$, $\bar{y} := e \star y \circ \alpha_{a'}$ and $\bar{z} := e \star z \circ \alpha_{a''}$, we have $(\bar{x}, \bar{y}) \ge_{n+1} \bar{z}$.*

157