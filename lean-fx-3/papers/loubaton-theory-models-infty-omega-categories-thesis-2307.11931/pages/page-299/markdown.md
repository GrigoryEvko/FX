5.2. CARTESIAN FIBRATIONS

The two morphisms $\{c\} \to C_{c/}^{\sharp}$ and $\{c\} \to D_{j(c)/}^{\sharp}$ are initial, and by stability by left cancellation, so is $C_{c/}^{\sharp} \to D_{j(c)/}^{\sharp}$. By stability by cartesian product, the two horizontal morphisms of the left square are initial. Lemma 5.2.4.22 then implies that the left square verifies the weak Beck-Chevaley condition. According to proposition 5.2.4.21, the right square fulfills the Beck-Chevaley condition, and so *a fortiori*, the weak one. The outer square then verified the weak Beck-Chevaley condition, which concludes the proof. $\square$

**5.2.4.25.** Suppose given a commutative square of marked $(\infty, \omega)$-categories:

$$
\begin{array}{c}
A \xrightarrow{j} C^{\sharp} \\
v \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(5.2.4.26)} \\
B \xrightarrow{i} D^{\sharp}
\end{array}
$$

where $j$ and $i$ are smooth. This induces a square

$$
\begin{array}{c}
\operatorname{LCart}^{c}(B) \xrightarrow{\mathbf{R} i_{*}} \operatorname{LCart}(D^{\sharp}) \\
\mathbf{L} v^{*} \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(5.2.4.27)} \\
\operatorname{LCart}^{c}(A) \xrightarrow{\mathbf{R} j_{*}} \operatorname{LCart}(C^{\sharp})
\end{array}
$$

that commutes up to a natural transformation

$$
\begin{array}{l}
\mathbf{L} u^{*} \circ \mathbf{R} i_{*} \quad \rightarrow \quad \mathbf{R} j_{*} \circ \mathbf{L} j^{*} \circ \mathbf{L} u^{*} \circ \mathbf{R} i_{*} \\
\quad \sim \quad \mathbf{R} j_{*} \circ \mathbf{L} v^{*} \circ \mathbf{L} i^{*} \circ \mathbf{R} i_{*} \\
\quad \rightarrow \quad \mathbf{R} j_{*} \circ \mathbf{L} v^{*}
\end{array}
\tag{5.2.4.28}
$$

A square (5.2.4.26) verifies the *opposed Beck-Chevaley condition* if $i$ and $j$ are smooth and the natural transformation (5.2.4.28) is an equivalence.

**Proposition 5.2.4.29.** *If the square (5.2.4.28) is cartesian, and $i$ and $j$ are smooth, then it verifies the opposed Beck-Chevaley condition.*

*Proof.* By adjunction, it is sufficient to show that the induced natural transformation

$$
\mathbf{L} v_{!} \circ \mathbf{R} j^{*} \to \mathbf{R} i^{*} \circ \mathbf{L} u_{!}: \operatorname{LCart}(C^{\sharp}) \to \operatorname{LCart}(B)
$$

is an equivalence. By construction, $\mathbf{L} v_{!} \circ \mathbf{R} j^{*}$ sends an object $E$ of $\operatorname{LCart}(C^{\sharp})$ onto the fibrant replacement of $v_{!} j^{*} E$. As $i$ is smooth, $\mathbf{R} i^{*} \circ \mathbf{L} u_{!}$ sends an object $E$ of $\operatorname{LCart}(C^{\sharp})$ onto the fibrant replacement of $i^{*} u_{!} E$. As pullbacks are stable under composition, we have $i^{*} u_{!} \sim v_{!} j^{*}$. $\square$

289