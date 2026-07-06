8. For any $A \in Ob_\lambda(\mathcal{C})$, a map $A \twoheadrightarrow B$ and any map $f: C \to B$ there is a pullback square

$$\begin{array}{ccc} f^*A & \xrightarrow{q(f,A)} & A \\ f^*p \downarrow & & \downarrow^p \\ C & \xrightarrow{f} & B \end{array}$$

called *canonical pullback* of $A$ along $f$, and we require $lt(f^*p) = lt(p)$.

9. Canonical pullbacks are strictly functorial: for ordinals with $\mu \leq \lambda$, $A \in Ob_\lambda(\mathcal{C})$

- (a) If $f = id_B$ then $id_B^*A = A$ and $q(id_B, A) = id_A$.
- (b) For a diagram

$$\begin{array}{ccc} & & A \\ & & \downarrow^p \\ D & \xrightarrow{g} & C \xrightarrow{f} & B, \end{array}$$

we have that $g^*(f^*(A)) = (fg)^*(A)$ and $q(fg, A) = q(f, A)q(g, f^*A)$.

10. Given display maps $p: A \twoheadrightarrow B$ and $q: B \to C$ and any $f: X \to C$, in the diagram

$$\begin{array}{ccc} q(f,B)^*A & \xrightarrow{q(q(f,B),A)} & A \\ q(f,B)^*p \downarrow & & \downarrow^p \\ f^*B & \xrightarrow{q(f,B)} & B \\ f^*r \downarrow & & \downarrow^r \\ X & \xrightarrow{f} & C, \end{array}$$

we have that $f^*r \circ (q(f,B)^*p) = f^*(r \circ p)$ and $q(q(f,B), A) = q(f, A)$.

*Remark B.2.* We use the term “display map” in a rather different way to Cartmell. For us, a display map can have any height, and it is only bounded by the regular cardinal $\kappa$.

We have already seen one example of such a category.

**Corollary B.3.** *For any generalized $\kappa$-algebraic theory $T$ the syntactic category $\mathbb{C}_T$ is a $\kappa$-contextual category.*

*Proof.* This is done throughout section A.5. $\square$

112