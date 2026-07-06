70

Cubical type theory

- Case: $r\psi = x$. Then $V_r(A, B, I)\psi$ and $V_r(A', B', I')\psi$ are values, and we have $\tau_i \vDash \Psi' \Vdash V_r(A, B, I)\psi \approx V_r(A', B', I')\psi \downarrow R_\psi$ by definition of the type system. $\square$

The above proof is representative of the shape of formation and introduction proofs for types with unstable operational semantics. Typically, the boundary of a term reduces in some way, in which case we apply some reduction rules to simplify the goal to an equation we already know to hold. When we are not on the boundary, on the other hand, the terms in question are typically values.

A value of the type $\Psi, x : \mathbb{I} \Vdash V_x(A, B, I)$ type is a term $v_x(M, P)$, which collects a line $\Psi, x : \mathbb{I} \Vdash P \in B$ in direction $x$ with a term $\Psi \vdash M : A$, living at $x \equiv 0$, which is mapped by $fst(I)$ to $P[0/x]$. This data parallels the shape of the V type itself.

$$\begin{array}{c c c} M & \\ I \downarrow & \searrow v_x(M, P) \\ P[0/x] & \xrightarrow{\quad} P[1/x] \\ x \to & \end{array} \qquad \in \qquad \begin{array}{c c c} A & \\ I \Downarrow & \searrow V_x(A, B, I) \\ B[0/x] & \xrightarrow{\quad} B[1/x] \\ x \to & \end{array}$$

We see intuitively that the dependent paths over the V type, i.e., the elements of some type $\text{Path}(x.V_x(A, B, I), M, N)$, correspond to paths in $B$ establishing that $M$ and $N$ correspond to each other across the isomorphism $I$. That is, the prototypical element of this path type is of the form $\lambda x.v_x(M, P)$ where $\Psi \Vdash P[0/x] = (fst(I)) M \in B$ and $\Psi \Vdash P[1/x] = N \in B$.

### Rules 3.1.46 (V type introduction).

$$\frac{\Psi \Vdash r \in \mathbb{I} \qquad \Psi, r \equiv 0 \gg I \in A \simeq B}{\Psi, r \equiv 0 \gg M = M' \in A \qquad \Psi \Vdash N = N' \in B \qquad \Psi, r \equiv 0 \gg (fst(I)) M = N \in B} \\ \hline \Psi \Vdash v_r(M, N) = v_r(M', N') \in V_r(A, B, I)$$

$$\frac{\Psi \Vdash M \in A}{\Psi \Vdash v_0(M, N) = M \in A} \qquad \frac{\Psi \Vdash N \in B}{\Psi \Vdash v_1(M, N) = N \in B}$$

We leave the proofs of these rules as an exercise to the reader; they follow the same pattern as the proof of the formation rules.

The elimination operator for V types extracts an element of $B$. With the reduction rules for V types, we have examples of coherent head expansion where the reduction rule is not stable under substitution.