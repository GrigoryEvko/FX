Cubical computational type theory 69

function $fst(I)$ of the isomorphism. Thus V types provide an inverse to the function that converts paths of types to isomorphisms using coe.

The precise formulation of V is slightly more subtle: rather than merely creating a path from an isomorphism, V actually *composes* an isomorphism onto an existing path to produce a new path. That is, given $\Psi \Vdash A$ type, a path $\Psi, x : \mathbb{I} \Vdash B$ type, and an isomorphism $\Psi \Vdash I \in A \simeq B[0/x]$ between A and the zero endpoint of B, the type $\Psi, x : \mathbb{I} \Vdash V_x(A, B, I)$ type is a path between A and the one endpoint of B. The V type therefore connects the two ends of a “V” shape formed by I and B.

$$\begin{array}{c} A \\ I \quad \Downarrow \\ B[0/x] \xrightarrow[B]{} B[1/x] \\ x \rightarrow \end{array}$$

When B happens to be a *degenerate* path, we recover the picture of a path directly constructed from an isomorphism.

Put in terms of an arbitrary interval term r, as opposed to a variable x, we arrive at the following formation and boundary rules, which require the arguments A and I to exist only under the constraint $r \equiv 0$.

**Rules 3.1.45 (V type formation).**

$$\begin{array}{c} \Psi, r \equiv 0 \gg A = A' \text{ type} \quad \Psi \Vdash r \in \mathbb{I} \\ \hline \Psi \Vdash V_r(A, B, I) = V_r(A', B', I') \text{ pretype} \end{array} \quad \begin{array}{c} \Psi, r \equiv 0 \gg I = I' \in A \simeq B \\ \hline \Psi \Vdash A \text{ type} \\ \hline \Psi \Vdash V_0(A, B, I) = A \text{ pretype} \end{array}$$

*Proof.* The reduction rules follow immediately from coherent head expansion, as we have $V_0(A, B, I)\psi \longmapsto A\psi$ and $V_1(A, B, I)\psi \longmapsto B\psi$ for all interval substitutions $\psi$. For the formation rule, we go by the coherent value lemma applied to $\tau_i[R]$, where R is the $\Psi$-PER assigned to the V type in Example 3.1.32. For a given $\Psi' \Vdash \psi \in \Psi$, we are in one of the following cases.

- Case: $r\psi = 0$. Then by the reduction rule already proven, we have $\Psi' \Vdash V_{r\psi}(A, B, I) = A$ pretype and $\Psi' \Vdash V_{r\psi}(A', B', I') = A'$ pretype. By transitivity, it follows that $\Psi' \Vdash V_r(A, B, I)\psi = V_r(A', B', I')\psi$ pretype.
- Case: $r\psi = 1$. Symmetric to the previous case.