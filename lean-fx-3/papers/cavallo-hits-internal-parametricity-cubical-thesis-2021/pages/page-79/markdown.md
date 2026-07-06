Cubical computational type theory 67

The introduction rule shows that the relation named by the path type is itself value-coherent. Formally, this result is a prerequisite to defining the candidate type system, but there is no real circularity here, only a perversion of the conceptual order for presentation's sake.

For elimination, it is convenient to prove the reduction rule *before* the binary elimination rule itself. At this point we switch from blindly applying value introduction to blindly applying coherent head expansion (Lemma 3.1.35).

# **Rule 3.1.41 (Path reduction).**

$$\frac{\Psi, x : \mathbb{I} \Vdash A \text{ type} \quad \Psi, x : \mathbb{I} \Vdash M \in A \quad \Psi \Vdash r \in \mathbb{I}}{\Psi \Vdash (\lambda^\mathbb{I} x \cdot M) r = M[r/x] \in A[r/x]}$$

*Proof.* By substitution, we know that $\Psi \Vdash M[r/x] \in A[r/x]$. For all $\Psi' \Vdash \psi \in \Psi$, we have $((\lambda^\mathbb{I} x \cdot M) r) \psi \longmapsto M[r/x] \psi$, so $\Psi \Vdash (\lambda^\mathbb{I} x \cdot M) r = M[r/x] \in A[r/x]$ by coherent expansion. $\square$

As path application evaluates its principal argument, we use the elimination lemma (Lemma 3.1.38) to prove its well-typedness.

# **Rule 3.1.42 (Path elimination).**

$$\frac{\begin{array}{c} \Psi, x : \mathbb{I} \Vdash A \text{ type} \quad (\forall \varepsilon) \Psi \Vdash M_\varepsilon \in A[\varepsilon/x] \\ \Psi \Vdash P = P' \in \text{Path}(x \cdot A, M_0, M_1) \quad \Psi \Vdash r \in \mathbb{I} \end{array}}{\Psi \Vdash P r = P' r \in A[r/x]}$$

*Proof.* By applying Lemma 3.1.38 with the eager terms $(-) r$ and $(-) r$, it suffices to prove that for every $\Psi' \Vdash \psi \in \Psi$ and $\Psi', x : \mathbb{I} \Vdash M = M' \in A\psi$, we have $\Psi' \Vdash (\lambda^\mathbb{I} x \cdot M) (r\psi) = (\lambda^\mathbb{I} x \cdot M') (r\psi) \in A[r/x]\psi$. By substitution, we have $\Psi' \Vdash M[r\psi/x] = M'[r\psi/x] \in A[r/x]\psi$, from which the necessary equation follows by applying path reduction on either side. $\square$

In addition to the usual suite of rules, we also want to know that the endpoints of a path element are equal to those prescribed by its type. For this we use the evaluation lemma (Lemma 3.1.36) to reduce to the case where the path is a value. Here we need that the relation named by the path type is value-coherent, which we established with the introduction rule.

# **Rule 3.1.43 (Path boundary).**

$$\frac{\begin{array}{c} \Psi, x : \mathbb{I} \Vdash A \text{ type} \quad (\forall \varepsilon) \Psi \Vdash M_\varepsilon \in A[\varepsilon/x] \\ \Psi \Vdash P \in \text{Path}(x \cdot A, M_0, M_1) \quad \varepsilon \in \{0, 1\} \end{array}}{\Psi \Vdash P \varepsilon = M_\varepsilon \in A[\varepsilon/x]}$$