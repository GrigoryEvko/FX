264

Cohesive parametric type theory

To show that $Fhcom(Elim^{-1}) \subseteq Elim^{-1}$, suppose we are given a pair of formal composites $fhcom^{t \to u}(M; \overline{\xi_i \hookrightarrow y.N_i}) \approx fhcom^{t \to u}(M'; \overline{\xi_i \hookrightarrow y.N_i'}) \in Fhcom(Elim^{-1})\langle\psi\rangle$. When we apply the eliminator to these values, the results reduce to composites of eliminations in the target family $B$, which are well-typed because the arguments to the formal composites belong to $\Downarrow Elim^{-1}$. It is straightforward to check that we can then apply coherent expansion to see that these reductions induce equalities, and we thereby deduce that the formal composites belong to $Elim^{-1}$ as required.

### 14.4.3 Splitting

Before we finish, there is one last construct we need to make proper use of bridge endpoint assumptions, an operator split that performs endpoint case analysis. Its operational semantics are included in Figure 14.4. This operator is easily seen to satisfy the following rules; note that in a interval context $\Psi$, any endpoint term is either 0 or 1.

Rules 14.4.14 (Splitting).

$$\begin{array}{c c c} & \Psi \Vdash r \in 2 @ m \\ \hline \Psi \Vdash A \text{ type } @ m & \Psi, r \equiv 0 \Vdash M_0 = M'_0 \in A @ m & \Psi, r \equiv 1 \Vdash M_1 = M'_1 \in A @ m \\ \hline & \Psi \Vdash \text{split}_r(M_0, M_1) = \text{split}_r(M'_0, M'_1) \in A \\ \hline \frac{\Psi \Vdash A \text{ type } @ m \quad \Psi \Vdash M_0 \in A @ m}{\Psi \Vdash \text{split}_r(M_0, M_1) = M_0 \in A} & \frac{\Psi \Vdash A \text{ type } @ m \quad \Psi \Vdash M_1 \in A @ m}{\Psi \Vdash \text{split}_r(M_0, M_1) = M_1 \in A} \end{array}$$

Proof. Immediate by coherent expansion.

□