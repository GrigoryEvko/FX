Gel types and relativity

183

# **Rules 9.4.3 (Gel introduction).**

$$\frac{(\forall \varepsilon) \ \Psi \setminus \boldsymbol{r} \Vdash M_{\varepsilon} = M'_{\varepsilon} \in A_{\varepsilon} \qquad \Psi \setminus \boldsymbol{r} \Vdash P = P' \in R[M_0/a_0, M_1/a_1]}{\Psi \Vdash \operatorname{gel}_{\boldsymbol{r}}(M_0, M_1, P) = \operatorname{gel}_{\boldsymbol{r}}(M'_0, M'_1, P') \in \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)}$$
$$\frac{\varepsilon \in \{0, 1\} \qquad \Psi \Vdash M_{\varepsilon} \in A_{\varepsilon}}{\Psi \Vdash \operatorname{gel}_{\boldsymbol{r}}(M_0, M_1, P) = M_{\varepsilon} \in A_{\varepsilon}}$$

*Proof.* Straightforward by coherent value introduction and expansion respectively.

Finally, the projection operator ungel provides the other direction of the isomorphism: given a bridge over the Gel type, it produces a witness to the relation.

# **Rules 9.4.4 (Gel elimination).**

$$\frac{\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q = Q' \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, R)}{\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = \operatorname{ungel}(\boldsymbol{x}, Q') \in R[Q[\mathbf{0}/\boldsymbol{x}]/a_0, Q[\mathbf{1}/\boldsymbol{x}]/a_1]}$$

$$\frac{\Psi \Vdash P \in R[M_0/a_0, M_1/a_1]}{\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P)) = P \in R[M_0/a_0, M_1/a_1]}$$

$$\frac{\Psi \Vdash \boldsymbol{r} \in \mathbf{I} \qquad \Psi \setminus \boldsymbol{r} \Vdash A_0 \text{ type} \qquad \Psi \setminus \boldsymbol{r} \Vdash A_1 \text{ type}}{\Psi \setminus \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \Vdash R \text{ type} \qquad \Psi \setminus \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash Q \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0, a_1, R)}{\Psi \Vdash Q[\boldsymbol{r}/\boldsymbol{x}] = \operatorname{gel}_{\boldsymbol{r}}(Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}], \operatorname{ungel}(\boldsymbol{x}, Q)) \in \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)}$$

*Proof.* For the first, we cannot directly apply Lemma 3.1.38, because the argument $Q$ to ungel appears under a binder (of $\boldsymbol{x}$). We instead give a hand-rolled argument by coherent head expansion. (We could have instead proven a more general form of Lemma 3.1.38, but this is the only place we would use it.) By Lemma 3.1.36, we have for every $\Psi' \Vdash \psi \in \Psi$ that $Q\psi \Downarrow \operatorname{gel}_{\boldsymbol{x}}(M_{\psi}, N_{\psi}, P_{\psi})$ for some terms $M_{\psi}$, $N_{\psi}$, and $P_{\psi}$ with $\Psi', \boldsymbol{x} : \mathbf{I} \Vdash Q\psi = \operatorname{gel}_{\boldsymbol{x}}(M_{\psi}, N_{\psi}, P_{\psi}) \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, R)\psi$. By stability of typing under substitution, it follows that $P_{\operatorname{id}_{\psi}}\psi = P_{\psi} \in R[M_{\operatorname{id}_{\psi}}/a_0, N_{\operatorname{id}_{\psi}}/a_1]$ for all $\psi$. By the same and the boundary rules for gel, we also have $\Psi \gg Q[\mathbf{0}/\boldsymbol{x}] = M_{\operatorname{id}_{\psi}} \in A_0$ and likewise for $Q[\mathbf{1}/\boldsymbol{x}]$ and $N_{\operatorname{id}_{\psi}}$. Combining these, we have $\operatorname{ungel}(\boldsymbol{x}, Q)\psi \longmapsto^* P_{\psi}$ and $\Psi' \Vdash P_{\psi} = P\psi \in R[Q[\mathbf{0}/\boldsymbol{x}]/a_0, Q[\mathbf{1}/\boldsymbol{x}]/a_1]$ for all $\psi$, whence $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = P_{\operatorname{id}_{\psi}} \in R[Q[\mathbf{0}/\boldsymbol{x}]/a_0, Q[\mathbf{1}/\boldsymbol{x}]/a_1]$ by coherent head expansion.

We apply the same reasoning to the right hand side, finding that $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q') = P'_{\operatorname{id}_{\psi}} \in R[Q[\mathbf{0}/\boldsymbol{x}]/a_0, Q[\mathbf{1}/\boldsymbol{x}]/a_1]$ for some $P'_{\operatorname{id}_{\psi}}$ that satisfies the equation $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q' =$