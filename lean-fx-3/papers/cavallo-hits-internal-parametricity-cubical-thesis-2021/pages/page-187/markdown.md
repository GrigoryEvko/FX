Bridge types

175

$$\frac{\Psi, \boldsymbol{x} : \mathbf{I} \Vdash A = A' \text{ type} \quad \Psi \Vdash M_0 = M'_0 \in A[\mathbf{0}/\boldsymbol{x}] \quad \Psi \Vdash M_1 = M'_1 \in A[\mathbf{1}/\boldsymbol{x}]}{\Psi \Vdash \text{Bridge}(\boldsymbol{x}.A, M_0, M_1) = \text{Bridge}(\boldsymbol{x}.A', M'_0, M'_1) \text{ type}}$$

$$\frac{\Psi, \boldsymbol{x} : \mathbf{I} \Vdash A \text{ type} \quad \Psi, \boldsymbol{x} : \mathbf{I} \Vdash M = M' \in A}{\Psi \Vdash \lambda^\mathbf{I} a. M = \lambda^\mathbf{I} a. M' \in \text{Bridge}(\boldsymbol{x}.A, M[\mathbf{0}/\boldsymbol{x}], M[\mathbf{1}/\boldsymbol{x}])}$$

$$\frac{\Psi, \boldsymbol{x} : \mathbf{I} \Vdash A \text{ type} \quad (\forall \varepsilon) \Psi \Vdash M_\varepsilon \in A[\varepsilon/\boldsymbol{x}]}{\Psi \Vdash \boldsymbol{r} \in \mathbf{I} \quad \Psi \setminus \boldsymbol{r} \Vdash P = P' \in \text{Bridge}(\boldsymbol{x}.A, M_0, M_1)} \\ \hline \Psi \Vdash P \boldsymbol{r} = P' \boldsymbol{r} \in A[\boldsymbol{r}/\boldsymbol{x}]$$

$$\frac{\Psi \setminus \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash A \text{ type} \quad \Psi \Vdash \boldsymbol{r} \in \mathbf{I} \quad \Psi \setminus \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash M \in A}{\Psi \Vdash (\lambda^\mathbf{I} \boldsymbol{x}.M) \boldsymbol{r} = M[\boldsymbol{r}/\boldsymbol{x}] \in A[\boldsymbol{r}/\boldsymbol{x}]}$$

$$\frac{\Psi, \boldsymbol{x} : \mathbf{I} \Vdash A \text{ type} \quad (\forall \varepsilon) \Psi \Vdash M_\varepsilon \in A[\varepsilon/\boldsymbol{x}]}{\Psi \Vdash P \in \text{Bridge}(\boldsymbol{x}.A, M_0, M_1) \quad \varepsilon \in \{0, 1\}} \\ \hline \Psi \Vdash P \varepsilon = M_\varepsilon \in A[\varepsilon/\boldsymbol{x}]$$

$$\frac{\Psi, \boldsymbol{x} : \mathbf{I} \Vdash A \text{ type} \quad (\forall \varepsilon) \Psi \Vdash M_\varepsilon \in A[\varepsilon/\boldsymbol{x}] \quad \Psi \Vdash P \in \text{Bridge}(\boldsymbol{x}.A, M_0, M_1)}{\Psi \Vdash P = \lambda^\mathbf{I} \boldsymbol{x}. P \boldsymbol{x} \in \text{Bridge}(\boldsymbol{x}.A, M_0, M_1)}$$

Figure 9.2: Rules for bridge types

bridge $P$ with a term $\boldsymbol{r}$ that already occurs in $P$. This matches the situation for judgmental bridges: given $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash M \in A$, we can only instantiate $\boldsymbol{x}$ with some $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$ if $M$ and $A$ are actually well-typed in the sub-context $(\Psi \setminus \boldsymbol{r}, \boldsymbol{x} : \mathbf{I}) \subseteq (\Psi, \boldsymbol{x} : \mathbf{I})$, in which case we can apply the substitution $\Psi \Vdash (\text{id}_{\Psi \setminus \boldsymbol{r}}, \boldsymbol{r}/\boldsymbol{x}) \in (\Psi \setminus \boldsymbol{r}, \boldsymbol{x} : \mathbf{I})$ to get $\Psi \Vdash M[\boldsymbol{r}/\boldsymbol{x}] \in A[\boldsymbol{r}/\boldsymbol{x}]$.

As the proofs of these rules do not deviate noticeably from those for path types (Section 3.1.6.1), we leave them as an exercise to the reader; the Kan operations, too, are the same as for paths, though now relying on the presence of $\boldsymbol{r} \equiv \varepsilon$ constraints. (Full proofs may be found in [CH19b, §5].) However, it is worth observing explicitly that, even with the complication of restriction in hypotheses, we can still derive open rules from their closed form, as in the example below. As mentioned above, the key fact is that interval restriction has an action on closing substitutions.

**Rule 9.2.1 (Open bridge reduction).** Let $\Gamma$ ctx.

$$\frac{\Gamma, \boldsymbol{x} : \mathbf{I} \gg A \text{ type} \quad \Gamma \gg \boldsymbol{r} \in \mathbf{I} \quad \Gamma \setminus \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \gg M \in A}{\Gamma \gg (\lambda^\mathbf{I} \boldsymbol{x}.M) \boldsymbol{r} = M[\boldsymbol{r}/\boldsymbol{x}] \in A[\boldsymbol{r}/\boldsymbol{x}]}$$