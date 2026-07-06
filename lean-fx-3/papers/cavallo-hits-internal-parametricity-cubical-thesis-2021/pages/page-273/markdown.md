Modal types

261

$\operatorname{hcom}_{A}^{r\to s}(\operatorname{unmod}(P); \overline{\xi_{i} \hookrightarrow x.\operatorname{unmod}(P_{i})}) \in A @ m$. Finally, we apply the introduction rule to obtain the composite in $\langle \mu \mid A \rangle$, which clearly has the necessary boundary by the equations for the composite in $A$.

### 14.4.2 The discrete type

Unlike the other two modal types, the discrete type is defined by a modality cc with no left adjoint, so the previous approach is unavailable. Instead, we give a dependent elimination principle, a case analysis operator analogous to that used for inductive types. Again, there is an analogy to Shulman's presentation of cohesion, wherein the b operator corresponding to the composite $\operatorname{Disc}(\operatorname{Glo}(-))$ is axiomatized in a positive style.

The first step is to confirm that formal composites are also elements of the type, which in turn implies that the type supports composition.

**Rule 14.4.9 (Formal composites in the discrete type).** Given $\Psi.\operatorname{cc} \gg A$ type @ pt, $\Psi \Vdash r, s \in \mathbb{I} @ \text{par}$ and $\Psi \Vdash \xi_{i} \in \mathbb{F} @ \text{par}$ for all $i$, the following rules are validated.

$$\begin{array}{c} \Psi \Vdash M = M' \in \operatorname{Disc}(A) @ \text{par} \quad (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \gg N_i = N'_j \in \operatorname{Disc}(A) @ \text{par} \\ (\forall i) \Psi, \xi_i \gg M = N_i[r/x] \in \operatorname{Disc}(A) @ \text{par} \end{array}$$

$$\Vdash \operatorname{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) = \operatorname{fhcom}^{r\to s}(M'; \overline{\xi_i \hookrightarrow x.N'_i}) \in \operatorname{Disc}(A) @ \text{par}$$

$$\begin{array}{c} \Psi \Vdash M \in \operatorname{Disc}(A) @ \text{par} \quad (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \gg N_i = N_j \in \operatorname{Disc}(A) @ \text{par} \\ (\forall i) \Psi, \xi_i \gg M = N_i[r/x] \in \operatorname{Disc}(A) @ \text{par} \end{array}$$

$$\Psi \Vdash \operatorname{fhcom}^{r\to r}(M; \overline{\xi_i \hookrightarrow x.N_i}) = M \in \operatorname{Disc}(A) @ \text{par}$$

$$\begin{array}{c} \Psi \Vdash \xi_k \text{ satisfied } @ \text{ par} \\ \Psi \Vdash M \in \operatorname{Disc}(A) @ \text{ par} \quad (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \gg N_i = N_j \in \operatorname{Disc}(A) @ \text{ par} \\ (\forall i) \Psi, \xi_i \gg M = N_i[r/x] \in \operatorname{Disc}(A) @ \text{ par} \end{array}$$

$$\Psi \Vdash \operatorname{fhcom}^{r\to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) = N_k[s/x] \in \operatorname{Disc}(A) @ \text{par}$$

*Proof.* A by-now standard argument by coherent introduction and head expansion. For details, see the proof of the more general Lemma 6.2.15 in Part II.

**Lemma 14.4.10 (Composition).** $\Psi \Vdash \operatorname{Disc}(A) = \operatorname{Disc}(A')$ pretype @ par support composition for any $\Psi.\operatorname{cc} \gg A = A'$ type @ pt.

*Proof.* This follows as a corollary of Rule 14.4.9 by coherent head expansion: composites in the discrete type reduce to formal composites, which are well-typed and satisfy the necessary boundary equations.