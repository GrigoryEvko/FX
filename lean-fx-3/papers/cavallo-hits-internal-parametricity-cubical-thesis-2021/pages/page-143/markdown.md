Kan operations 131

Proof. By Lemma 6.2.14.

**Rule 6.2.28 (Formal composition introduction).** Let $\Psi \Vdash \Delta \blacktriangleright \mathcal{K}$ spec and $\Psi \Vdash \delta \in \Delta$ be given together with interval terms $\Psi \Vdash r, s \in \mathbb{I}$, and constraints $\Psi \Vdash \xi_i \in \mathbb{F}$ for $0 \leq i < n$.

$$\begin{array}{c} \Psi \Vdash M = M' \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \Vdash N_i = N'_j \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \quad (\forall i) \Psi, \xi_i \Vdash M = N_i[r/x] \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ \hline \Psi \Vdash \text{fhcom}^{r \rightarrow s}(M; \overline{\xi_i \hookrightarrow x.N'_i}) = \text{fhcom}^{r \rightarrow s}(M'; \overline{\xi_i \hookrightarrow x.N'_i}) \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ \hline \Psi \Vdash M \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \Vdash N_i = N_j \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \quad (\forall i) \Psi, \xi_i \Vdash M = N_i[r/x] \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ \hline \Psi \Vdash \text{fhcom}^{r \rightarrow r}(M; \overline{\xi_i \hookrightarrow x.N'_i}) = M \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ \hline \Psi \Vdash \xi_k \text{ satisfied} \quad \Psi \Vdash M \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ (\forall i, j) \Psi, \xi_i, \xi_j, x : \mathbb{I} \Vdash N_i = N_j \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \quad (\forall i) \Psi, \xi_i \Vdash M = N_i[r/x] \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ \hline \Psi \Vdash \text{fhcom}^{r \rightarrow s}(M; \overline{\xi_i \hookrightarrow x.N'_i}) = N_k[s/x] \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \end{array}$$

Proof. By Lemma 6.2.15.

## 6.3 Kan operations

We now show that the inductive pretypes are indeed types by proving the typing rules and boundary conditions for the Kan operators at inductive type. The operational semantics for these operations are shown in Figure 6.6.

We dispatch with composition first: support follows immediately from the existence and well-typedness of formal composites in the inductive type.

**Theorem 6.3.1 (Composition).** $\Psi \Vdash \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) = \text{Ind}_{\mathcal{K}'}^{\Delta'}(\delta')$ pretype support homogeneous composition for any $\Psi \Vdash \Delta = \Delta'$ tel, $\Psi \Vdash \Delta \blacktriangleright \mathcal{K} = \mathcal{K}'$ spec, and $\Psi \Vdash \delta = \delta' \in \Delta$.

Proof. Any hcom in a higher inductive type reduces to an fhcom term, as shown in Figure 6.6. Support for homogeneous composition therefore follows immediately from Lemma 6.2.15.

As one piece of coercion in inductive types, we must be able to apply coercion to a list of arguments. We therefore extend coercion from types to telescopes, coercing them as we might elements of product types. Defined in Figure 6.6, this operator satisfies the following rules.