Strengthening canonicity

147

Proof. By coherent head expansion. Let $\Psi'' \Vdash \psi \in \Psi$ be given. We are in one of two cases.

- There is some minimal $k$ such that $\Psi'' \Vdash \xi_k \psi'$ satisfied. Then we have the following reduction.

$$\text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; \text{intro}_{\ell}^{\mathcal{K}''}(\phi; \omega; \chi); \mathcal{E}\psi)\psi'$$

$$\longmapsto$$

$$\text{elim}(\bar{v}_{\Delta}.h.D\psi; \delta; (\Theta.M_k[\phi, \omega])_{\mathcal{K}''}(\chi); \mathcal{E}\psi)\psi'$$

By Lemma 6.4.13, the latter term is equal to $(\Theta.M_k[\phi, \omega])_{\mathcal{K}'',\mathcal{E}\psi}^{\Delta.h.D\psi}(\chi; \rho)\psi'$ as an element of $D\psi[\delta, \text{intro}_{\ell}^{\mathcal{K}''}(\phi; \omega; \chi)/h]\psi'$, which is in turn equal to $T[\phi, \omega, \chi, \rho]\psi'$ by the requirements on the clause $(\ell: \bar{v}_{\text{H}}.T) \in \mathcal{E}\psi$ imposed by $\Psi \Vdash \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} \in [\mathcal{K} \Rightarrow h.D]$.

- There is no $k$ such that $\Psi'' \Vdash \xi_k \psi'$ satisfied. Then the left hand side steps to the right hand side, which is well-typed by $\Psi \Vdash \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} \in [\mathcal{K} \Rightarrow h.D]$. $\square$

Corollary 6.4.16. $Intro_{\ell}^{\mathcal{K}}(Elim^{-1}) \subseteq Elim^{-1}$ for all $\ell \in \mathcal{K}$.

Proof. By induction on the height of $\ell$, first applying Lemma 6.4.13 and then Lemma 6.4.15. $\square$

Rule 6.4.17 (Elimination).

$$\begin{array}{c} \Psi \Vdash \Delta \text{ tel} \quad \Psi \Vdash \Delta \blacktriangleright \mathcal{K} \text{ spec} \quad \Psi, \Delta, h: \text{Ind}_{\mathcal{K}}^{\Delta}(\bar{v}_{\Delta}) \gg D = D' \text{ type} \\ \Psi \Vdash \Delta \mid \mathcal{K} \blacktriangleright \mathcal{E} = \mathcal{E}' \in [\mathcal{K} \Rightarrow h.D] \quad \Psi \Vdash \delta = \delta' \in \Delta \quad \Psi \Vdash M = M' \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) \\ \hline \Psi \Vdash \text{elim}(\bar{v}_{\Delta}.h.D; \delta; M; \mathcal{E}) = \text{elim}(\bar{v}_{\Delta}.h.D'; \delta'; M'; \mathcal{E}') \in D[\delta, M/h] \end{array}$$

Proof. By the combination of Lemmas 6.4.7, 6.4.9 and 6.4.15, Lemma 6.4.6, and the definition of $Ind_{\mathcal{K}}$ as the least fixed-point of $Step^{\mathcal{K}}$. $\square$

## 6.5 Strengthening canonicity

By definition of the typing judgment, any well-typed term $\Psi \Vdash M \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta)$ is guaranteed to compute to a value belonging to the inductive relation $Ind_{\mathcal{K}}$. Such a value is of one of three kinds: it may be a constructor term (intro), but it may also be a formal coercion (fcoe) or composite (fhcom).

This is a broader range of possibilities than one would like, especially in the case that $\Psi$ is empty. For example, we might compute a term $\cdot \Vdash M \in \text{Int}_2$ (an integer modulo 2, as defined in Section 5.1) and get the following unsightly result.

$$\text{fcoe}_{x,\cdot}^{0\to 1}(\text{fhcom}^{0\to 1}(\text{fhcom}^{0\to 1}(\text{fcoe}_{x,\cdot}^{1\to 0}(\text{int}(3)); \cdot); 0 \equiv 1 \hookrightarrow \dots\text{int}(8)))$$