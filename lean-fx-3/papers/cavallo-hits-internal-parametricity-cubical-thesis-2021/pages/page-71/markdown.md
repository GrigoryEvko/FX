Cubical computational type theory 59

We use the notation $\overrightarrow{x}$ to denote lists (here of entries $\xi_i \hookrightarrow x.N_i$), leaving quantification over the indexing variable (here $i$) implicit for sake of concision. In short, $R$ has homogeneous composition when we can compose in any instance $R\psi$; the result must fit into the tube $\overrightarrow{\xi_i \hookrightarrow x.N_i}$ instantiated at $s$, and the trivial composition $r \to r$ is required to be the identity. In order for a tube to be well-formed, its entries must agree where their equations overlap; this is effected by the requirement $\Psi', \xi_i, \xi_j, x : \mathbb{I} \gg N_i \approx N_j \in R\psi$.

We say that $\Psi \Vdash A = A'$ pretype support composition when $[[A]]$ supports composition at $A, A'$.

*Remark 3.1.28.* As above, we use the word *trivial* to describe coercions and composites $r \to r$; *degenerate*, one the other hand, refers to paths of the form $\lambda^\mathbb{I} \dots M$.

**Definition 3.1.29 (Kan types).**

- *Closed types:* $\Psi \Vdash A = A'$ type is defined to hold when $\Psi \Vdash A = A'$ pretype support coercion and homogeneous composition.
- *Open types:* $\Gamma \gg A = A'$ type is defined to hold when $\Psi \Vdash A\gamma = A'\gamma'$ type holds for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

Like the pretype judgment, the closed type judgment is stable under interval substitution by construction: if $\Psi' \Vdash \psi \in \Psi$ and $\Psi \Vdash A = A'$ type, then $\Psi' \Vdash A\psi = A'\psi$ type.

This completes the derivation of the type-theoretic judgments from an operational semantics and type system. We leave the definition of $\Gamma' \gg \gamma = \gamma' \in \Gamma$ to the reader, this being simple to extrapolate from Definition 2.1.18 and the definition of closing substitutions above.

### 3.1.5 Constructing a cubical type theory

We now upgrade our examples of type systems to include cubical elements. To the syntax described in Section 2.1, we add the following terms for path types, V *types* (to be introduced below), and the Kan operations.

$$\begin{aligned} A, B, M, N, I & ::= \cdots \\ & | \text{Path}(x.A, M, N) | \lambda^\mathbb{I} x.M | Pr \\ & | \text{V}_r(A, B, I) | \text{v}_r(M, N) | \text{vproj}_r(M, I) \\ & | \text{coe}_{x.A}^{r \to s}(M) | \text{hcom}_A^{r \to s}(M; \overrightarrow{\xi_i \hookrightarrow x.N_i}) \end{aligned}$$

We give the operational semantics for formation, introduction, and elimination of path and V types in Figure 3.1. In addition to these, we must also describe the evaluation