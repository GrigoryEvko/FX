Cubical computational type theory 61

of coe and hcom at each value type. We give two examples—function and path types—in Figure 3.2. In each case, coercion and composition at the compound type reduce to coercion and composition at the component types. To coerce a function along the type line $x.(A \rightarrow B)$ from $r$ to $s$, for example, we precompose with a reversed coercion $\text{coe}_{x.A}^{s \rightarrow r}$ in the domain type and then postcompose with a coercion $\text{coe}_{x.B}^{r \rightarrow s}$ in the codomain type, thus transforming a function of type $A[r/x] \rightarrow B[r/x]$ into one of type $A[s/x] \rightarrow B[s/x]$.

The evaluation of coercion for paths, meanwhile, relies on *heterogeneous composition*, a compound operation derived from coercion and homogeneous composition. Heterogeneous composition combines the functionality of the two Kan operations, coercing the base term $M$ along a type line $x.A$ while maintaining a tube of paths $\xi_i \hookrightarrow x.N_i$ lying over said line of types.

**Definition 3.1.30.** We define the heterogeneous composition operator, com, as follows.

$$\text{com}_{x.A}^{r \rightarrow s}(M; \overline{\xi_i \hookrightarrow x.N_i}) := \text{hcom}_{A[s/x]}^{r \rightarrow s}(\text{coe}_{x.A}^{r \rightarrow s}(M); \overline{\xi_i \hookrightarrow x.\text{coe}_{x.A}^{x \rightarrow s}(N_i)})$$

**Rules 3.1.31 (Heterogeneous composition).** For the following rules, we assume type lines $\Gamma, x : \mathbb{I} \gg A = A'$ type, interval terms $\Gamma \gg r = r' \in \mathbb{I}$ and $\Gamma \gg s = s' \in \mathbb{I}$, and constraints $\Gamma \gg \xi_i = \xi_i' \in \mathbb{F}$ for some $0 \leq i < n$.

$$\begin{array}{c} \Gamma \gg M = M' \in A[r/x] \\ (\forall i, j) \; \Gamma, \xi_i, \xi_j, x : \mathbb{I} \gg N_i = N'_j \in A \quad (\forall i) \; \Gamma, \xi_i \gg M = N_i[r/x] \in A[r/x] \\ \hline \Gamma \gg \text{com}_{x.A}^{r \rightarrow s}(M; \overline{\xi_i \hookrightarrow x.N_i}) = \text{com}_{x.A'}^{r' \rightarrow s'}(M'; \overline{\xi_i' \hookrightarrow x.N_i'}) \in A[s/x] \end{array}$$

$$\begin{array}{c} \Gamma \gg M \in A[r/x] \\ (\forall i, j) \; \Gamma, \xi_i, \xi_j, x : \mathbb{I} \gg N_i = N_j \in A \quad (\forall i) \; \Gamma, \xi_i \gg M = N_i[r/x] \in A[r/x] \\ \hline \Gamma \gg \text{com}_{x.A}^{r \rightarrow r}(M; \overline{\xi_i \hookrightarrow x.N_i}) = M \in A[s/x] \end{array}$$

$$\begin{array}{c} \Gamma \gg \xi_k \text{ satisfied} \quad \Gamma \gg M \in A[r/x] \\ (\forall i, j) \; \Gamma, \xi_i, \xi_j, x : \mathbb{I} \gg N_i = N_j \in A \quad (\forall i) \; \Gamma, \xi_i \gg M = N_i[r/x] \in A[r/x] \\ \hline \Gamma \gg \text{com}_{x.A}^{r \rightarrow s}(M; \overline{\xi_i \hookrightarrow x.N_i}) = N_k[s/x] \in A[s/x] \end{array}$$

*Proof.* Straightforward consequences of the defining rules for coercion and composition in types (given in Section 3.1.4). $\square$

The definition of coercion at path types demonstrates the necessity of the composition operator. To ensure that the result of coercing has the necessary endpoints, we need an operation that maintains them. The definition of homogeneous composition at the path