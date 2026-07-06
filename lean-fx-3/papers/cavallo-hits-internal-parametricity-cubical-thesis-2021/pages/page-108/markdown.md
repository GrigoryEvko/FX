96

Case studies

To give a computational definition of this type, we have a number of pieces to assemble: its operational semantics (including both the constructors and eliminator), the relation named by Int$_2$, and its coercion and composition operators. To start with, it is at least clear that the constructors of the inductive type should be values, with the exception that the boundary of a path constructor should reduce as specified.

$$\overline{\operatorname{int}(M) \text{ val}} \quad \overline{\operatorname{mod}(M, x) \text{ val}} \quad \overline{\operatorname{mod}(M, 0) \longmapsto \operatorname{int}(M)} \quad \overline{\operatorname{mod}(M, 1) \longmapsto \operatorname{int}(M + 2)}$$

Naively, we might take the terms int($M$) and mod($M, x$) as the sole values of Int$_2$. For this to be sensible, however, we need to check that the Kan operations are definable. Because we have restricted our attention to a concrete HIT with no parameters, we have no problem with coercion: the only line of the form $x.\operatorname{Int}_2$ is the constant line, so we can define coercion across it as the identity function.

$$\overline{\operatorname{coe}_{x.\operatorname{Int}_2}^{r \to s}(M) \longmapsto M}$$

It is with composition that we find ourselves in hot water. Recall that hcom in particular implements symmetry and transitivity of the path relation. In order for these to be implementable in int($M$), they must hold on the level of values; for one, given any value $x : \mathbb{I} \gg V \in \operatorname{Int}_2$, there should be some inverse value $x : \mathbb{I} \gg W \in \operatorname{Int}_2$ with $W[0/x] = V[1/x] \in \operatorname{Int}_2$ and $W[1/x] = V[0/x] \in \operatorname{Int}_2$. But this clearly fails for our choice of values: we always have a path int($M$) $\rightsquigarrow$ int($M + 2$), but there is no value that provides a path int($M + 2$) $\rightsquigarrow$ int($M$). Likewise, our selection of values fails to be transitive, there being no paths int($M$) $\rightsquigarrow$ int($M + 4$) or int($M$) $\rightsquigarrow$ int($M + 6$).

We therefore have no choice but to revise our choice of values, adding new terms to stand for these values obtained by composition. Of course, we need to account not only for the special cases of symmetry and transitivity, but for all kinds of composition. We therefore introduce formal composite values, fhcom, that provide composites for every possible composition problem.

$$\begin{array}{c c c} r \neq s & (\nexists i) \xi_i \text{ satisfied} & (\nexists i) \xi_i \text{ satisfied} \\ \hline \operatorname{fhcom}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \text{ val} & & \overline{\operatorname{fhcom}^{r \to r}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto M} \\ & \frac{(\nexists i < k) \xi_i \text{ satisfied} \quad \xi_k \text{ satisfied}}{\operatorname{fhcom}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}) \longmapsto N_k[s/x]} \end{array}$$

The reduction rules for fhcom line up exactly with the equations imposed in the definition of composition (Definition 3.1.27). By adding fhcom values to our definition of the