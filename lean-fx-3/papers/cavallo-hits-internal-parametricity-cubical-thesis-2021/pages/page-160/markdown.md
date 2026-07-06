148 General higher inductive types

We can see an int(3) somewhere inside, and this term is indeed equal to int(3) up to a path, but it is buried beneath a pile of “frivolous” formal coercions and composites. Note that there can be no truly significant coercions or composites in a non-indexed type in an empty context. There are no indices to coerce between, and the boundary constraints of a composite will either be true (0 ≡ 0 or 0 ≡ 1), in which case the composite reduces, or false (0 ≡ 1 or 1 ≡ 0), in which case they are irrelevant.

The problem of coercions is easy to solve; we can simply add a rule to the operational semantics so that such frivolous coercions reduce away. (To keep the operational semantics deterministic, we should also add a condition that δ ≠ · on rules that operate on fcoe$_{x,δ}^{r→s}$(M) values.)

$$\frac{r \neq s}{\text{fcoe}_{x,\cdot}^{r\rightarrow s}(M) \longmapsto M}$$

Compositions are less simple, however, because a non-frivolous composite can become a frivolous composite through interval substitution. It takes a few steps to dig up how this becomes a problem; to start, recall the reduction of the inductive type eliminator applied to a formal composite (Figure 6.7).

$$\begin{array}{c} \text{elim}(\bar{v}_{\delta}.h.D; \delta; \text{fhcom}^{r\rightarrow s}(M; \overrightarrow{\xi_i \hookrightarrow x.N_i}); \mathcal{E}) \\ \longmapsto \\ \text{com}_{x.D[\delta',F_x/h]}^{r\rightarrow s}(\text{elim}(\bar{v}_{\delta}.h.D; \delta; M; \mathcal{E}); \overrightarrow{\xi_i \hookrightarrow x.\text{elim}(\bar{v}_{\delta}.h.D; \delta; N_i; \mathcal{E})) \end{array}$$

For this application of the eliminator to be well-typed (i.e., for Lemma 6.4.9 to go through), this reduction must be coherent. If some interval substitution makes the input fhcom frivolous, causing it to reduce to its cap, the right hand side must simplify in a corresponding way. Essentially, if frivolous fhcom terms are made equal to their caps, then, so must all frivolous compositions be equal to their caps.$^1$ In particular, a coercion in a degenerate type line must be equal to its input: coe$_{A}^{r\rightarrow s}(M) = M$. Because of the way composition in path types is defined, ensuring this further requires that any composite with a degenerate type line and tube is equal to its cap: com$_{A}^{r\rightarrow s}(M; \overrightarrow{\xi_i \hookrightarrow \dots N_i}) = M$.

Unfortunately, it is apparently impossible to impose this condition, known variously as regularity [CCHM15, Acknowledgements] or normality [Awo18, Definition 31], without compromising either univalence or constructivity. The reasons are beyond the scope of this work: the obstruction is composition in the universe, which we have studiously avoided defining. For an illustration of the problems with regularity at the universe type, see [Ang19, §3.4]. More formally, Swan shows that reconciling regularity with univalence requires non-constructivity in a large class of cubical models of type theory [Swa18b].

$^1$Alternatively, this reduction rule must be changed in some way—pursuing that option leads to similar conclusions.