Quotients and pushouts

101

in the concrete case, arriving at the following typing rule.

$$\begin{array}{l} q: A \parallel R \gg D \text { type } \quad M \in A \parallel R \quad a: A \gg T_{\mathrm{pt}} \in D[\mathrm{pt}(a) / q] \\ a: A, a^{\prime}: A, r: R\langle a, a^{\prime} \rangle, x: \mathbb{I} \gg T_{\mathrm{rel}} \in D[\mathrm{rel}(a, a^{\prime}, r, x) / q] \\ a: A, a^{\prime}: A, r: R\langle a, a^{\prime} \rangle \gg T_{\mathrm{rel}}[0 / x]=T_{\mathrm{pt}} \in D[\mathrm{pt}(a) / q] \\ a: A, a^{\prime}: A, r: R\langle a, a^{\prime} \rangle \gg T_{\mathrm{rel}}[1 / x]=T_{\mathrm{pt}}[a^{\prime} / a] \in D[\mathrm{pt}(a^{\prime}) / q] \\ \hline \operatorname{elim}(q, D; M; a, T_{\mathrm{pt}}, a, a^{\prime}, r, x, T_{\mathrm{rel}}) \in D[M / q] \end{array}$$

**Pushouts** The quotient type is actually a deceptively simple example of a parameterized higher inductive type, at least as far as coercion is concerned. It has the special property that the naive definition of coercion for the path constructor—coerce each argument and repackage—produces coherent results. This is not the case in general, as demonstrated by our next example: the *pushout* [Uni13, §6.8].

The pushout of a pair of maps $F \in C \rightarrow A$ and $G \in C \rightarrow B$ is the coproduct of $A$ and $B$ “modulo $C$”: it has an element $\operatorname{inl}(a)$ for every $a: A$ and an element $\operatorname{inr}(b)$ for every $b: B$, but also identifies $\operatorname{inl}(Fc)$ with $\operatorname{inr}(Gc)$ for every $c: C$.

$$\begin{array}{l} A, B, C: \cup, f: C \rightarrow A, g: C \rightarrow B \gg \textbf{inductive Push}(A, B, C, f, g) \textbf{ where} \\ | \operatorname{inl}(a: A) \in \operatorname{Push}(A, B, C, f, g) \\ | \operatorname{inr}(b: B) \in \operatorname{Push}(A, B, C, f, g) \\ | \operatorname{push}(c: C, x: \mathbb{I}) \in \operatorname{Push}(A, B, C, f, g) \quad[x \equiv 0 \hookrightarrow \operatorname{inl}(fc) \mid x \equiv 1 \hookrightarrow \operatorname{inr}(gc)] \end{array}$$

The notable feature of this definition, in comparison to what we have seen before, is that the boundary of the path constructor push depends on the parameters $f, g$ to the type. (Strictly speaking, push should be annotated with $f$ and $g$ so that these are available for the boundary reductions in the operational semantics, but we will suppress such annotations here for readability.)

As with the quotient, we can define composition in $\operatorname{Push}(A, B, C, F, G)$ using formal composites, and we can define coercion on the point constructors by moving the coercion inside the constructor.

$$\overline{\operatorname{coe}_{x, \operatorname{Push}(A, B, C, F, G)}^{r \rightarrow s}(\operatorname{inl}(M)) \longmapsto \operatorname{inl}(\operatorname{coe}_{x, A}^{r \rightarrow s}(M))}$$
$$\overline{\operatorname{coe}_{x, \operatorname{Push}(A, B, C, F, G)}^{r \rightarrow s}(\operatorname{inr}(N)) \longmapsto \operatorname{inr}(\operatorname{coe}_{x, B}^{r \rightarrow s}(N))}$$

It is tempting to do the same for the path constructor.

$$\overline{\operatorname{coe}_{x, \operatorname{Push}(A, B, C, F, G)}^{r \rightarrow s}(\operatorname{push}(P, y)) \longmapsto \operatorname{push}(\operatorname{coe}_{x, C}^{r \rightarrow s}(P), y)} \times$$

Looking closely at this definition, however, we notice that it fails to be coherent. If we instantiate $y$ with 0, the left side will reduce to $\operatorname{coe}_{x, \operatorname{Push}(A, B, C, F, G)}^{r \rightarrow s}(\operatorname{inl}(F[r / x] P))$,