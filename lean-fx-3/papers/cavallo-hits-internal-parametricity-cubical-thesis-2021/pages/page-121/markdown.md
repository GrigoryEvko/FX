Identity types 109

created by formal coercion are composable.

$$\frac{\overline{\mathrm{pcoe}}_{x.A \blacktriangleright \mathrm{Id}}^{r \rightarrow s}(\mathrm{refl}(M)) \longmapsto \mathrm{refl}(\mathrm{coe}_{x.A}^{r \rightarrow s}(M))}{\overline{\mathrm{pcoe}}_{x.A \blacktriangleright \mathrm{Id}}^{r \rightarrow s}(\mathrm{fcoe}_{y.(M_0,M_1)}^{t \rightarrow u}(P)) \longmapsto \mathrm{fcoe}_{y.(\mathrm{coe}_{x.A}^{r \rightarrow s}(M_0), \mathrm{coe}_{x.A}^{r \rightarrow s}(M_1))}^{t \rightarrow u}(\mathrm{pcoe}_{x.A \blacktriangleright \mathrm{Id}}^{r \rightarrow s}(P))}$$
$$\frac{\overline{\mathrm{pcoe}}_{x.A \blacktriangleright \mathrm{Id}}^{r \rightarrow s}(\mathrm{fhcom}^{t \rightarrow u}(M; \overline{\xi_i \hookrightarrow y.N_i}))}{\longmapsto \mathrm{fhcom}^{t \rightarrow u}(\mathrm{pcoe}_{x.A \blacktriangleright \mathrm{Id}}^{r \rightarrow s}(M); \overline{\xi_i \hookrightarrow y.\mathrm{pcoe}_{x.A \blacktriangleright \mathrm{Id}}^{r \rightarrow s}(N_i)})} \quad (P)$$

In the general case, the constructor case becomes slightly more complex in the same way that coercion in pushouts is more involved than in quotients: if the index of a constructor involves outside parameters, then an additional formal coercion is necessary in order to commute coercion past uses of those parameters. A simple example where this is needed is the *fiber family* $\mathrm{Fib}(A, B, f, -)$ of a function $f \in A \rightarrow B$, a family indexed by $B$ whose elements at index $b : B$ are the elements of $A$ mapped to $b$ by $f$.

$$A : \cup, B : \cup, f : A \rightarrow B \gg \textbf{inductive } \mathrm{Fib}(A, B, f, b : B) \textbf{ where}$$
$$| \mathrm{fib}(a : A) \in \mathrm{Fib}(A, B, f, f, a)$$

In this example, parameter coercion of the constructor along a line $x : \mathbb{I} \gg F \in A \rightarrow B$ can be defined as follows, with an fcoe applying the necessary adjustment.

$$\overline{\mathrm{pcoe}}_{x.(A,B,F) \blacktriangleright \mathrm{Fib}}^{r \rightarrow s}(\mathrm{fib}(M)) \longmapsto \mathrm{fcoe}_{x.\mathrm{coe}_{x.B}^{r \rightarrow s}(F(\mathrm{coe}_{x.A}^{r \rightarrow s}(M)))}^r(\mathrm{fib}(\mathrm{coe}_{x.A}^{r \rightarrow s}(M)))$$

To wrap up our definition of identity types, we still need to implement the eliminator. In addition to the refl constructor, we must handle the two formal Kan operator values. The same pattern used for composition in higher inductive types applies to both coercion and composition here: convert formal Kan operations in the domain into “real” Kan operations in the codomain, as shown for formal coercion below.

$$\frac{H^x := \mathrm{fcoe}_{x.(M'_0,M'_1)}^{r \rightarrow x}(P)}{\mathrm{elim}(a_0.a_1.p.B; M_0, M_1; \mathrm{fcoe}_{x.(M'_0,M'_1)}^{r \rightarrow s}(P); a.N)} \longmapsto \mathrm{coe}_{x.B[M'_0/a_0,M'_1/a_1,H^x/p]}^{r \rightarrow s}(\mathrm{elim}(a_0.a_1.p.B; M'_0[r/x], M'_1[r/x]; P; a.N))$$

If applied to the refl constructor, of course, the eliminator should simply apply the provided clause $a.N$, straightforwardly validating the reduction rule that cannot be achieved