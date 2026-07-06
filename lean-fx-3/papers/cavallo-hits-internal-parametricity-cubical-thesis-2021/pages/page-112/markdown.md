100 Case studies

repackage.

$$\begin{array}{c} \hline \text{coe}_{x.A \parallel R}^{r \rightarrow s}(\text{rel}(N, N', P, y)) \\ \longmapsto \\ \text{rel}(\text{coe}_{x.A}^{r \rightarrow s}(N), \text{coe}_{x.A}^{r \rightarrow s}(N'), \text{coe}_{x.R(\text{coe}_{x.A}^{r \rightarrow y}(N), \text{coe}_{x.A}^{r \rightarrow y}(N'))}^{r \rightarrow s}(P), y) \end{array}$$

While the above looks a bit more complicated thanks to the dependency of the type of $P$ on $N$ and $N'$, the essential idea is the same. As required, the reduction is coherent: if, for example, we reduce and then instantiate $y$ with 0, the result steps to $\text{pt}(\text{coe}_{x.A}^{r \rightarrow s}(N))$, which is the same as the result we would arrive at by instantiating $y$ with 0 and then reducing.

Finally, we must consider coercion on a formal composite. In this case, the idea is the same as with the eliminator. A coercion applied to a formal composite becomes a composite of coercions in the target type—which is to say, another formal composite.

$$\text{coe}_{x.A \parallel R}^{r \rightarrow s}(\text{fhcom}^{t \rightarrow u}(M; \overline{\xi_i \hookrightarrow y.N_i})) \longmapsto \text{fhcom}^{t \rightarrow u}(\text{coe}_{x.A \parallel R}^{r \rightarrow s}(M); \overline{\xi_i \hookrightarrow y.\text{coe}_{x.A \parallel R}^{r \rightarrow s}(N_i)})$$

Again, it is easy to see that this is a coherent definition, and it completes our specification of coercion in the quotient type.

Note that we do not have the option of defining coercion in the quotient type by simply introducing formal coercions, as we did with composition—at least, not without imposing severe restrictions on the parameters. The problem is that, unlike composition, coercion moves between different instantiations of the parameters of a type. If we introduced formal coercion values, the values of a given $A \parallel R$ would depend on the values of $A' \parallel R'$ for every $A', R'$ connected by paths to $A, R$; as such, we would have to define the semantics of the quotient type for every possible parameter instantiation simultaneously. This dependency on the complete parameter space precludes including $A \parallel R$ in the same universe as its type parameters; given $A \in \text{U}_n$ and $R \in A \times A \rightarrow \text{U}_n$, we would not have $A \parallel R \in \text{U}_n$ but only $A \parallel R \in \text{U}_{n+1}$. This issue was encountered by Lumsdaine and Shulman in their semantics of higher inductive types in simplicial model categories, where it manifests as the failure of a fibrant replacement operation to preserve size. It is thus an important feature of the cubical setting that the Kan operations can be divided into homogeneous composition, which can be added formally in HITs, and coercion, which is definable in HITs. In the simplicial setting, there is instead only an operation analogous to com which is not known to decompose in such a way.¹

Elimination, meanwhile, is not complicated by the addition of parameters; we may state the elimination principle and define its computational behavior in the same way as

¹Shulman has recently proposed an alternative (yet unpublished) technique for realizing higher inductive types in the simplicial case.