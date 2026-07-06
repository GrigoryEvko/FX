102

Case studies

which in turn reduces to $\text{inl}(\text{coe}_{x,A}^{r\to s}(F[r/x]P))$ by our rules for coercion of point constructors. If, on the other hand, we instantiate $y$ with 0 on the *right* side, we instead obtain $\text{inl}(F[s/x](\text{coe}_{x,C}^{r\to s}(P)))$. That is, depending on our ordering of reduction and interval substitution, we apply $F$ and coercion in different orders. Nothing guarantees that $\text{coe}_{x,A}^{r\to s}(F[r/x]P)$ and $F[s/x](\text{coe}_{x,C}^{r\to s}(P))$ will be equal as elements of $A[s/x]$, and so this reduction rule fails to give us a well-typed coercion operator.$^2$

Fortunately, although we have a mismatch up to *exact* equality, these two terms *are* the same up to path equality, which means we will be able to correct the definition using composition. Consider the following term varying in $x:\mathbb{I}$.

$$x:\mathbb{I}\gg\text{coe}_{x,A}^{x\to s}(F(\text{coe}_{x,C}^{r\to x}(P)))\in A$$

When we instantiate $x$ with $r$, the inner coercion vanishes, and so the term simplifies to $\text{coe}_{x,A}^{r\to s}(F[r/x]P)$. Conversely, when we instantiate $x$ with $s$, the outer coercion disappears and we are left with $F[s/x](\text{coe}_{x,C}^{r\to s}(P))$. We can use this adjustment path, together with the corresponding path for $G$, as the tube of a formal composition that “fixes” the boundary of our naive definition.

$$\begin{array}{c}\hline \text{coe}_{x:\text{Push}(A,B,C,F,G)}^{r\to s}(\text{push}(P,y))\\ \longmapsto\\ \text{fhcom}^{s\to r}\left(\text{push}(\text{coe}_{x,C}^{r\to s}(P),y);\quad y\equiv 0\hookrightarrow x.\text{inl}(\text{coe}_{x,A}^{x\to s}(F(\text{coe}_{x,C}^{r\to x}(P))))\right)\\ y\equiv 1\hookrightarrow x.\text{inr}(\text{coe}_{x,B}^{x\to s}(G(\text{coe}_{x,C}^{r\to x}(P))))\end{array}$$

This rectified definition satisfies the coherence conditions we require, and still simplifies to $\text{push}(P,y)$ when $r=s$. This shape of coercion implementation—with coherence ensured by formal composition—will suffice for all *non-indexed* higher inductive types. For indexed higher inductive types (indeed, for indexed inductive types more generally), another adjustment will be necessary, as we will see in Section 5.3.

## 5.2 Truncations

For our next class of examples, we examine the role of recursive constructors by considering the propositional truncation and more generally the *higher truncations*. These

$^2$Indeed, in order for this condition to hold in general, we would need exact uniqueness of identity proofs in $A$. Consider the case where $F$ is a constant function $\lambda_{\infty}M$ for some $M\in A$. The coherence condition then requires that $\text{coe}_{x,A}^{r\to s}(M[r/x])$ is exactly $M[s/x]$ for all $r,s$, which implies in particular that $y:\mathbb{I}\gg M[y/x]=\text{coe}_{x,A}^{0\to y}(M[0/x])\in A[y/x]$. Were this true for all $M$, any path $Q\in\text{Path}(x,A,M_0,M_1)$ would be equal to the path $\lambda y.\text{coe}_{x,A}^{0\to y}(M_0)$.