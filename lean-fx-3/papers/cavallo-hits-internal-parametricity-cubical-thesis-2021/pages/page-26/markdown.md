14

Introduction

Church's $\lambda$-calculus; we uniformly write variable bindings either in the form "a." or with a type annotation as "a : A".)

Conversely, if we have an element of a function type $F \in (a : A) \to B$, we can apply it to any element $M \in A$ to obtain an element of $B[M/a]$ (the result of substituting the term $M$ for the variable $a$ in $B$).

$$\frac{F \in (a : A) \to B \qquad M \in A}{F M \in B[M/a]}$$

We may therefore say that the function type $(a : A) \to B$ is an internalization of the external concept of hypothetical judgment. Indeed, it is a unifying design principle of type theories that each type former internalizes some judgmental concept. In the case of paths, the path type $\text{Path}(A, M_0, M_1)$ serves to internalize the hypothetical judgment $x : \mathbb{I} \gg - \in A$ (together with conditions on the endpoints).

The name cubical type theory comes from the intuitive reading of judgments such as $x_1 : \mathbb{I}, \ldots, x_n : \mathbb{I} \gg M \in A$ that depend on multiple interval variables. Where the term $M$ in $x : \mathbb{I} \gg M \in A$ is a path or line in the type $A$, a term $x_1 : \mathbb{I}, \ldots, x_n : \mathbb{I} \gg M \in A$ is an $n$-dimensional (hyper)cube in $A$, filled in as each of the variables ranges between 0 and 1.

Coercion The utility of paths—the ability to transport results across them—is delivered by an operation called coercion. The effect of coercion is expressed by the following rule.

$$\frac{x : \mathbb{I} \gg A \text{ type} \qquad r \in \mathbb{I} \qquad s \in \mathbb{I} \qquad M \in A[r/x]}{\text{coe}_{x.A}^{r \to s}(M) \in A[s/x]}$$

In words, if we have a line of types $x : \mathbb{I} \gg A$ type and an inhabitant $M \in A[r/x]$ of some type along that line, then we may coerce it to obtain an element of any other type $A[s/x]$ along the line.

Transport along paths within types arises as a corollary of coercion. Suppose we have a family of types $a : A \gg B$ type depending on a variable of type $A$, a path $x : \mathbb{I} \gg P \in A$ in the indexing type, and an inhabitant $N \in B[P[0/x]/a]$, which we can read as a proof that the property $B$ holds of the term $P[0/x]$. Then we can obtain a term of type $B[P[1/x]/a]$ using coercion as follows.

$$\text{transport}_{a.B}^{0 \to 1}(x.P, N) := \text{coe}_{x.B[P/a]}^{0 \to 1}(N) \in B[P[1/x]/a]$$

Thus, any "property" $B$ that is satisfied by a term $M \in A$ is also satisfied by any term connected to $M$ by a path.

Specifying the computational behavior of $\text{coe}_{x.A}^{r \to s}(M)$ for each possible type line $x.A$ is the main technical challenge of designing a cubical type theory. (To do so requires an additional concept, path composition, that we will introduce later on.) Reflecting the contentful nature of path equality, this behavior does depend in general on the entirety of the line $x.A$, not only on the source and destination points $A[r/x]$ and $A[s/x]$.