Realizing contentful equality 13

First, an exact equality $M = N \in A$ is not a type but a judgment, a statement of the same kind as the elementhood judgment $M \in A$. Judgments are not themselves types, so we cannot speak about the exact equality judgment inside our type theory. That is, the following is not a well-formed type.

$$(n : \text{Int}) \rightarrow ((m : \text{Int}) \times (m + n = 0 \in \text{Int})) \quad \times$$

In contrast, the path type *is* of course a type. We say that exact equality is an *external* equality, while the path type is an *internal* equality.

Second, $M = N \in A$ is a *substitutional* equality. This means that, given any judgment depending on an element of $A$, we can silently replace $M$ with $N$ anywhere we like without affecting the validity of the judgment. For example, if $P \in \text{Path}(A, O, M)$, then it is also the case that $P \in \text{Path}(A, O, N)$. In contrast, paths are merely *transportational*: if we have $Q \in \text{Path}(A, M, N)$ and $P \in \text{Path}(A, O, M)$, then it is not necessarily the case that $P \in \text{Path}(A, O, N)$. Instead, there is an *operation*, “transport”, which we can apply with $Q$ to obtain a new term $P' \in \text{Path}(A, O, N)$. In particular, the result $P'$ can vary depending on the form of $Q$.

The substitutional/transportational distinction is correlated with, if not identical to, our previous contentless/contentful distinction: we think of the former as a description of the available logical principles, while the latter is a description of a computational interpretation. The external/internal and substitutional/transportational axes, on the other hand, are independent. For example, the identity type in Martin-Löf’s extensional type theory is internal and substitutional.

Conversely, cubical type theory’s path type is merely the internalization of an external transportational notion of path. To understand this, we need to delve a bit deeper into the details of type theory by introducing the idea of a *hypothetical judgment*. A hypothetical judgment is one that depends on some collection of typed variables (the *hypotheses*). For example, the judgment $a : A \gg M \in B$ asserts that the term $M$ has type $B$ under the assumption that the variable $a$ has type $A$. Both $M$ and $B$ may make use of the variable $a$. As a concrete example, the judgment $m : \text{Int}, n : \text{Int} \gg m + n \in \text{Int}$ asserts that $m + n$ is an integer whenever $m$ and $n$ are integers.

Using the hypothetical judgment, we can state the following rule for constructing elements of the function type $(a : A) \rightarrow B$.

$$\frac{a : A \gg N \in B}{\lambda a \cdot N \in (a : A) \rightarrow B}$$

In words, if $N$ is an element of $B$ under the assumption that $a$ has type $A$, then the function that takes in an element $a$ of $A$ and returns $N$—here written $\lambda a \cdot N$—is a function of type $(a : A) \rightarrow B$. (The prefix $\lambda$ for the function constructor is traditional, dating back to