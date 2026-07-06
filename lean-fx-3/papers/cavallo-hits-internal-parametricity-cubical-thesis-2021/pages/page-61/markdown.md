Cubical computational type theory 49

points (the *endpoints*) and a line between them. We name these two endpoints “0” and “1”.

$$\overline{0 \in \mathbb{I}} \qquad \overline{1 \in \mathbb{I}}$$

A path is then a type or term that depends on an interval variable: $x : \mathbb{I} \gg A$ type is a path of types, and $x : \mathbb{I} \gg M \in A$ is a path of terms. The endpoints of a path are recovered by substituting the constants 0 and 1: $x : \mathbb{I} \gg A$ type is a path from $A[0/x]$ type to $A[1/x]$ type. (Note that as far as substitution is concerned, interval variables behave exactly like ordinary term variables.)

The judgmental concept of path can then be straightforwardly internalized by *path types*: for each $x : \mathbb{I} \gg A$ type, and pair of endpoint terms $M_0 \in A[0/x]$ and $M_1 \in A[1/x]$, we introduce a type $\text{Path}(x.A, M_0, M_1)$ type whose values are abstracted terms $\lambda^1 x$. $M$ such that $x : \mathbb{I} \gg M \in A$, $M[0/x] = M_0 \in A[0/x]$, and $M[1/x] = M_1 \in A[1/x]$. This type will behave much like a function type, albeit one with constraints on its values at 0 and 1. In general, it is like a *dependent* function type: elements of $\text{Path}(x.A, M_0, M_1)$ are paths over the “path of types” $x : \mathbb{I} \gg A$ type.

**Notation 3.1.1.** When $A$ type does not depend on $x$, we abbreviate $\text{Path}(x.A, M_0, M_1)$ as $\text{Path}(A, M_0, M_1)$.

In a type theory with interval variables, each type comes equipped with a contentful relation: for any $M_0 \in A$ and $M_1 \in A$, the collection of paths $x : \mathbb{I} \gg M \in A$ such that $M[0/x] = M_0 \in A$ and $M[1/x] = M_1 \in A$ can be thought of as a collection of witnesses that $M_0$ and $M_1$ are related. Note that this relation is reflexive by way of constant functions: given any $M \in A$, we have $\lambda \dots M \in \text{Path}(A, M, M)$. In order for this contentful relation to be a notion of *equality*, however, more structure is required. For one, nothing here implies that the path relation is symmetric or transitive. More fundamentally, there is no way to *transport* along these paths, to transfer results about a given term to any path-equal term.

**Coercion and composition** The second essential component of cubical type theory is thus a pair of operations called the *Kan operations*, so called in reference to the Kan condition in classical homotopy theory [Kan55]. The first of these, coercion, implements the transport of terms along paths of types.

$$\frac{x : \mathbb{I} \gg A \text{ type} \quad r \in \mathbb{I} \quad s \in \mathbb{I} \quad M \in A[r/x]}{\text{coe}^r_{x.A}(M) \in A[s/x]}$$

That is, if $x : \mathbb{I} \gg A$ type is a path of types and we have an element of $A[r/x]$, then we can transform it into an element of $A[s/x]$ for any other $s$.