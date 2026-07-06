Church booleans 267

- For any $a : A$, we have $\text{undisc}(\text{mod}(a)) = a \in A$.
- For any $(\text{dsc} \mid d : \text{Disc}(A))$, we have a path as follows.

$$\text{undisc-uniq}(d) \in \text{Glo}(\text{Path}(\text{Disc}(A), \text{mod}(\text{undisc}(d)), d))$$

*Proof.* Set $\text{undisc}(d) := \text{letdisc}_{\text{pt}}(\dots A, d, a.a)$. The first property follows from the reduction rule for the pointwise eliminator. For the second, we construct the path by pointwise elimination into $B := \text{Glo}(\text{Path}(\text{Disc}(A), \text{mod}(\text{undisc}(d)), d))$.

$$\text{undisc-uniq}(d) := \text{letdisc}_{\text{pt}}(d.B, d, a.\text{mod}(\lambda^1 \dots \text{mod}(a))) \quad \square$$

From this point forward, we will use the following syntactic sugar for the discrete eliminator, mimicking our higher inductive type pseudocode.

$$\left[ \begin{array}{c} \text{case } P \text{ of} \\ | \text{mod}(a) \mapsto N \end{array} \right] := \text{letdisc}(d.B, P, a.N)$$

The type argument $B$ is implicit here, but should be straightforward for the reader to infer in concrete cases. Again as with HITs, we will also collapse iterated case analyses into a single block branching on two or more terms, as in the following definition.

**Proposition 15.1.3 (Action of the discrete embedding).** For any $(\text{cc} \mid A, B : U)$, we have a term $\text{map-disc} \in \text{Disc}(A \to B) \to \text{Disc}(A) \to \text{Disc}(B) \text{ @ par}$ defined as follows.

$$\text{map-disc} := \lambda f. \lambda d. \left[ \begin{array}{c} \text{case } f, d \text{ of} \\ | \text{mod}(g), \text{mod}(a) \mapsto \text{mod}(f a) \end{array} \right]$$

De-sugared, this is $\lambda f. \lambda d. \text{letdisc}(\dots \text{Disc}(B), f, g.\text{letdisc}(\dots \text{Disc}(B), d, a.\text{mod}(f a))$.

## 15.2 Church booleans

To demonstrate how we can apply parametricity results in the pointwise fragment, let us revisit the Church boolean example presented in Section 10.1.

$$\mathbb{B} := (A : U) \to A \to A \to A$$

Built from a universe and function types, the type of Church booleans exists in both the pointwise and parametric modes: we have both $\mathbb{B}$ type @ par and $\mathbb{B}$ type @ pt. Note that while these types are syntactically identical, they are interpreted as different relations: the elements of $\mathbb{B}$ in the parametric mode must have an action on bridges, while the elements of $\mathbb{B}$ in the pointwise mode need only act on paths. (Indeed, it is merely a