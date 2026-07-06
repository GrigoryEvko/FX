Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:11

COERCION

$$\begin{array}{l} \Gamma , x: \mathbb {I} \gg A \text {type} \quad \Gamma \gg r, s \in \mathbb {I} \quad \Gamma \gg M \in A [ r / x ] \\ \hline \Gamma \gg \operatorname {c o e} _ {x. A} ^ {r \rightsquigarrow s} (M) \in A [ s / x ] \\ \Gamma \gg \operatorname {c o e} _ {x. A} ^ {r \rightsquigarrow r} (M) = M \in A [ r / x ] \end{array}$$

HOMOGENEOUS COMPOSITION

$$\Gamma \gg A \text {type} \quad \Gamma \gg r, s \in \mathbb {I} \quad \Gamma \gg M \in A$$

$$(\forall i) \Gamma \gg \xi_ {i} \text {constraint} \quad (\forall i) \Gamma , \xi_ {i}, x: \mathbb {I} \gg N _ {i} \in A$$

$$(\forall i) \Gamma , \xi_ {i} \gg M = N _ {i} [ r / x ] \in A \quad (\forall i, j) \Gamma , \xi_ {i}, \xi_ {j}, x: \mathbb {I} \gg N _ {i} = N _ {j} \in A$$

$$\Gamma \gg \mathsf {h c o m} _ {A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) \in A$$

$$(\forall j) \Gamma , \xi_ {j} \gg \mathsf {h c o m} _ {A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = N _ {j} [ s / x ] \in A$$

$$\Gamma \gg \mathsf {h c o m} _ {A} ^ {r \rightsquigarrow r} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = M \in A$$

HETEROGENEOUS COMPOSITION

$$\Gamma , x: \mathbb {I} \gg A \text {type} \quad \Gamma \gg r, s \in \mathbb {I} \quad \Gamma \gg M \in A [ r / x ]$$

$$(\forall i) \Gamma \gg \xi_ {i} \text {constraint} \quad (\forall i) \Gamma , \xi_ {i}, x: \mathbb {I} \gg N _ {i} \in A$$

$$(\forall i) \Gamma , \xi_ {i} \gg M = N _ {i} [ r / x ] \in A [ r / x ] \quad (\forall i, j) \Gamma , \xi_ {i}, \xi_ {j}, x: \mathbb {I} \gg N _ {i} = N _ {j} \in A$$

$$\Gamma \gg \mathsf {c o m} _ {x. A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) \in A [ s / x ]$$

$$(\forall j) \Gamma , \xi_ {j} \gg \mathsf {c o m} _ {x. A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = N _ {j} [ s / x ] \in A [ s / x ]$$

$$\Gamma \gg \mathsf {c o m} _ {x. A} ^ {r \rightsquigarrow r} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = M \in A [ r / x ]$$

Figure 2: Rules for coercion, homogeneous composition, and heterogeneous composition

Constructing an inverse to this function will require the coercion operator introduced in the following section.

1.3. Kan operations: coercion and composition. The judgmental path structure of cubical type theory endows each type with a "path" relation. So far, this relation is not quite a proper notion of equality. For one, while it is reflexive, it need not be symmetric or transitive. Perhaps more importantly, we do not know that type families respect paths in the following sense. If we have some family $a: A \gg B$ type and a path $P \in \mathsf{Path}_A(M_0, M_1)$, we expect that for every element of $BM_0$, there is a corresponding element of $BM_1$. If we think of $B$ as a predicate on elements of $A$, we are saying that $M_1$ should satisfy the same properties as $M_0$. In fact, we would expect that $BM_0$ and $BM_1$ are isomorphic. At the moment, however, we only know that there is a path $x.B(P@x)$ from $BM_0$ to $BM_1$. What we need, then, is one direction of the univalence axiom: the ability to transform paths between types into isomorphisms. This is effected by the coercion operator coe, which satisfies the first rule in Figure 2.

Given a term at some index $r$ of a type path $x.A$, coercion produces an element at any other $s$. We can show that $\mathsf{coe}_{x.A}^{r\rightsquigarrow s}(-\in A[r/x]\to A[s/x])$ is in fact an isomorphism. The full proof relies on composition, which we have not yet introduced, but we can at least see