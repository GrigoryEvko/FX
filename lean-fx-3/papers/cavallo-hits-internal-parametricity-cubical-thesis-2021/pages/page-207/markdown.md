Bridge-discrete types

195

We define the universe of bridge-discrete types as $U_{\text{bdisc}} := (A : U) \times \text{IsBDisc}(A)$.

Remark 10.3.2. The map $\text{loosen}_A$ takes reflexive paths to reflexive bridges, up to a path: for any $a : A$, we have $\lambda^\mathbb{I}_y \cdot \text{coe}_{x \text{Bridge}(A, a, a)}^{y \to 1} (\lambda^\mathbb{I}_{-}, a) \in \text{loosen}_A (\lambda^\mathbb{I}_{-}, a) \rightsquigarrow (\lambda^\mathbb{I}_{-}, a)$.

By requiring $\text{loosen}_A$ in particular to be an isomorphism, we ensure that the type $\text{IsBDisc}(A)$ is a proposition (Definition 3.2.1), as the type $\text{IsIso}(A, B, f)$ is always a proposition [Uni13, Theorem 4.3.2]. To show that a type is bridge-discrete, however, it suffices to show that any map is an isomorphism (indeed, a retraction); this is a special case of a result stated in Section 3.2.

Lemma 10.3.3 (Bridge-discreteness by retract). Let $A$ type and suppose we have two functions as follows.

$$\begin{array}{l} f : (a_0, a_1 : A) \to \text{Bridge}(A, a_0, a_1) \to \text{Path}(A, a_0, a_1) \\ g : (a_0, a_1 : A) \to \text{Path}(A, a_0, a_1) \to \text{Bridge}(A, a_0, a_1) \end{array}$$

If $g \, a_0 \, a_1 \, (f \, a_0 \, a_1 \, q) \rightsquigarrow q$ for all $a_0, a_1 : A$ and $q : \text{Bridge}(A, a_0, a_1)$, then $A$ is bridge-discrete.

Proof. By Lemma 3.2.8.

Before we show that any types are bridge-discrete, the following demonstrates why this collection of types is worth identifying. Whenever we want to prove a parametricity result about a type that involves an "external" type parameter, we likely need to assume that parameter is bridge-discrete.

Theorem 10.3.4. For any bridge-discrete $A$ type, we have an isomorphism of the following type.

$$((B : U) \to (A \to B) \to B) \simeq A$$

Proof. Set $\mathbb{A} := ((B : U) \to (A \to B) \to B)$. We follow the pattern established in Theorem 10.1.2. The functions in either direction are simple to define.

$$\begin{array}{l} H := \lambda c. c A (\lambda a. a) \in \mathbb{A} \to A \\ K := \lambda a. \lambda A. \lambda f. f a \in A \to \mathbb{A} \end{array}$$

Moreover, calculation shows immediately that $H(Ka) = a \in A$ for any $a : A$. For the other inverse, we work by parametricity. We must show that for every $c : \mathbb{A}$, $B : U$, and $f : A \to B$, we have a path from $f(c A (\lambda a. a))$ to $c B f$. We define a relation from $A$ to $B$, the graph of $f$, by $R := \lambda \langle a, b \rangle. \text{Path}(B, f a, b)$. We aim to apply $c$ at the Gel type for $R$ in a fresh direction $x$.