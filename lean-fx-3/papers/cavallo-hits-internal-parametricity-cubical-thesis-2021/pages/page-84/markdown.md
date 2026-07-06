72*Cubical type theory*

We give our proofs in a style reminiscent of the **HoTT** Book [Uni13]: a combination of textual argument and explicit syntax. Textual statements should be understood as syntactic sugar for type expressions: when we say “for all $a:A$, there exists $b:B$ such that…”, we mean that the type $(a:A) \rightarrow (b:B) \times \cdots$ is inhabited, not some metatheoretic property. Also, we will use the notation $M_0 \rightsquigarrow M_1$ an informal shorthand for the path type $\text{Path}(A, M_0, M_1)$.

### 3.2.1 Path induction

We have seen that, via coercion, we can transport properties between path-equal terms. We now show that transport further induces an *a priori* stronger principle: a version of the J eliminator that defines identity types (Section 2.1.5.4). We obtain this result as a corollary of *singleton contractibility*.

**Definition 3.2.1.** *A* type is a *proposition* if there is a path between any pair of elements in $A$, that is, if the following type is inhabited.

$$\text{IsProp}(A) := (a_0, a_1 : A) \rightarrow \text{Path}(A, a_0, a_1)$$

We define the *universe of propositions* as $U := (A : U) \times \text{IsProp}(A)$. $A$ is *contractible* when it is an inhabited proposition.

$$\text{IsContr}(A) := A \times \text{IsProp}(A)$$

Equivalently, a type is contractible when it contains an element to which all its other elements are equal up to a path. Singleton contractibility says that *singleton type* $(a:A) \times \text{Path}(A, a_0, a)$ of terms path-equal to some fixed point $a_0 : A$ is always contractible, the canonical inhabitant being $\langle a_0, \lambda^\mathbb{I} \dots a_0 \rangle$. Given any other element $\langle b, p \rangle$, we have evidence $p$ that the first component $b$ is path-equal to $a_0$, and we can moreover show that $\lambda^\mathbb{I} \dots a_0$ and $p$ correspond over this path.

**Lemma 3.2.2 (Singleton contractibility).** For any $A$ type and $a_0 : A$, the singleton type $(a:A) \times \text{Path}(A, a_0, a)$ is contractible.

*Proof.* The singleton type is inhabited, as $a_0$ is equal to itself by the reflexive path: we have $\langle a_0, \lambda^\mathbb{I} \dots a_0 \rangle : (a:A) \times \text{Path}(A, a_0, a)$. To see that the singleton type is a proposition, suppose we are given $\langle b, p \rangle$, $\langle b, p' \rangle : (a:A) \times \text{Path}(A, a_0, a)$. To construct a path between these in the type $(a:A) \times \text{Path}(A, a_0, a)$, we need a pair of terms $x : \mathbb{I} \gg T_x \in A$ and $x : \mathbb{I} \gg Q_x \in \text{Path}(A, a_0, T_x)$ that reduce to $\langle b, p \rangle$ when $x = 0$ and $\langle b', p' \rangle$ when $x = 1$. We might look to define $\lambda^\mathbb{I} x \cdot T_x$ as the concatenation of $p^{-1} : b \rightsquigarrow a_0$ with $p : a_0 \rightsquigarrow b'$, but we will actually