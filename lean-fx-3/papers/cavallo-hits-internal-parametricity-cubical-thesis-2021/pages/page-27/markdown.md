Realizing contentful equality 15

**Univalence** With some clever programming, one may show that the coercion function $\lambda a.\operatorname{coe}_{x,A}^{0\to 1}(a) \in A[0/x] \to A[1/x]$ induced by a type path $x.A$ is in fact an isomorphism, with inverse given by the reverse coercion $\lambda a.\operatorname{coe}_{x,A}^{1\to 0}(a)$. That is, every $x:\mathbb{I} \gg A$ type induces an isomorphism between its endpoints, which we call $\operatorname{coe}_{x,A}^{0\to 1} \in A[0/x] \simeq A[1/x]$. In keeping with our conception of isomorphism as a kind of contentful equality, we might hope for the reverse: that every $A[0/x] \simeq A[1/x]$ induces a path from $A[0/x]$ to $A[1/x]$, with the property that coercing along said path applies the underlying function of the isomorphism. To have this correspondence would be a great boon: it would allow us to automatically transport theorems between isomorphic types, justifying formally that common informal mathematical practice.

Such a principle was first proposed by Voevodsky [Voe14] in the form of the *univalence axiom* for Martin-Löf's intensional type theory. To state the univalence axiom, we need to introduce two preliminaries: first, a more careful definition of isomorphism$^1$, and second, the concept of a *universe*.

**Definition 1.2.1 (Isomorphism).** Given a function $f \in A \to B$, a *left inverse* for $f$ is an element of the type $\operatorname{Linv}(A, B, f)$ defined as follows.

$$\operatorname{Linv}(A, B, f) := (g : B \to A) \times ((a : A) \to \operatorname{Path}(A, g(fa), a))$$

That is, a left inverse is a function $g \in B \to A$ such that $g(fa)$ is equal to $a$ for all $a \in A$. A *right inverse* for $f$ is an element of $\operatorname{Rinv}(A, B, f)$.

$$\operatorname{Rinv}(A, B, f) := (h : B \to A) \times ((b : B) \to \operatorname{Path}(B, f(hb), b))$$

A function is an isomorphism when it has both a left and right inverse.

$$\operatorname{IsIso}(A, B, f) := \operatorname{Linv}(A, B, f) \times \operatorname{Rinv}(A, B, f)$$

The type of isomorphisms between $A$ and $B$, written $A \simeq B$, is then defined as follows.

$$(A \simeq B) := (f : A \to B) \times \operatorname{IsIso}(A, B, f)$$

When $f$ is an isomorphism, we can prove its left and right inverse functions $g, h \in B \to A$ are equal up to a path. Nevertheless, requiring that they be the same *a priori* leads to an ill-behaved definition of isomorphism, interprovable with but not isomorphic to the one we present here. We will not get into the reasons here, but the reader can

$^1$I use *isomorphism* for what is more commonly called an *equivalence* in the homotopy type theory and cubical type theory community. I feel that isomorphism is the more suggestive term for a computer scientist's ears: "equivalence" suggests a contentless relation such as contextual equivalence or logical equivalence. Mathieu Anel has also suggested that isomorphism is a more appropriate term from an $\infty$-categorical perspective.