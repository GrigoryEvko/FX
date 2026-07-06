196

Programming with parametricity

To do so, we will need a term $f_x \in A \to \text{Gel}_x(A, B, R)$ to supply as the function argument. It is here that we use bridge-discreteness of $A$, which gives us some function $t \in (a_0, a_1 : A) \to \text{Bridge}(A, a_0, a_1) \to \text{Path}(A, a_0, a_1)$. Using $t$, we can define $f_x$ by way of extent.

$$f_x := \lambda a. \text{extent}_x(a; a_0. a_0, a_1. f a_1, a_0. a_1. q. \lambda^1 x. \text{gel}_x(a_0, f a_1, \lambda^1 y. f (t a_0 a_1 q y)))$$

We have $f_0 = \lambda a. a \in A \to A$ and $f_1 = f \in A \to B$. In words, to construct $f_x$, we need to know that any $a_0, a_1 : A$ related by $\text{Bridge}(A, -, -)$ satisfy $f a_0 \rightsquigarrow f a_1$. This is only guaranteed if bridges in the constant $A$ give rise to paths in the same; thus the necessity of bridge-discreteness.

The remainder of the argument proceeds as in Theorem 10.1.2. By applying $c$ at $f_x$, we obtain an element of $\text{Gel}_x(A, B, R)$, which we can ungel to get the witness to $R$ we require.

$$\text{ungel}(x. c (\text{Gel}_x(A, B, R)) f_x) \in \text{Path}(B, f (c A (\lambda a. a)), c B f) \quad \square$$

Now we take a look at types formed from bridge-discrete arguments. When we have a bridge-discrete family of types, we have the following result, which will help analyze dependent function and product types.

Lemma 10.3.5. Let $A$ type and $a : A \gg B$ type. Suppose that $B$ is bridge-discrete for every $a : A$. Then for any path $a_0, a_1 : A$, $p : \text{Path}(A, a_0, a_1)$, and $b_0 : B[a_0/a]$ and $b_1 : B[a_1/a]$, we have the following isomorphism.

$$\text{Path}(x. B[p x/a], b_0, b_1) \simeq \text{Bridge}(x. B[\text{loosen}_A p x/a], b_0, b_1)$$

Proof. By Lemma 3.2.3, it suffices to show this when $a_0 = a_1$ and $p$ is the degenerate path $\lambda_{-} a_0$. In that case, we have $\text{loosen}_A (\lambda^1_{-} a_0) \rightsquigarrow (\lambda^1_{-} a_0)$, and so the isomorphism we must construct follows directly from bridge-discreteness of $B[a_0/a]$. $\square$

Theorem 10.3.6. The universe of bridge-discrete types is closed under product, function, path, and bridge types.

Proof. For product types, $(a : A) \times B$, this follows from Lemmas 3.2.4 and 9.2.2, using Lemma 10.3.5 to get a correspondence between dependent bridges and paths in $B$ over the correspondence in $A$. For functions, it follows from Lemma 3.2.6 and Theorem 9.3.2. For paths and bridges, it follows from Lemma 9.2.3. $\square$

We may also show that inductive types preserve bridge-discreteness. Here, we show as an example that Bool is bridge-discrete. The argument is more involved than for the preceding types, employing in particular relativity (that is, Gel types). This presents an interesting parallel to the use of univalence to characterize the path types of higher inductive types, sketched in our discussion of descent in Chapter 4.