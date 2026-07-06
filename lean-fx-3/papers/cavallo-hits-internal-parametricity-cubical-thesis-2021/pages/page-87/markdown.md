Programming in a cubical type theory 75

that $A$ depends on $x$: a path between functions is a function from paths in the domain to paths in the codomain. The proof of this result is rather more involved and in particular makes use of coercion.

**Lemma 3.2.6 (Paths in function types).** Let $x : \mathbb{I} \gg A$ type and $x : \mathbb{I}, a : A \gg B$ type be given together with $f_0 : ((a : A) \rightarrow B)[0/x]$ and $f_1 : ((a : A) \rightarrow B)[1/x]$. Then we have an isomorphism of the following type.

$$
\begin{aligned}
&\text{Path}(x.(a : A) \rightarrow B, f_0, f_1) \\
&\approx \\
&\left(a_0 : A[0/x]\right) \left(a_1 : A[1/x]\right) \left(p : \text{Path}(x.A, a_0, a_1)\right) \rightarrow \text{Path}(x.B[p \, x/a], f_0 \, a_0, f_1 \, a_1)
\end{aligned}
$$

That is, a path in a function type is a function from paths in the domain to paths in the codomain.

*Proof.* Given $q$ in the former type, we have $\lambda a_0. \lambda a_1. \lambda p. \lambda^\mathbb{I} x. (q \, x) \, (p \, x)$ in the latter.

Conversely, suppose we are given $h$ in the latter. Supposing $x : \mathbb{I}$ and $a : A$, we must construct an element of $B$ that becomes $f_0 \, a$ when $x = 0$ and $f_1 \, a$ when $x = 1$. Employing coercion, we can create a path $P_x$ along $A$ from the single element $a$.

$$
P_x := \lambda^\mathbb{I} y. \text{coe}_{x.A}^{x \rightarrow y}(a) \in \text{Path}(y.A[y/x], \text{coe}_{x.A}^{x \rightarrow 0}(a), \text{coe}_{x.A}^{x \rightarrow 1}(a))
$$

Note that we have $P_x \, x = a \in A$. By applying $h$ to this path, we obtain a corresponding path along $B$.

$$
h \left(P_x \, 0\right) \left(P_x \, 1\right) P_x \in \text{Path}(y.B[y/x, P_x \, y/a], f_0 \left(P_x \, 0\right), f_1 \left(P_x \, 1\right))
$$

Our solution is the evaluation of this path at $x$, the term $h \left(P_x \, 0\right) \left(P_x \, 1\right) P_x \, x \in B$, which has the right type thanks to the equation $P_x \, x = a \in A$. When $x$ is 0, it becomes $f_0 \left(P_0 \, 0\right)$, which is again $f_0 \, a$; when $x$ is 1, it is $f_1 \left(P_1 \, 1\right) = f_1 \, a$.

Now we must check that the two constructions above are mutually inverse. First, given $q : \text{Path}(x.(a : A) \rightarrow B, f_0, f_1)$, we need a path of the following type.

$$
(\lambda^\mathbb{I} x. \lambda a. q \, x \left( (\lambda^\mathbb{I} y. \text{coe}_{x.A}^{x \rightarrow y}(a)) \, x \right)) \rightsquigarrow q
$$

In fact, this equation holds up to exact equality, thanks to the reduction equation for trivial coercions.

For the other inverse condition, we see after a bit of computation that we must construct a path of the following type for $h$ in the right hand type.

$$
(\lambda a_0. \lambda a_1. \lambda p. \lambda^\mathbb{I} x. h \left( \text{coe}_{x.A}^{x \rightarrow 0}(p \, x) \right) \left( \text{coe}_{x.A}^{x \rightarrow 1}(p \, x) \right) (\lambda^\mathbb{I} y. \text{coe}_{x.A}^{x \rightarrow y}(p \, x)) \, x) \rightsquigarrow h
$$