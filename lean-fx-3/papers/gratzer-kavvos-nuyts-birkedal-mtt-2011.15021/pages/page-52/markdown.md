11:52

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

**Theorem 9.9.** If $f$ is commutative then $\text{zipWith}(f)$ is commutative. That is, given $A, B : \mathsf{U}$ and $f : \mathsf{El}(A) \to \mathsf{El}(A) \to \mathsf{El}(B)$ there is a term of the following type:

$$
\begin{array}{l}
((x, y : \mathsf{El}(A)) \to \mathsf{Eq}_{\mathsf{El}(B)}(f(x, y), f(y, x))) \to \\
(s, t : \mathsf{El}(\mathsf{Str}(A))) \to \mathsf{Eq}_{\mathsf{El}(\mathsf{Str}(B))}(\text{zipWith}(f, s, t), \text{zipWith}(f, t, s))
\end{array}
$$

*Proof.* Suppose $e : (x, y : \mathsf{El}(A)) \to \mathsf{Eq}_{\mathsf{El}(B)}(f(x, y), f(y, x))$ and $s, t : \mathsf{El}(\mathsf{Str}(A))$. We wish to show that $\text{zipWith}(f, s, t) = \text{zipWith}(f, t, s)$. By the definition of $\text{zipWith}$, it is sufficient to prove that for any $u, v : \mathsf{El}(\mathsf{Str}'(A))$ we have

$$
\text{zipWith}'(\text{mod}_\delta(f), u, v) = \text{zipWith}'(\text{mod}_\delta(f), v, u)
$$

In turn, it suffices to show that

$$
\text{löb}(F_0) = \text{löb}(F_1)
$$

where

$$
\begin{array}{l}
F_0 \triangleq \lambda r. \lambda x, y. (\text{mod}_\delta(f) \circledast_\delta \text{pr}_0(x) \circledast_\delta \text{pr}_0(y), r \circledast_\ell \text{pr}_1(x) \circledast_\ell \text{pr}_1(y)) \\
F_1 \triangleq \lambda r. \lambda x, y. (\text{mod}_\delta(f) \circledast_\delta \text{pr}_0(y) \circledast_\delta \text{pr}_0(x), r \circledast_\ell \text{pr}_1(y) \circledast_\ell \text{pr}_1(x))
\end{array}
$$

because then

$$
\text{zipWith}'(\text{mod}_\delta(f), v, u) \triangleq \text{löb}(F_0)(u, v) = \text{löb}(F_1)(u, v) = \text{zipWith}'(\text{mod}_\delta(f), u, v)
$$

By Theorem 9.5 we know guarded fixed points are unique, so it suffices to show that

$$
\text{löb}(F_1) = F_0(\text{next}(\text{löb}(F_1))) \tag{9.5}
$$

We use Löb induction to construct a term of type $\mathsf{Eq}(\text{löb}(F_1), F_0(\text{next}(\text{löb}(F_1))))$.

$$
\begin{array}{l}
F_0(\text{next}(\text{löb}(F_1))) \\
= \lambda x, y. (\text{mod}_\delta(f) \circledast_\delta \text{pr}_0(x) \circledast_\delta \text{pr}_0(y), \text{next}(\text{löb}(F_1)) \circledast_\ell \text{pr}_1(x) \circledast_\ell \text{pr}_1(y)) \\
\quad \text{by induction let } \text{mod}_\delta(a) \triangleq \text{pr}_0(x) \text{ and } \text{mod}_\delta(b) \triangleq \text{pr}_0(y) \\
= \lambda x, y. (\text{mod}_\delta(f(a, b)), \text{next}(\text{löb}(F_1)) \circledast_\ell \text{pr}_1(x) \circledast_\ell \text{pr}_1(y)) \\
= \lambda x, y. (\text{mod}_\delta(f(b, a)), \text{next}(\text{löb}(F_1)) \circledast_\ell \text{pr}_1(x) \circledast_\ell \text{pr}_1(y)) \\
= \lambda x, y. (\text{mod}_\delta(f(b, a)), \text{next}(F_1(\text{next}(\text{löb}(F_1)))) \circledast_\ell \text{pr}_1(x) \circledast_\ell \text{pr}_1(y)) \\
\quad \text{by induction let } \text{mod}_\ell(s) \triangleq \text{pr}_1(x) \text{ and } \text{mod}_\ell(t) \triangleq \text{pr}_1(y) \\
= \lambda x, y. (\text{mod}_\delta(f(b, a)), \text{next}(F_1(\text{next}(\text{löb}(F_1))(s, t))) \\
= \lambda x, y. (\text{mod}_\delta(f(b, a)), \text{next}(F_0(\text{next}(\text{löb}(F_1))(t, s))) \\
= \lambda x, y. (\text{mod}_\delta(f(b, a)), \text{next}(F_0(\text{next}(\text{löb}(F_1)))) \circledast_\ell \text{pr}_1(y) \circledast_\ell \text{pr}_1(x)) \\
\quad \text{using the IH through Lemma 9.4} \\
= \lambda x, y. (\text{mod}_\delta(f(b, a)), \text{next}(\text{löb}(F_1)) \circledast_\ell \text{pr}_1(y) \circledast_\ell \text{pr}_1(x)) \\
= \lambda x, y. (\text{mod}_\delta(f) \circledast_\delta \text{pr}_0(y) \circledast_\delta \text{pr}_0(x), \text{next}(\text{löb}(F_1)) \circledast_\ell \text{pr}_1(y) \circledast_\ell \text{pr}_1(x)) \\
= \text{löb}(F_1)
\end{array}
$$

**Remark 9.10** (Previous approaches). Using dependent type theories to reason about guarded recursion and coinductive types has been a problem for some time [Møg14]. The technical device of *clocks*, due to [AM13], was introduced to deal with productivity in a simply-typed setting. Clocks were then introduced to dependent types [Møg14], and later refined into the extensional guarded type theory **gDTT** of [BGC$^+$16].