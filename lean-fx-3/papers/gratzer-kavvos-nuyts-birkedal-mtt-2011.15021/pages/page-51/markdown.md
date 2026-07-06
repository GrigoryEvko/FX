Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:51

Finally, we must show that \( f \) is the unique coalgebra morphism. Suppose we are given \( g: B \to \mathsf{El}(\mathsf{Str}(A)) \circledast s \) which also satisfies \( \mathsf{uncons}(g(x)) = (\mathsf{pr}_0(c(x)), g(\mathsf{pr}_1(c(x)))) \). We 'shift' this definition to timed sets, by defining

\[
\begin{array}{l} \hat {g} \quad : \Delta B \rightarrow \operatorname{El} (\operatorname{Str} ^ {\prime} (A)) @ t \\ \hat {g} (x) \triangleq \mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\mathsf {m o d} _ {\delta} (g) \circledast_ {\delta} x) \\ \end{array}
\]

It suffices to show that \(\hat{g} = f' \circledast t\), and we do so by Löb induction and function extensionality. Assume \(p: \blacktriangleright \mathsf{Eq}(\hat{g}, f')\), and \(x: \Delta B\). To prove \(\hat{g}(x) = f'(x): \Delta B \times \blacktriangleright \mathsf{Str}'(A)\) it suffices to show componentwise equality. By modal induction write \(x = \mathsf{mod}_{\delta}(y)\) for \(y: B\).

First, we have that \(\mathsf{pr}_0(f'(\mathsf{mod}_{\delta}(y))) = \mathsf{mod}_{\delta}(\mathsf{pr}_0(c(y)))\) by the definition of \(f'\). On the other hand, we have that

\[
\mathsf {p r} _ {0} (\hat {g} (\mathsf {m o d} _ {\delta} (y))) = \mathsf {p r} _ {0} (\mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\mathsf {m o d} _ {\delta} (g (y)))) = \mathsf {p r} _ {0} (g _ {x}): \Delta B @ t
\]

where we have used modal induction to write  \(  g(y) = \text{mod}_{\gamma}(g_x)  \) . That g is a coalgebra morphism implies that  \(  \text{head}(g(y)) = \text{pr}_0(c(y))  \) . If we now use modal induction to write  \(  \text{pr}_0(g_x) = \text{mod}_{\delta}(b)  \)  for b : B and unfold the definition of head, we obtain  \(  b = \text{pr}_0(c(y))  \) , so  \(  \text{pr}_0(g_x) = \text{mod}_{\delta}(b) = \text{mod}_{\delta}(\text{pr}_0(c(y)))  \) , which shows that the two first components are equal.

For the second component, we compute that

\[
\begin{array}{l} \operatorname{pr} _ {1} (f ^ {\prime} (\mathsf {m o d} _ {\delta} (y))) \\ = \operatorname{next} (f ^ {\prime}) \circledast_ {\ell} \operatorname{next} (\operatorname{mod} _ {\delta} (\operatorname{pr} _ {1} (c (y)))) \\ = \operatorname{next} (f ^ {\prime} (\mathsf {m o d} _ {\delta} (\mathsf {p r} _ {1} (c (y)))) \\ = \operatorname{next} (\hat {g} (\operatorname{mod} _ {\delta} (\operatorname{pr} _ {1} (c (y)))) \quad \text { using } p \text { through   Lemma } 9. 4 \\ = \operatorname{next} (\mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\operatorname{mod} _ {\delta} (g (\operatorname{pr} _ {1} (c (x)))))) \\ = \operatorname{next} (\mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\operatorname{mod} _ {\delta} (\operatorname{tail} (g (y)))) \quad \text { as } g \text { is   a   coalgebra   morphism } \\ = \operatorname{pr} _ {1} (\mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\mathsf {m o d} _ {\delta} (g (y)))) \quad \text { lemma } \\ = \operatorname{pr} _ {1} (\hat {g} (x)) \\ \end{array}
\]

The lemma referred to above is the fact that for any \( s: \mathsf{Str}(A) \) it is the case that

\[
\operatorname{next} (\mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\operatorname{mod} _ {\delta} (\operatorname{tail} (s)))) = \operatorname{pr} _ {1} (\mathbf {c o e} [ \delta \circ \gamma \leq 1 ] (\operatorname{mod} _ {\delta} (s)))
\]

which can be shown by a series of modal inductions.

□

We conclude this section by showing how to use these mechanisms in order to prove properties of coinductive programs. Specifically, we will replicate a proof from  \( [BGC^{+}16] \)  which shows that the zipWith operator on streams preserves commutativity. Let

\[
\operatorname{zipWith} ^ {\prime}: \Delta (\operatorname{El} (A) \rightarrow \operatorname{El} (B) \rightarrow \operatorname{El} (C)) \rightarrow \operatorname{El} (\operatorname{Str} ^ {\prime} (A)) \rightarrow \operatorname{El} (\operatorname{Str} ^ {\prime} (B)) \rightarrow \operatorname{El} (\operatorname{Str} ^ {\prime} (C))
\]

\[
\mathsf {z i p W i t h} ^ {\prime} (f) \triangleq \operatorname{löb} (\lambda r. \lambda x, y. (f \circledast_ {\delta} \mathsf {p r} _ {0} (x) \circledast_ {\delta} \mathsf {p r} _ {0} (y), r \circledast_ {\ell} \mathsf {p r} _ {1} (x) \circledast_ {\ell} \mathsf {p r} _ {1} (y)))
\]

\[
\text { zipWith } \quad : (\operatorname{El} (A) \to \operatorname{El} (B) \to \operatorname{El} (C)) \to \operatorname{El} (\operatorname{Str} (A)) \to \operatorname{El} (\operatorname{Str} (B)) \to \operatorname{El} (\operatorname{Str} (C))
\]

\[
\mathsf {z i p W i t h} (f) \triangleq \lambda x, y. \mathsf {m o d} _ {\gamma} (\mathsf {z i p W i t h} ^ {\prime} (\mathsf {m o d} _ {\delta} (f))) \circledast_ {\gamma} x \circledast_ {\gamma} y
\]

Remark 9.8. Take note of a useful pattern for programming with guarded recursion, which is visible both here and in the proof of Theorem 9.7. We first define an auxiliary function in mode t, which uses Löb induction. The main function itself is then just a thin wrapper which ‘corrects’ that with the appropriate modalities and modal combinators.