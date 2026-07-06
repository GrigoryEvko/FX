Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:49

If $x : A$ and $p : \mathsf{Eq}_{\mathsf{El}(A)}(M(\mathsf{next}(x)), x)$, we calculate that

$\operatorname{löb}(M) = M(\operatorname{next}(\operatorname{löb}(M)))$ unfolding rule for löb

$$\begin{array}{l} = M(\operatorname{next}(x)) \quad \text{by Lemma 9.4 on } f \circledast \operatorname{next}(x) \circledast \operatorname{next}(p) : \blacktriangleright \mathsf{Eq}_{\mathsf{El}(A)}(\operatorname{löb}(M), x) \\ = x \quad \text{by } p \end{array}$$

Thus, this type is inhabited by the term $\lambda A$. $\operatorname{löb}(\lambda f. \lambda x. \lambda p. \operatorname{refl}(x))$.

We can also use the Löb operator on the universe to form guarded recursive types. For example, streams can be defined by$^9$

$$\operatorname{Str} \quad : \quad \mathsf{U} \to \mathsf{U} \circledast s$$

$$\operatorname{Str}(A) \triangleq \Gamma(\operatorname{löb}(\lambda X. \Delta A \times \operatorname{let} \operatorname{mod}_{\ell}(Y) \leftarrow X \text{ in } \blacktriangleright Y))$$

Str maps a constant set, i.e. a type $A \circledast s$, to the type of streams over $A$, which is again a constant set. This is done by first defining a timed set

$$A : (1 \mid \mathsf{U}), \widehat{\blacksquare}_{\gamma} \vdash \operatorname{Str}'(A) \triangleq \operatorname{löb}(\lambda X. \Delta A \times \operatorname{let} \operatorname{mod}_{\ell}(Y) \leftarrow X \text{ in } \blacktriangleright Y) : \mathsf{U} \circledast t$$

$\operatorname{Str}'(A)$ is defined by Löb induction: assuming $X : (1 \mid \blacktriangleright \mathsf{U}^{1 \leq \ell})$ we must define an element of the timed universe. This is given as the product of

- the set $A \circledast s$, considered as a constant-everywhere timed set $\Delta A \circledast t$;
- a guarded recursive call, which represents the rest of the stream.

Recalling that $\mathsf{U}^{1 \leq \ell} = \mathsf{U}$, the second component is given by modal elimination. Nevertheless, it is not immediate that the first component type-checks: we must show that

$$A : (1 \mid \mathsf{U}), \widehat{\blacksquare}_{\gamma}, \widehat{\blacksquare}_{\delta} \vdash A : \mathsf{U} \circledast s$$

But $\gamma \circ \delta = 1$, so the context is equal to $A : (1 \mid \mathsf{U}), \widehat{\blacksquare}_{1}$ and we can use $A$. Unfolding the guarded fixed point, we have that

$$\operatorname{Str}'(A) = \Delta A \times \blacktriangleright \operatorname{Str}'(A) : \mathsf{U} \circledast t$$

We apply $\Gamma$ to 'totalize' this into the constant set $\operatorname{Str}(A) \circledast s$ of guarded streams.

Even though not immediately obvious, there is a serious advantage in expressing this definition in a way that spans two modes. In previous work [BGC$^+$16] the stream type $\operatorname{Str}(A)$ was coinductive only if $A$ was provably a 'constant set,' i.e. if $A \simeq \square A$. Theorems about streams had to carry around a proof of this equivalence. In our case, defining $\operatorname{Str}(A)$ at the mode $s$ of constant sets automatically ensures that. Hence, $\operatorname{Str}(A)$ is equivalent to the familiar definition, but we no longer need to propagate proofs of constancy.

$\operatorname{Str}(A)$ supports the following operations:

$$\operatorname{cons} \quad : (A : \mathsf{U}) \to \operatorname{El}(A) \to \operatorname{El}(\operatorname{Str}(A)) \to \operatorname{El}(\operatorname{Str}(A)) \circledast s$$

$$\operatorname{cons}_A(h, t) \triangleq \operatorname{let} \operatorname{mod}_{\gamma}(t') \leftarrow t \text{ in } \operatorname{mod}_{\gamma}((\operatorname{mod}_{\delta}(h), \operatorname{next}(t')))$$

$$\operatorname{head} \quad : (A : \mathsf{U}) \to \operatorname{El}(\operatorname{Str}(A)) \to \operatorname{El}(A) \circledast s$$

$$\operatorname{head}_A(s) \triangleq \operatorname{let} \operatorname{mod}_{\gamma}(s') \leftarrow s \text{ in } \operatorname{triv}^{-1}(\operatorname{comp}_{\gamma, \delta}(\operatorname{mod}_{\gamma}(\operatorname{pr}_0(s'))))$$

$$\operatorname{tail} \quad : (A : \mathsf{U}) \to \operatorname{El}(\operatorname{Str}(A)) \to \operatorname{El}(\operatorname{Str}(A)) \circledast s$$

$$\operatorname{tail}_A(s) \triangleq \operatorname{let} \operatorname{mod}_{\gamma}(s') \leftarrow s \text{ in } \operatorname{comp}_{\gamma, \ell}(\operatorname{mod}_{\gamma}(\operatorname{pr}_1(s')))$$

$^9$We denote modalities and their counterparts on the universe by the same notation. For example, we may write $\Delta A$ to mean the type $\Gamma \vdash \langle \delta \mid A \rangle \operatorname{type}_1 \circledast m$ whenever $\Gamma, \widehat{\blacksquare}_{\delta} \vdash A \operatorname{type}_1 \circledast m$, but also to mean the term $\Gamma \vdash \operatorname{Code}(\langle \delta \mid \operatorname{El}(A) \rangle) : \mathsf{U} \circledast m$ whenever $\Gamma, \widehat{\blacksquare}_{\delta} \vdash A : \mathsf{U} \circledast m$.