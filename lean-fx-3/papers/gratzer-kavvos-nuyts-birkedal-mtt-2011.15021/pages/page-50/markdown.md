11:50

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

Those familiar with prior work on guarded streams may be surprised by the type of tail. The expected definition would be

$$\operatorname{tail}_{A}(s) \stackrel{\gamma}{=} \operatorname{let} \operatorname{mod}_{\gamma}(s') \leftarrow s \text{ in } \operatorname{mod}_{\gamma}(\operatorname{pr}_{1}(s'))$$

This term has type $\operatorname{El}(\operatorname{Str}(A)) \rightarrow \Gamma(\blacktriangleright \operatorname{El}(\operatorname{Str}'(A)))$. However, in our case the $\Gamma$ modality is sufficiently strong to “absorb” this extra $\blacktriangleright$: the equality $\gamma \circ \ell = \gamma$ induces an equivalence $\Gamma \circ \blacktriangleright \simeq \Gamma$, which we use to obtain the version given above. This small difference is crucial: it will internally make $\operatorname{Str}(A)$ into a final coalgebra!

**Lemma 9.6.** *These operations satisfy the expected $\beta$ and $\eta$ laws, i.e.*

(1) $(h : \operatorname{El}(A))(t : \operatorname{El}(\operatorname{Str}(A))) \rightarrow \operatorname{Eq}_{\operatorname{El}(A)}(\operatorname{head}_{A}(\operatorname{cons}_{A}(h, t)), h) \circledast s$
(2) $(h : \operatorname{El}(A))(t : \operatorname{El}(\operatorname{Str}(A))) \rightarrow \operatorname{Eq}_{\operatorname{El}(\operatorname{Str}(A))}(\operatorname{tail}_{A}(\operatorname{cons}_{A}(h, t)), t) \circledast s$
(3) $(h : \operatorname{El}(A))(t : \operatorname{El}(\operatorname{Str}(A))) \rightarrow \operatorname{Eq}_{\operatorname{El}(\operatorname{Str}(A))}(s, \operatorname{cons}_{A}(\operatorname{head}_{A}(s), \operatorname{tail}_{A}(s))) \circledast s$

*Proof.* We prove (2), the other two being similar. If $h : \operatorname{El}(A)$ and $t : \operatorname{El}(\operatorname{Str}(A))$, note that $\operatorname{El}(\operatorname{Str}(A))$ is a type of the form $\Gamma(-)$, and calculate that

$$\begin{array}{l} \operatorname{tail}_{A}(\operatorname{cons}_{A}(h, t)) \\ = \operatorname{tail}_{A}(\operatorname{cons}_{A}(h, \operatorname{mod}_{\gamma}(t'))) \quad \text{write } t = \operatorname{mod}_{\gamma}(t') \text{ by modal induction} \\ = \operatorname{tail}_{A}(\operatorname{mod}_{\gamma}((\operatorname{mod}_{\delta}(h), \operatorname{next}(t')))) \\ = \operatorname{comp}_{\gamma, \ell}(\operatorname{mod}_{\gamma}(\operatorname{pr}_{1}((\operatorname{mod}_{\delta}(h), \operatorname{next}(t'))))) \\ = \operatorname{comp}_{\gamma, \ell}(\operatorname{mod}_{\gamma}(\operatorname{next}(t'))) \\ = \operatorname{mod}_{\gamma}(t') \quad \text{as } \gamma \circ \ell = \gamma \\ = t \end{array}$$

**Theorem 9.7.** $\operatorname{Str}(A)$ is the final coalgebra for $\lambda X$. $\operatorname{El}(A) \times X : \cup \rightarrow \cup \circledast s$.

*Proof.* Given $A : \cup$ we define a coalgebra $\operatorname{uncons} : \operatorname{Str}(A) \rightarrow (\operatorname{El}(A) \times \operatorname{Str}(A)) \circledast s$ by

$$\operatorname{uncons}(s) \triangleq (\operatorname{head}_{A}(s), \operatorname{tail}_{A}(s))$$

To show finality, suppose $c : B \rightarrow \operatorname{El}(A) \times B \circledast s$ is another coalgebra. We define a function $f : B \rightarrow \operatorname{Str}(A) \circledast s$ by

$$\begin{array}{l} f' : \Delta B \rightarrow \operatorname{El}(\operatorname{Str}'(A)) \circledast t \\ f' \triangleq \operatorname{l\"ob}(\lambda f'', x. \operatorname{let} \operatorname{mod}_{\delta}(x') \leftarrow x \text{ in } (h, t)) \\ \quad \text{where } h = \operatorname{mod}_{\delta}(\operatorname{pr}_{0}(c(x'))) \\ \quad \text{and } t = f'' \circledast_{\ell} \operatorname{next}(\operatorname{mod}_{\delta}(\operatorname{pr}_{1}(c(x')))) \\ f : B \rightarrow \operatorname{El}(\operatorname{Str}(A)) \circledast s \\ f(x) \triangleq \operatorname{mod}_{\gamma}(f'(\operatorname{mod}_{\delta}(x))) \end{array}$$

This is a morphism of coalgebras: for any $x : B$ we have

$$\begin{array}{l} \operatorname{uncons}(f(x)) = (\operatorname{head}_{A}(f(x)), \operatorname{tail}_{A}(f(x))) \\ = (\operatorname{pr}_{0}(c(x)), \operatorname{tail}_{A}(f(x))) \\ = (\operatorname{pr}_{0}(c(x)), \operatorname{comp}_{\gamma, \ell}(\operatorname{mod}_{\gamma}(\operatorname{pr}_{1}(f'(x)))))) \\ = (\operatorname{pr}_{0}(c(x)), \operatorname{comp}_{\gamma, \ell}(\operatorname{mod}_{\gamma}(\operatorname{next}(f') \circledast_{\ell} \operatorname{next}(\operatorname{mod}_{\delta}(\operatorname{pr}_{1}(c(x))))))) \\ = (\operatorname{pr}_{0}(c(x)), f(\operatorname{pr}_{1}(c(x)))) \end{array}$$