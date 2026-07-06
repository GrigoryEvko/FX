Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:47

First, we wish to show that if we restrict ourselves to endomodalities $\mu \in \operatorname{Hom}(s, s)$ from sets to sets, the type theory is just MLTT. Looking at Fig. 11 as a finite state machine, we see that all loops on $s$ are of the form $\gamma \circ \ell^n \circ \delta$, and the equations of $\mathcal{M}_g$ allow us to prove that they are all equal to the identity $1_s$. It follows that $\langle \mu \mid A \rangle \simeq A$. Finally, as there is no non-trivial 2-cell $1_s \Rightarrow 1_s$ the variable rule reduces to

$$\frac{\mu \in \operatorname{Hom}(s, s) \qquad \Gamma \operatorname{ctx} @_S \qquad \Gamma \vdash A \operatorname{type}_\ell @_S \qquad (x : (\mu \mid A)) \in \Gamma}{\Gamma \vdash x : A @_S}$$

which is essentially the usual variable rule of MLTT.

Second, we use the combinators of Section 3.2 to prove that $\square$ is an idempotent comonad.

$$\begin{array}{l} \mathsf{dup}_A \quad : \square A \xrightarrow{\simeq} \square \square A \qquad \mathsf{extract}_A \quad : \square A \to A^{b \le 1} \\ \mathsf{dup}_A(x) \triangleq \mathbf{comp}_{b,b}^{-1}(x) \qquad \mathsf{extract}_A(x) \triangleq \mathbf{triv}^{-1}(\mathbf{coe}b \le 1) \end{array}$$

Recall the $K$ operator $- \circledast_b - : \square(A \to B) \to \square A \to \square B$ for the modality $b$, which was defined in Section 3.1. Writing $\mathsf{box}(M) \triangleq \mathsf{mod}_b(M)$, the claim that $\square$ is an internal idempotent comonad amounts to defining terms of the following types.

$$(x : \square A) \to \mathsf{Id}_{\square A}(x, \mathsf{box}(\mathsf{extract}) \circledast_b \mathsf{dup}(x)) \tag{9.2}$$

$$(x : \square A) \to \mathsf{Id}_{\square A}(x, \mathsf{extract}(\mathsf{dup}(x))) \tag{9.3}$$

$$(x : \square A) \to \mathsf{Id}_{\square \square \square A}(\mathsf{dup}(\mathsf{dup}(x)), \mathsf{box}(\mathsf{dup}) \circledast_b \mathsf{dup}(x)) \tag{9.4}$$

These can be constructed by unfolding and modal induction on $x : \square A$.

The $K$ operator $- \circledast_\ell - : \blacktriangleright(A \to B) \to \blacktriangleright A \to \blacktriangleright B$ for the modality $\ell$ almost proves that $\blacktriangleright$ is an applicative functor. It remains to show that $\blacktriangleright$ is pointed:

$$\begin{array}{l} \mathsf{next}_A \quad : A \to \blacktriangleright A \\ \mathsf{next}_A(x) \triangleq \mathbf{coe}1 \le \ell) \end{array}$$

Next, we show the defining equivalence $(*)$. We calculate that $b \circ \ell \triangleq \delta \circ \gamma \circ \ell = \delta \circ \gamma \triangleq b$, and hence that the equivalence is a corollary of a combinator given in Section 3.1:

$$\begin{array}{l} \mathsf{now}_A(x) : \square \blacktriangleright A \xrightarrow{\simeq} \square A \\ \mathsf{now}_A(x) \triangleq \mathbf{comp}_{b,\ell}^{-1}(x) \end{array}$$

As a sanity check, we can compute that the following composite is the identity:

$$\square A \xrightarrow{\mathsf{box}(\mathsf{next}) \circledast -} \square \blacktriangleright A \xrightarrow{\mathsf{now}} \square A$$

The calculation is as follows:

$$\begin{array}{l} \mathbf{comp}_{b,\ell}(\mathsf{mod}_b(\mathbf{coe}1 \le \ell)) \circledast x) \qquad \text{by induction, suppose } x = \mathsf{mod}_b(y) \\ = \mathbf{comp}_{b,\ell}(\mathsf{mod}_b(\mathbf{coe}1 \le \ell)) \circledast \mathsf{mod}_b(y)) \\ = \mathbf{comp}_{b,\ell}(\mathsf{mod}_b(\mathbf{coe}1 \le \ell))) \\ = \mathbf{comp}_{b,\ell}(\mathsf{mod}_b(\mathsf{mod}_\ell(y))) \\ = \mathsf{mod}_b(y) \qquad \text{as } b \circ \ell = b \\ = x \end{array}$$