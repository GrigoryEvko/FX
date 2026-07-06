- By definition of term substitution in a presheaf CwF, we have $t[\sigma][\gamma] = t[\sigma\gamma]$.

- We omit applications of the isomorphisms $(W \Rightarrow \Gamma) \cong (\mathbf{y}W \to \Gamma)$ and $(W \triangleright T[\gamma]) \cong (\mathbf{y}W \vdash T[\gamma])$. This is not confusing: e.g. given $W \triangleright t : T[\gamma]$, the term $\mathbf{y}W \vdash t' : T[\gamma]$ is defined by $t'[\varphi] := t \langle \varphi \rangle$.

One advantage of these notations is that we can put presheaf cells in diagrams; we will use double arrows when doing so.

### 2.3.2 On the Yoneda-embedding

We consider the Yoneda-embedding $\mathbf{y} : \mathcal{W} \to \widehat{\mathcal{W}}$.

**Proposition 2.3.1.** A morphism $\varphi : V \to W$ in $\mathcal{W}$ is:

- Mono if and only if $\mathbf{y}\varphi$ is mono,
- Split epi if and only if $\mathbf{y}\varphi$ is epi.

*Proof.* It is well-known that a presheaf morphism $\sigma : \Gamma \to \Delta$ is mono/epi if and only if $\sigma \circ \sqcup : (W \Rightarrow \Gamma) \to (W \Rightarrow \Delta)$ is injective/surjective for all $W$. Now $\mathbf{y}\varphi \circ \sqcup = \varphi \circ \sqcup$. So $\mathbf{y}\varphi$ is mono if and only if $\varphi \circ \sqcup$ is injective, which means $\varphi$ is mono. On the other hand, $\mathbf{y}\varphi$ is epi if and only if $\varphi \circ \sqcup$ is surjective, which is the case precisely when id is in its image, and that exactly means that $\varphi$ is split epi. $\square$

### 2.3.3 Lifting functors

**Theorem 2.3.2.** Any functor $F : \mathcal{V} \to \mathcal{W}$ gives rise to functors $F_! \dashv F^* \dashv F_*$, with a natural isomorphism $F_! \circ \mathbf{y} \cong \mathbf{y} \circ F : \mathcal{V} \to \widehat{\mathcal{W}}$. We will call $F_! : \widehat{\mathcal{V}} \to \widehat{\mathcal{W}}$ the **left lifting** of $F$ to presheaves, $F^* : \widehat{\mathcal{W}} \to \widehat{\mathcal{V}}$ the **central** and $F_* : \widehat{\mathcal{V}} \to \widehat{\mathcal{W}}$ the **right lifting**.$^{23}$ [Sta19]

*Proof.* Using quantifier symbols for ends and co-ends, we can define:

$$\begin{aligned} W \Rightarrow F_! \Gamma & := \exists V.(W \to FV) \times (V \Rightarrow \Gamma), \\ V \Rightarrow F^* \Delta & := FV \Rightarrow \Delta \\ W \Rightarrow F_* \Gamma & := \forall V.(FV \to W) \to (V \Rightarrow \Gamma) = (F^* \mathbf{y}W \to \Gamma). \end{aligned}$$

By the co-Yoneda lemma, we have:

$$W \Rightarrow F_! \mathbf{y}V = \exists V'.(W \to FV') \times (V' \to V) \cong (W \to FV) = (W \Rightarrow \mathbf{y}FV),$$

i.e. $F_! \mathbf{y}V \cong \mathbf{y}FV$.

Adjointness also follows from applications of the Yoneda and co-Yoneda lemmas. $\square$

**Notation 2.3.3.** • We denote the cell $(V, \varphi, \gamma) : W \Rightarrow F_! \Gamma$ as $F_! \gamma \circ \varphi$. If we rename $F_!$, then we will also do so in this notation. We will further abbreviate $F_! \gamma \circ \text{id} = F_! \gamma$ and, if $\Gamma = \mathbf{y}V$, also $F_! \text{id} \circ \varphi = \varphi$.

- If $\delta : FV \Rightarrow \Delta$, then we write $\alpha_F(\delta) : V \Rightarrow F^* \Delta$.
- If $\gamma : F^* \mathbf{y}W \to \Gamma$, then we write $\beta_F(\gamma) : W \Rightarrow F_* \Gamma$.

**Proposition 2.3.4.** A functor $F : \mathcal{V} \to \mathcal{W}$ is fully faithful if and only if $F_!$ is fully faithful.

$^2$The central and right liftings are also sometimes called the inverse image and direct image of $F$, but these are actually more general concepts and as such could perhaps cause confusion or unwanted connotations in some circumstances. The left-central-right terminology is very no-nonsense.

$^3$From the construction, it is evident that $F^*$ is precomposition with $F$ and hence, by definition of Kan extension, $F_!$ and $F_*$ are the left and right Kan extensions of $F$.

5