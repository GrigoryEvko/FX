Gel types and relativity

181

Proof. We have the functions in either direction defined above. One of inverse condition is the reduction rule for extent; the other may proven by applying extent. □

It is worth noting that, while affine variables allow us to prove this characterization without using coercion, they also prevent us from proving a function extensionality principle for bridges à la Lemma 3.2.5. That is, even when A does not depend on x, the following does not hold in general.

$$\operatorname{Bridge}(\boldsymbol{x}.(a:A) \rightarrow B, F_0, F_1) \simeq (a:A) \rightarrow \operatorname{Bridge}(\boldsymbol{x}.B, F_0 a, F_1 a) \ \mathbf{X}$$

To see why the proof of Lemma 3.2.5 does not apply, suppose we are given a function $h:(a:A) \rightarrow \operatorname{Bridge}(\boldsymbol{x}.B, F_0 a, F_1 a)$. We would like to write the following.

$$\lambda^1 \boldsymbol{x}. \lambda a. h a \boldsymbol{x} \in \operatorname{Bridge}(\boldsymbol{x}.(a:A) \rightarrow B, F_0, F_1) \ \mathbf{X}$$

But this term is not in fact well-typed. We cannot apply $h a$ to $\boldsymbol{x}$, because $a$ is not apart from $\boldsymbol{x}$: it was introduced after $\boldsymbol{x}$, so can be instantiated with terms that contain $\boldsymbol{x}$. Put another way, we have $(\boldsymbol{x}:\mathbf{I}, a:A) \setminus \boldsymbol{x} = \cdot$, so $h a$ is not well-typed in $(\boldsymbol{x}:\mathbf{I}, a:A) \setminus \boldsymbol{x}$.

To note one more point in the space of possibility, the BCH cubical sets model of homotopy type theory is based on affine cubical sets, like parametric type theory, but includes a coercion operation, like our structural cubical type theory. In this setting, we can obtain the equivalent of Theorem 9.3.2 by the extent argument. There, however, coercion can then be used to show derive function extensionality as well. (Indeed, function extensionality is a formal consequence of univalence [Uni13, §4.9], so it must hold in the BCH model.)

## 9.4 Gel types and relativity

As in cubical type theory, the coup de grâce of parametric type theory is a characterization of bridges in the universe. For cubical type theory, this is the univalence axiom (Theorem 3.2.9), which identifies paths in the universe with isomorphisms. More precisely, univalence states that the canonical function from paths to isomorphisms, implemented by coercion as shown below, is invertible.

$$p: \operatorname{Path}(\mathrm{U}, A, B) \mapsto \left[ \begin{array}{c} \operatorname{coe}_{x.p x}^{0 \rightarrow 1}(-) \\ A \xrightarrow{\simeq} B \\ \operatorname{coe}_{x.p x}^{1 \rightarrow 0}(-) \end{array} \right] \in A \simeq B$$

Recall that the inverse of this map is provided by a new type former, the V type (Section 3.1.6.2), that composes paths with isomorphisms.