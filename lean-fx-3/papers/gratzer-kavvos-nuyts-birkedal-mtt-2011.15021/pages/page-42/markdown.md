11:42

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

Modalities. It remains to show that each $\llbracket \widehat{\bullet}_f \rrbracket \triangleq J(f)^* : \mathbf{PSh}(J(j)) \to \mathbf{PSh}(J(i))$ has a corresponding modality acting on terms and types. We will do so by using previous results. By Theorem 7.1, it suffices to construct a dependent right adjoint to $J(f)^*$. But recall that each lock functor $J(f)^*$ already has an (ordinary) right adjoint, viz. $J(f)_*$. Thus, by Lemma 7.4 it will suffice to show that the action of this right adjoint extends to types and terms. We then have DRAs, and hence a model of MTT.

The following result has previously been shown in a tech report by the third author [Nuy18, Prop. 2.2.9]. We reproduce it here for the sake of completeness.

Lemma 8.2. The right adjoint to precomposition $\mu_* : \mathbf{PSh}(\mathcal{C}) \to \mathbf{PSh}(\mathcal{D})$ induces a DRA for any $\mu : \mathcal{C} \to \mathcal{D}$. Moreover, $\mu_*$ is size-preserving for any Grothendieck universe.

Proof. We use Lemma 7.4 once more. The action of $\mu_*$ on types and terms is given by

$$\mu_* A \in \mathbf{PSh}(\int \mu_* \Gamma) = (D \in \mathcal{D}, a \in \mu_* \Gamma(D)) \mapsto \operatorname{Hom}_{\mathbf{PSh}(\int \mu^*(\mathbf{y}(D)))} (1, A\left[\widehat{[a]}\right])$$

$$\mu_* M \in \operatorname{Hom}(1, \mu_* A) = (D \in \mathcal{D}, a \in \mu_* \Gamma(D)) \mapsto (\int \widehat{[a]})^* M$$

Both of these actions are well-typed. For types, as $a \in \mu_* \Gamma(D)$ we have $[a] : \mathbf{y}(D) \Rightarrow \mu_* \Gamma$, so by transposition $\widehat{[a]} : \mu^*(\mathbf{y}(D)) \Rightarrow \Gamma$. For terms, notice that $\int \widehat{[a]} : \int \mu^*(\mathbf{y}(D)) \to \int \Gamma$, recall that $A[\sigma] \triangleq A \circ \int \sigma$, and that precomposition preserves the terminal object on-the-nose.

The presheaf action. The action of $\mu_* A$ is subtle: it is given by the functor

$$(\int \mu^* \mathbf{y}(f))^* : \mathbf{PSh}(\int \mu^* \mathbf{y}(D)) \to \mathbf{PSh}((\int \mu^* \mathbf{y}(D'))$$

for each $f : \operatorname{Hom}_{\mathcal{D}}(D', D)$. In more detail, given $f : \operatorname{Hom}_{\mathcal{D}}(D', D)$, $a \in \mu_* \Gamma(D)$, $A \in \mathbf{PSh}(\int \Gamma)$, and $x \in \mu_* A(D, a) \triangleq \operatorname{Hom}(1, A\left[\widehat{[a]}\right])$, we define $x \cdot f \in \mu_* A(D', a \cdot f)$ by

$$x \cdot f \triangleq (\int \mu^* \mathbf{y}(f))^*(x) : \operatorname{Hom}_{\mathbf{PSh}(\int \mu^*(\mathbf{y}(D')))} ((\int \mu^* \mathbf{y}(f))^* 1, (\int \mu^* \mathbf{y}(f))^*(A\left[\widehat{[a]}\right]))$$

This is of the right type; reindexing preserves the terminal, $(\int \mu^* \mathbf{y}(f))^* 1 = 1$. Moreover,

$$\widehat{[a]} \circ \mu^* \mathbf{y}(f) = \widehat{[a] \circ \mathbf{y}(f)} = \widehat{[a \cdot f]}$$

by naturality of the adjunction and of Yoneda. Using this calculation, we see that

$$(\int \mu^* \mathbf{y}(f))^*(A\left[\widehat{[a]}\right]) \triangleq A \circ \int \widehat{[a]} \circ \int \mu^* \mathbf{y}(f) = A \circ \int \widehat{[a \cdot f]} \triangleq A\left[\widehat{[a \cdot f]}\right]$$

Hence $x \cdot f \in \mu_* A(D', a \cdot f)$. This assignment is functorial because $\int -, (-)^*$ and $\mathbf{y}(-)$ are.

Naturality. We must show that both of these definitions are natural with respect to substitution, i.e. that $(\mu_* A)[\mu_* \gamma] = \mu_*(A[\gamma])$, and similarly for terms.

For types, suppose we are given $\gamma : \Delta \to \Gamma$ and $A \in \mathbf{PSh}(\int \Gamma)$. Carefully unfolding both sides of the desired equation, for any $D \in \mathcal{D}$ and $a \in \mu_* \Delta(D)$ we must show that

$$\operatorname{Hom}_{\mathbf{PSh}(\int \mu^* \mathbf{y}(D))} (1, A\left[\widehat{\mu_* \gamma_D(a)}\right]) = \operatorname{Hom}_{\mathbf{PSh}(\int \mu^* \mathbf{y}(D))} (1, A[\gamma]\left[\widehat{[a]}\right])$$

But, by naturality of both the adjunction and Yoneda:

$$\gamma \circ \widehat{[a]} = \widehat{\mu_* \gamma \circ [a]} = \left[\widehat{\mu_* \gamma_D(a)}\right]$$

Hence the two sets are the same. The calculation for terms is of a similar ilk.