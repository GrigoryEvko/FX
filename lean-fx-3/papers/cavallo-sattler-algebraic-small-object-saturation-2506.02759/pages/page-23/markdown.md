$(\tau_1)_*$, we see $F^\gamma(\tau_1)_* \cong (\tau_2)_* F^\gamma$ and indeed that $F^\gamma$ pairs with $F^\gamma$ to define a strong morphism of adjunctions from $(\mathcal{E}_1)_{\mathcal{M}_1}^\gamma: (\tau_1)_* \xleftrightarrow{\leftrightarrow} (\tau_1)! : \mathcal{E}_1^\gamma$ to $(\mathcal{E}_2)_{\mathcal{M}_2}^\gamma: (\tau_2)_* \xleftrightarrow{\leftrightarrow} (\tau_2)! : \mathcal{E}_2^\gamma$. Finally, $F^\gamma$ preserves the pushouts in the definition of the transfer $\mathsf{T}_1^\gamma$ because these are levelwise cobase changes of maps in $\mathcal{M}_1$, see (2.11). Thus we have a transferred morphism $(\mathcal{E}_1, \mathsf{T}_1^\gamma) \to (\mathcal{E}_2, \mathsf{T}_2^\gamma)$ extending $F^\gamma$ by Proposition 2.3.13.

To see that $F^\gamma$ preserves colimits of $(1 + \alpha)$-chains in $\mathcal{M}_1$ for any $\alpha < \kappa$ and of $\mathsf{T}_1^\gamma$-algebraized $\kappa$-chains, recall their construction in Lemmas 2.3.22 and 2.3.23 and note that $F$ preserves all of the involved colimits, namely cobase changes of maps in $\mathcal{M}_1$ and colimits of $(1 + \alpha)$- and $\kappa$-chains in $\mathcal{M}_1$. $\square$

**Theorem 2.3.26.** The functor $\mathrm{ConfMnd}_\mathrm{p}^\kappa \to \mathbf{Fun}_s$ sending $(\mathcal{E}, \mathcal{M}, \mathsf{T})$ to the forgetful functor $U_\mathsf{T}: \mathsf{T}$-Alg $\to \mathcal{E}$ lifts through the projection $\mathbf{Adj}_s \to \mathbf{Fun}_s$ of the right adjoint.

*Proof.* Combining Lemma 2.3.25 and Theorem 2.2.14, we have a composite functor

$$\mathrm{ConfMnd}_\mathrm{p}^\kappa \longrightarrow \mathrm{ConfMnd}_{\mathrm{wp}}^\kappa \longrightarrow \mathbf{Adj}_s$$

sending a configuration $(\mathcal{E}, \mathcal{M}, \mathsf{T})$ to the free algebra adjunction for $\mathsf{T}^\gamma$. Writing $\mathrm{dom}: \mathcal{E}^\gamma \to \mathcal{E}$ for the functor sending $(A, B, f)$ to $A$, we recall from Lemma 2.3.21 that we have an equivalence $\mathsf{T}$-Alg $\simeq \mathsf{T}^\gamma$-Alg over $\mathcal{E}^\gamma$, providing a factorization

$$\mathsf{T}\text{-Alg} \xrightarrow[\simeq]{\mathrm{T}^\gamma\text{-Alg}} \xrightarrow[U_{\mathsf{T}^\gamma}]{U_\mathsf{T}} \mathcal{E}^\gamma \xrightarrow[\mathrm{dom}]{\mathrm{dom}} \mathcal{E}.$$

The projection $\mathrm{dom}: \mathcal{E}^\gamma \to \mathcal{E}$ has a left adjoint sending $A$ to $(A, TA, \mathrm{id}_{TA}: TA \to TA)$, so a left adjoint to $U_{\mathsf{T}^\gamma}$ induces a left adjoint to $U_\mathsf{T}$, the object part of our desired functor $\mathrm{ConfMnd}_\mathrm{p}^\kappa \to \mathbf{Adj}_s$.

For the functorial action, given $(F, \gamma): (\mathcal{E}_1, \mathcal{M}_1, \mathsf{T}_1) \to (\mathcal{E}_2, \mathcal{M}_2, \mathsf{T}_2)$, Theorem 2.2.14 gives us a strong morphism of adjunctions from the free algebra adjunction for $\mathsf{T}_1^\gamma$ to that for $\mathsf{T}_2^\gamma$. It is straightforward to check that $F^\gamma$ and $F$ pair to define a strong morphism of adjunctions from the pair with right adjoint $\mathrm{dom}: \mathcal{E}_1^\gamma \to \mathcal{E}_1$ to the pair with right adjoint $\mathrm{dom}: \mathcal{E}_2^\gamma \to \mathcal{E}_2$. Composing these yields a strong morphism of adjunctions from the free algebra adjunction for $\mathsf{T}_1$ to that for $\mathsf{T}_2$. $\square$

**Theorem 2.3.27.** The projection $\mathrm{ConfMnd}_\mathrm{p}^\kappa \to \mathbf{Cat}$ lifts to a functor $\mathrm{ConfMnd}_\mathrm{p}^\kappa \to \mathbf{Mnd}_s$ sending $(\mathcal{E}, \mathcal{M}, \mathsf{T})$ to the free and algebraically free monad on $\mathsf{T}$.

*Proof.* As in Theorem 2.2.15, this is an immediate consequence of Theorem 2.3.26, using that the free and algebraically free monad on a pointed endofunctor is given by the monad of the free algebra adjunction [Kel80, Proposition 22.2 and Theorem 22.3]. $\square$

### 3 The algebraic small object argument

We now use Section 2 as a tool to analyze the algebraic small object argument and prove our saturation theorems.

We recall the basic theory of AWFS's in Section 3.1. In Section 3.2, we instantiate Bourke and Garner's results with the free monad construction from Section 2 to obtain a variation of algebraic small object argument for (possibly non-cocomplete) categories equipped with a backdrop (Theorem 3.2.12). In Section 3.3 we introduce *notions of composable structure*. A notion of composable structure on a category is a notion of structured morphism such that identities have canonical structure and structured morphisms are closed under composition. We define what it means for a notion of composable structure to be *left-connected* (following Bourke and Garner) and *cellular* and observe that the double categories L-Coalg and $L_p$-Coalg associated to an AWFS (L, R)

23