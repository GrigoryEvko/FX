Proof. The proof is by induction on the derivations, by showing that rule derivation preserves the properties above. □

The important result of this section is the following.

Corollary B.26. For every generalized $\kappa$-algebraic theory $T$, the map $\varphi_T: T \to U(\mathbb{C}_T)$ is an interpretation.

Proof. We see that the function $\widehat{\varphi_T}: Rul(T) \to Rul(U(\mathbb{C}_T))$ is well-defined. We start with a rule $\mathcal{J}$ of $T$ and show that $\widehat{\varphi_T}(\mathcal{J})$ is a rule of $U(\mathbb{C}_T)$

1. Type judgment: Assume that $\mathcal{J} := \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ Type is a rule of $T$, from theorem A.24 it follows that

$$\widehat{\varphi_T}(\mathcal{J}) = \{x_\alpha : \widetilde{\varphi}(\Delta_\alpha)\}_{\alpha < \lambda} \vdash \widetilde{\varphi_T}(\Delta) \text{ Type}.$$

From theorem B.25 we have for any $\gamma < \lambda + 1$, the rule

$$\{x_\alpha : \overline{\Delta_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\gamma+1}}(x_\alpha)_{\alpha < \gamma+1} \equiv \widetilde{\varphi_T}(\Delta_\gamma)$$

is a derived rule of $U(\mathbb{C}_T)$. Thus, the following is also a derived rule

$$\{x_\alpha : \widetilde{\varphi_T}(\Delta_\alpha)(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\gamma+1}}(x_\alpha)_{\alpha < \lambda+1} \equiv \widetilde{\varphi_T}(\Delta).$$

Then it must be the case that $\{x_\alpha : \widetilde{\varphi}(\Delta_\alpha)\}_{\alpha < \lambda} \vdash \widetilde{\varphi_T}(\Delta)$ Type is a rule of $U(\mathbb{C}_T)$.

2. Element judgment: $\Gamma \vdash t : \Delta$. This very similar to the previous rule.
3. Type equality judgment: $\Gamma \vdash \Delta \equiv \Delta'$. Also follows from theorem B.25.
4. Term equality judgment: $\Gamma \vdash t \equiv_\Delta t'$. The same argument works.

Corollary B.27. For every generalized $\kappa$-algebraic theory $T$, the map $[\varphi_T]: T \to U(\mathbb{C}_T)$ is morphism in the category $\kappa$-GAT.

Next, we will now show that $[\varphi_-]: Id_{\kappa\text{-GAT}} \Rightarrow U \circ \mathbb{C}$ is a natural transformation.

Lemma B.28. Let $T, T'$ two generalized $\kappa$-algebraic theories and $I: T \to T'$ an interpretation between them. Then, we have a commutative diagram

$$\begin{array}{c} T \xrightarrow{[\varphi_T]} U(\mathbb{C}_T) \\ [I] \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ T' \xrightarrow{[\varphi_{T'}]} U(\mathbb{C}_{T'}). \end{array}$$

124