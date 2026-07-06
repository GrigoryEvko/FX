Elimination 139

In turn, by universal property of $Fcom^*$, it is enough to show that the right side is a pre-fixed-point of $R \mapsto Intro_\ell^K?(Pcoe^\nu) \cup Fcom(R)$. This splits into two inclusions, which we prove as follows.

- $Intro_\ell^K?(Pcoe^\nu) \subseteq Pcoe^{-1}(Fcom^*(Intro_\ell^K?(Pcoe^\nu)))$. This is true by Corollary 6.3.20, using the induction hypothesis.
- $Fcom(Pcoe^{-1}(Fcom^*(Intro_\ell^K?(Pcoe^\nu)))) \subseteq Pcoe^{-1}(Fcom^*(Intro_\ell^K?(Pcoe^\nu)))$. This is true by Corollaries 6.3.13 and 6.3.10. $\square$

**Theorem 6.3.22 (Coercion).** $\Psi' \Vdash \text{Ind}_{\mathcal{K}\psi}^{\Delta\psi}(\delta) = \text{Ind}_{\mathcal{K}'\psi}^{\Delta'\psi}(\delta')$ pretype support coercion for any $\Psi' \Vdash \psi \in \Psi$ and $\Psi' \Vdash \delta = \delta' \in \Delta\psi$.

*Proof.* Combining Corollaries 6.3.14 and 6.3.11 and Lemma 6.3.21, we can conclude that $Step^K(Pcoe^\nu) \subseteq Pcoe^\nu$ and therefore that $Ind_\mathcal{K} \subseteq Pcoe^\nu$. We have $Ind_\mathcal{K} \supseteq Pcoe^\nu$ by definition, so the two are equal. Thus this is exactly Lemma 6.3.17. $\square$

**Corollary 6.3.23 (Typehood).** $\Psi' \Vdash \text{Ind}_{\mathcal{K}\psi}^{\Delta\psi}(\delta) = \text{Ind}_{\mathcal{K}'\psi}^{\Delta'\psi}(\delta')$ type for any $\Psi' \Vdash \psi \in \Psi$ and $\Psi' \Vdash \delta = \delta' \in \Delta\psi$.

## 6.4 Elimination

Finally, we establish the elimination principle for a higher inductive type. The operational semantics for the eliminator and associated operators are shown in Figure 6.7. The eliminator takes a list of clauses $\mathcal{E}$ of the following format as an argument.

$$\mathcal{E} = (\ell_1 : \bar{v}_{\text{H}_1}.T_1, \dots, \ell_n : \bar{v}_{\text{H}_n}.T_n)$$

The clause for each constructor $\ell$ is an open term taking the arguments of that constructor as arguments as well as the results of recursive calls applied to each recursive argument. As an operator that evaluates its principal argument (the element of the inductive type), the proof of its well-typedness proceeds in a manner similar to that for pcoe, although this case is somewhat simpler.

Perhaps the more involved task is *stating* the elimination principle. In particular, we must define the types of the results of recursive calls at compound types as well as the coherence conditions that the case branches provided for path constructors should satisfy. To do so, we define a new, *dependent* interpretation of the argument type theory.

We first define the dependent interpretation of terms. It is easiest to understand what this means for an argument term of the form $\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \text{M} \in \text{IND}(\delta)$ where $\Theta = a_1 : \text{IND}(\delta_1), \dots, a_n : \text{IND}(\delta_n)$. Recall that in such a case, we will have $(\langle \Theta, \text{M} \rangle_{\mathcal{K}}(\chi) \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta))$