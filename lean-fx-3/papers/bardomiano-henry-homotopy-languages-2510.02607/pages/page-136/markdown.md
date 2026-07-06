One term axiom

$$x : X \vdash s(x) : X$$

and one type equality axiom

$$x : X \vdash O(x) = O(s(x))$$

Models of $T$ are given by a set $X$, with a function $s : X \to X$ together with a collection of set indexed by the quotient $X/s$. It is then possible to prove ( we omit the details here) that:

- The category of models of $T$, equipped with its weak factorization system as defined in section 2.2, does not satisfy J. Frey's characterization, hence is not the category of model of a clan.
- The category of models of the underlying clan of $\mathbb{C}_T$ is equivalent to the category of models of the theory $T'$, similar to $T$ but where the type equality axiom is replaced by the existence of a bijection between $O(x)$ and $O(s(x))$.

### B.5 Coclans and contextual categories

In this section, we prove that every $\kappa$-contextual category can be obtained by strictification of a $\kappa$-clan. Clans were introduced in [Joy17], a related definition appears in [Hen20] under the name category with fibrations.

**Definition B.55.** We say that a category $\mathcal{C}$ is a $\kappa$-coclan if it has a collection of maps $\operatorname{COF}(\mathcal{C})$ satisfying the following conditions:

1. $\mathcal{C}$ has initial object 0.
2. For any $X \in \mathcal{C}$, the map $0 \to X$ is an element in $\operatorname{COF}(\mathcal{C})$.
3. Any isomorphism is an element of $\operatorname{COF}(\mathcal{C})$.
4. $\operatorname{COF}(\mathcal{C})$ is closed under compositions.
5. $\operatorname{COF}(\mathcal{C})$ is closed under pushouts: If $f : A \to C$ is a morphism in $\mathcal{C}$ and $A \to B \in \operatorname{COF}(\mathcal{C})$, then the map $C \to C \coprod_A B$ is an element in $\operatorname{COF}(\mathcal{C})$.
6. $\operatorname{COF}(\mathcal{C})$ is closed under transfinite compositions: for any $\lambda < \kappa$ and any $\lambda$-diagram of maps in $\operatorname{COF}(\mathcal{C})$

$$A_0 \longrightarrow A_1 \longrightarrow A_2 \longrightarrow \cdots$$

$\operatorname{Colim}_\lambda A_\alpha$ exists and the map $A_0 \to \operatorname{Colim}_\lambda A_\alpha$ belongs to $\operatorname{COF}(\mathcal{C})$.

136