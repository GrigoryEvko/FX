172

Parametric cubical type theory

Otherwise, restriction is defined as follows.

$$(\Gamma, y : \mathbb{I}) \setminus \boldsymbol{x} := (\Gamma \setminus \boldsymbol{x}), y : \mathbb{I}$$

$$(\Gamma, \boldsymbol{y} : \mathbb{I}) \setminus \boldsymbol{x} := \begin{cases} \Gamma & \text{if } \boldsymbol{x} = \boldsymbol{y} \\ (\Gamma \setminus \boldsymbol{x}), \boldsymbol{y} : \mathbb{I} & \text{otherwise} \end{cases}$$

$$(\Gamma, \xi) \setminus \boldsymbol{x} := \begin{cases} \Gamma \setminus \boldsymbol{x} & \text{if } \boldsymbol{x} \text{ occurs in } \xi \\ (\Gamma \setminus \boldsymbol{x}), \xi & \text{otherwise} \end{cases}$$

$$(\Gamma, a : A) \setminus \boldsymbol{x} := \Gamma \setminus \boldsymbol{x}$$

Given contexts $\Gamma = \Gamma'$ ctx, substitutions $\Gamma'' \gg \gamma = \gamma' \in \Gamma$, and terms $\Gamma \gg \boldsymbol{r} = \boldsymbol{r}' \in \mathbb{I}$, we have that $\Gamma'' \setminus \boldsymbol{r}\gamma \gg (\gamma : \Gamma) \setminus \boldsymbol{r} = (\gamma' : \Gamma') \setminus \boldsymbol{r}' \in \Gamma \setminus \boldsymbol{r}$.

Proof. If $\boldsymbol{r}$ is equal to a constant, then this is immediate. Otherwise, we go by induction on the derivation of $\Gamma'' \gg \gamma = \gamma' \in \Gamma$.

- Case: $\Gamma' \gg \cdot = \cdot \in \cdot$. Immediate.

- Case: $\Gamma'' \gg (\gamma, s/\boldsymbol{y}) = (\gamma', s'/\boldsymbol{y}) \in (\Gamma, \boldsymbol{y} : \mathbb{I})$. If $\boldsymbol{r} = \boldsymbol{y}$, then we have $\Gamma'' \setminus s \gg \gamma = \gamma' \in \Gamma$ by assumptions of this rule, which is exactly what we need. If not, then we instead have the substitutions $\Gamma'' \setminus s \setminus \boldsymbol{r}\gamma \gg (\gamma : \Gamma) \setminus \boldsymbol{r} = (\gamma' : \Gamma') \setminus \boldsymbol{r}' \in \Gamma \setminus \boldsymbol{r}$ by induction hypothesis, to which we append $\Gamma'' \setminus \boldsymbol{r}\gamma \gg s \in \mathbb{I}$ using the fact that $\Gamma'' \setminus s \setminus \boldsymbol{r}\gamma = \Gamma'' \setminus \boldsymbol{r}\gamma \setminus s$.

- Case: $\Gamma' \gg (\gamma, r/x) = (\gamma', r/x) \in (\Gamma, x : \mathbb{I})$. By induction hypothesis and the substitution formation rule for path dimensions.

- Case: $\Gamma' \gg \gamma = \gamma' \in (\Gamma, \xi)$. By induction hypothesis and the substitution formation rule for constraints.

- Case: $\Gamma' \gg (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)$. Immediate by induction hypothesis. $\square$

Remark 9.1.12. On the level of syntax, the effect of a restricted substitution is the same as that of the original substitution. That is, if $M$ is a term depending only on the variables in $\Gamma \setminus \boldsymbol{r}$, then $M[(\gamma : \Gamma) \setminus \boldsymbol{r}] = M\gamma$.

Now we get down to specifics. The new operational semantics rules we use for parametric type theory are shown in Figure 9.1. We construct our type systems in the usual way, taking the least fixed-point of an operator that introduces one layer of each type former. Below we get a sneak peak at the key type formers of parametric type theory, the bridge and Gel types, which we introduce in more detail below.

Example 9.1.13 (Small type system). We define an operator $IP$ on candidate type systems as follows: given $\tau$, $IP(\tau)$ is the union of the following clauses.