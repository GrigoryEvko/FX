as a cartesian lift of $E \rightarrow \pi(E_\gamma^0)$ to a map $E_\gamma \rightarrow E_\gamma^0$, and easily check that $E_\gamma$ has all the properties needed to extend $E$.

Finally, we show that any $Y \in \text{Lim}_{\gamma \in \alpha^\infty} \text{Ind}_\kappa(\mathcal{C}_\gamma)$ is indeed the colimits of this $\kappa$-filtered diagram. $\kappa$-filtered colimits being computed componentwise it is enough to check that for each $V \in \mathcal{C}_\gamma$ and any maps $V \rightarrow Y_\gamma$, the map can be factored as $V \rightarrow X_\gamma \rightarrow Y_\gamma$ where $X \rightarrow Y$ is a map in the limits with $X \in \text{Lim}_{\gamma \in \alpha^\infty} \mathcal{C}_\gamma$, and that given two such factorizations, they can be equalized by some larger $X' \rightarrow Y$. This can be achieved by exactly the same construction as above, by just adding one step: when constructing $E_\gamma^0$, one can make it so that (depending on the case) either the map $X_\gamma \rightarrow Y_\gamma$ factors through $E_\gamma^0 \rightarrow Y_\gamma$ or that the two maps $V \Rightarrow X_\gamma$ are equalized by $E_\gamma^0$, and then proceed with constructing $E_\gamma^0 \rightarrow E_\gamma$ in the same way. And this concludes the proof. $\square$

**3.7 Lemma.** *Let $C$ be any category and $A \subset B$ be a sieve inclusion. That is $A$ is a full subcategory of $B$ such that for $f : b \rightarrow a$ with $a \in A$ we have $b \in B$. Then restriction functor $C^B \rightarrow C^A$ is a cartesian fibration.*

*Proof.* We omit the details. The central observation is that given $F : B \rightarrow C$, $E : A \rightarrow C$, and $\lambda : E \rightarrow F|_B$ a cartesian lift of $\lambda$ is obtained by considering $F' : B \rightarrow C$ to be defined as

$$F'(b) = \begin{cases} E(b) & \text{if } b \in A. \\ F(b) & \text{Otherwise.} \end{cases}$$

with the functoriality of $F'$ being given by the functoriality of $E$ and $F$ respectively for the arrows whose source and target are either both in $A$ or both outside of $A$, for the arrows $f : a \rightarrow b$ with $a \in A$, and $b \notin A$, by

$$E(a) \xrightarrow{\lambda} F(a) \xrightarrow{F(f)} F(b)$$

and as $A$ is a sieve, there are no arrows going in the other direction. $\square$

**3.8 Proposition.** *Let $\mathcal{C}$ be any category, $I$ be a $\kappa$-small category and $\alpha < \kappa$ an ordinal then*

$$E_{\mathcal{C},\kappa}^{I(\alpha)} : \text{Ind}_\kappa\left(\mathcal{C}^{I(\alpha)}\right) \rightarrow \text{Ind}_\kappa(\mathcal{C})^{I(\alpha)}$$

*is an equivalence.*

*Proof.* We proceed by induction on $\alpha$, that is we assume the result is true for all $\beta < \alpha$. In the case of $\alpha = 0$, the category $I^{(\alpha)}$ is the discrete category on the set $X$ of objects of $I$, which is in particular a $\kappa$-small set. It is then easy to check that in this case the map:

$$E_{\mathcal{C},\kappa}^X : \text{Ind}_\kappa\left(\mathcal{C}^X\right) \rightarrow \text{Ind}_\kappa(\mathcal{C})^X$$

is an equivalence, which gives the case $\alpha = 0$.

If $\alpha = \beta^+$ is a successor ordinal, we show that $E_{\mathcal{C},\kappa}^{I(\alpha)}$ is an equivalence following a strategy similar to the proof of Proposition 3.5. First one can apply Corollary 2.2 to show that it is fully faithful. So we only need to show that it is essentially surjective, that is that every object $Y \in \text{Ind}_\kappa(\mathcal{C})^{I(\alpha)}$ is a $\kappa$-directed colimit of objects in $\mathcal{C}^{I(\alpha)}$. For this we will proceed in two steps: we first show that the slice $\mathcal{C}^{I(\alpha)}/Y$ is a $\kappa$-filtered category and then that $Y$ is its colimits. In

14