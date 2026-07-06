**Corollary 4.40.** *Any map between diagrams $f : X \rightarrow Y$, where $X$ is a cofibrant diagram and $Y$ is a fibrant diagram in $\mathcal{N}_{Loc}^I$, can be factored as a trivial cofibration followed by a fibration.*

*Proof.* Now that we have theorem 4.39, we can proceed as in theorem 4.26 by first taking the factorization in $\mathcal{N}_{Reedy}^I$. $\square$

**Construction 4.41.** Denote by $K'$ the category $I$ with the opposite Reedy structure given above (the degree function reversed). We endow $\mathcal{N}^{K'}$ with the Reedy model structure. Then a diagram $Y \in \mathcal{N}_{Reedy}^{K'}$ is fibrant if $Y_2 \rightarrow 1$, $Y_0 \rightarrow Y_2$ and $Y_1 \rightarrow Y_2$ are fibrations in $\mathcal{N}$.

In this situation we can see that $\lim Y = Y_0 \times_{Y_2} Y_1$ and is fibrant in $\mathcal{N}$. We can again take a $Z \in \mathcal{N}^I$ to be the correspondence with constant value $\lim Y$. So it comes with a map $Z \rightarrow Y$.

**Lemma 4.42.** *The map $Z \rightarrow Y$ from above is a trivial fibration in $\mathcal{N}_{Loc}^I$.*

*Proof.* The same idea as in theorem 4.29 carries over here. The diagrams are even simpler. $\square$

**Lemma 4.43.** *If $Y \in \mathcal{N}_{Reedy}^{K'}$ is fibrant then there exists a trivial fibration $W \rightarrow Y \in \mathcal{N}_{Loc}^I$ with $W \in \mathcal{N}_{Loc}^I$ cofibrant.*

*Proof.* The argument of theorem 4.30 applies here too. $\square$

**Lemma 4.44.** *Let $X \rightarrow Y$ be a map in $\mathcal{N}^I$ with $X$ cofibrant and $Y$ fibrant. Then such a map can be factored as a cofibration followed by a trivial fibration.*

*Proof.* We have all ingredients to proceed as in theorem 4.35. Firstly, we can assume that $Y$ is Reedy cofibrant in $\mathcal{N}^I$ and we can take a fibrant replacement in $\mathcal{N}^K$. So we can construct the following pullback square:

$$\begin{array}{c} LY \xrightarrow{\sim} W \\ \sim \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Then we can obtain a map $X \rightarrow LY$. Factoring this map as $X \hookrightarrow X' \xrightarrow{\sim} LY$, the first map is moreover a cofibration in $\mathcal{N}_{Loc}^I$ in view of theorem 4.39. This produces the factorization $X \hookrightarrow X' \xrightarrow{\sim} Y$. $\square$

The proof of theorem 4.36 is a carbon copy from the one of theorem 4.19, the lemmas of this section provide us with all the required steps.

83