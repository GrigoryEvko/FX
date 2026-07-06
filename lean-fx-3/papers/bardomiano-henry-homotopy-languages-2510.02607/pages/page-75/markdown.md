Thus, we obtain the following lifts:

$$\begin{array}{ccc} B_a \rightarrow Y_a & B_a \rightarrow Y_a & B_b \rightarrow Y_b \\ B_i \downarrow \sim \nearrow l_i \downarrow Y_i & B_j \downarrow \sim \nearrow l_j \downarrow Y_j & B_k \downarrow \sim \nearrow l_k \downarrow Y_k \\ B_b \rightarrow Y_b & B_b \rightarrow Y_b & B_c \rightarrow Y_c \end{array}$$

Using this we can construct the following commutative diagram:

$$\begin{array}{ccc} B_a & \searrow \nearrow & B_b \\ \downarrow \searrow & \searrow & \downarrow \searrow \nearrow \\ B_b & \searrow & B_b \sqcup_{B_a} B_b \\ B_k & \searrow & \downarrow \searrow \nearrow \\ & & B_c \\ & & \downarrow \searrow \nearrow \\ & & B_c \\ & & \downarrow \searrow \nearrow \\ & & Y_b \end{array} \begin{array}{ccc} Y_a & \searrow & Y_j \\ \downarrow \searrow & \searrow & Y_b \\ Y_b & \searrow Y_c & Y_b \\ \downarrow & \searrow & \downarrow \\ Y_b & \searrow & Y_c \end{array}$$

where the middle trivial cofibration and fibration come from $B$ being cofibrant in $\mathcal{M}_{Loc}^J$ and $Y$ being fibrant in $\mathcal{M}_{Reedy}^K$ respectively. Then there exist a map $B_c \xrightarrow{r} Y_a$ that fits in the diagram. Furthermore, we readily see from the diagram that $Y_j r = l_k = Y_i r$. Therefore, there is a unique arrow $B_c \xrightarrow{t} Eq(Y_i, Y_j) = \text{Lim } Y$ making the obvious triangle commutative. By taking the appropriate compositions with the map $t$ we can construct a diagram map $B \rightarrow Z$ such that is a solution to the lifting problem.

For the general case

$$\begin{array}{ccc} A & \longrightarrow & Z \\ \downarrow & & \downarrow \\ B & \longrightarrow & Y \end{array}$$

one can play the same game, the only change is that the diagram is a bit more involved. $\square$

The diagram $Z$ from theorem 4.27 is not necessarily Reedy cofibrant, but it is almost cofibrant in $\mathcal{M}_{Loc}^J$ as the maps in it are trivial cofibrations. The only missing part is that $\lim Y$ is not cofibrant in $\mathcal{M}$. In order to obtain cofibrant diagram in $\mathcal{M}_{Loc}^J$, we include the following result.

**Lemma 4.30.** If $Y \in \mathcal{M}_{Reedy}^K$ is fibrant then there exists a trivial fibration $W \twoheadrightarrow Y \in \mathcal{M}_{Loc}^J$ with $W \in \mathcal{M}_{Loc}^J$ cofibrant.

75