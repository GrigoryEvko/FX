that (in the $\kappa = \omega$ case) the $\omega$-presentable cofibrant object in $\text{Mod}(\mathcal{C})$ are exactly the retracts of representable models. The same proof generalizes to the $\kappa$-case to show that if $\mathcal{C}$ is a $\kappa$-clan, then $\kappa$-presentable cofibrant objects are exactly the retracts of representables. We only mention these results for context, we will not directly use them.

**Lemma 2.19.** *Given a generalized $\kappa$-algebraic theory $T$, a morphism $f : M \to N$ of $T$-models is an anodyne fibration if and only if for every generalized display map $p : X \twoheadrightarrow Y$ in $\mathbb{C}_T$, the naturality square:*

$$\begin{array}{ccc} M(X) & \longrightarrow & M(Y) \\ \downarrow & & \downarrow \\ N(X) & \longrightarrow & N(Y) \end{array}$$

*is a weak pullback square, that is, if the induced map $M(X) \to N(X) \times_{N(Y)} M(Y)$ is a surjection.*

*Proof.* By the Yoneda lemma, there is a one-to-one correspondence between elements of $M(X)$ and morphisms of models $X^* \to M$. The map $M(X) \to M(Y)$ is obtained as the composite $Y^* \to X^* \to M$, and the map $M(X) \to N(X)$ as the composite $X^* \to M \to N$. An element of $N(X) \times_{N(Y)} M(Y)$ is hence the data of maps $X^* \to N$ and $Y^* \to M$ such that the composite $Y^* \to M \to N$ and $Y^* \to X^* \to N$ coincide. This is exactly a commutative square:

$$\begin{array}{ccc} Y^* & \longrightarrow & M \\ p^* \downarrow & & \downarrow f \\ X^* & \longrightarrow & N. \end{array}$$

An element of $M(X)$ whose image in $N(X) \times_{N(Y)} M(Y)$ is then exactly a dotted diagonal filling in the square above:

$$\begin{array}{ccc} Y^* & \longrightarrow & M \\ p^* \downarrow & & \downarrow f \\ X^* & \longrightarrow & N. \end{array}$$

Hence the surjectivity of this map is equivalent to the fact that $f$ has the right lifting property against $Y^* \to X^*$ for all fibrations $X \twoheadrightarrow Y$, which concludes the proof. $\square$

17