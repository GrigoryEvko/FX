pullback diagram of geometric morphisms

$$\begin{array}{ccc} Sh(Y_A) & \xrightarrow{x} & Sh(G_0) \\ \downarrow q & & \downarrow l \\ Sh(X) & \xrightarrow{k_A} & [NDL] \end{array}$$

to clarify which map is $q$ and can then use the following to complete our verification of condition (1) of Proposition 4.2:

$$\begin{aligned} q^* A &\cong q^*(c_{Sh(X)}\mathcal{O}_X(A)) \\ &\cong c_{Sh(Y)}q^*\mathcal{O}_X(A) \\ &\cong c_{Sh(Y)}q^*k_A^*G_{NDL} \\ &\cong c_{Sh(Y)}x^*l^*G_{NDL} \\ &\cong x^*c_{Sh(G_0)}l^*G_{NDL} \\ &\cong x^*C. \end{aligned}$$

For (2) observe that as the locale $C$ is compact Hausdorff so is $\pi_i^*C$ where $\pi_i: G_0 \times G_0 \longrightarrow G_0$ for $i = 1, 2$; compact Hausdorff locales are locally compact and so are exponentiable. Define $G_1 = Iso_{G_0 \times G_0}((\pi_2^*C)^{\pi_1^*C})$; the exponentiation is in the category of locales over $G_0 \times G_0$ and $Iso_{G_0 \times G_0}(\bullet)$ indicates taking the sublocale of isomorphisms (explicitly, this is constructed as a sublocale of $(\pi_2^*C)^{\pi_1^*C} \times (\pi_1^*C)^{\pi_2^*C}$).

## 5 Sierpiński homotopies

**Definition 5.1** *Given a localic groupoid $\mathbb{G}$, if $P_1$ and $P_2$ are two principal $\mathbb{G}$-bundles over $X$ (for some locale $X$) then a $\mathbb{S}$-homotopy from $P_1$ to $P_2$ consists of a principal $\mathbb{G}$-bundle $Q$ over $\mathbb{S} \times X$ and two isomorphisms, $P_1 \cong (0_{\mathbb{S}}!^X, Id_X)^*Q$ and $P_2 \cong (1_{\mathbb{S}}!^X, Id_X)^*Q$ where $0_{\mathbb{S}}, 1_{\mathbb{S}}: 1 \longrightarrow \mathbb{S}$ are the bottom and top of $\mathbb{S}$.*

In good cases principal $\mathbb{G}$-bundles and $\mathbb{S}$-homotopies between them form a category, but this is not always the case. In particular the composition of two Sierpiński homotopies cannot be defined in general, but one can make sense of “a composition” of two homotopies by using the $n$-points version of the Sierpiński locale.

Let $\mathbb{S}_n$ be the $n$-point Sierpiński locale; that is, the locale such that $Sh(\mathbb{S}_n) \simeq \mathbf{Set}^{[n]}$, where $[n]$ is the category $0 \rightarrow 1 \rightarrow \cdots \rightarrow n$. For any topos $\mathcal{T}$ geometric morphisms $\mathbb{S}_n \rightarrow \mathcal{T}$ are the same as a series of points of $\mathcal{T}$ and maps between them $p_0 \rightarrow \cdots \rightarrow p_n$. The full subcategory of $\mathfrak{Cat}$ on the $[n]$ is the simplicial category $\Delta$, so the construction above defines a functor $\Delta \rightarrow \mathbf{Loc}$, where a

8