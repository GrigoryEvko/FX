$\epsilon_{X_{\infty}} \circ x_{\infty}$ is induced by the composite fence, and since $g_{n+1} = \epsilon_{X_n} \circ x_{n+1}$ this is

$$\begin{array}{c} X_{\infty} \longrightarrow \cdots \longrightarrow X_3 \xrightarrow{g_3} X_2 \xrightarrow{g_2} X_1 \xrightarrow{g_1} X_0 \\ 1_{X_{\infty}} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad X_{\infty} \longrightarrow \cdots \longrightarrow X_3 \xrightarrow{g_3} X_2 \xrightarrow{g_2} X_1 \xrightarrow{g_1} X_0 \end{array}$$

which induces the identity $1_{X_{\infty}}$. Thus, $X_{\infty}$ is an F-coalgebra.

Now suppose $y : Y \rightarrow FY$ is another F-coalgebra. We construct inductively maps $h_n : Y \rightarrow X_n$ such that $x_{n+1} \circ h_{n+1} = Fh_n \circ y$ and $g_{n+1} \circ h_{n+1} = h_n$. We start with $h_0 : Y \rightarrow X_0 = \mathbb{1}$ the unique morphism, and $h_1 : Y \rightarrow X_1 = FX_0$ the composite $Y \xrightarrow{y} FY \xrightarrow{Fh_0} FX_0$. Then we induce $h_{n+1}$ by the universal property of the pullback defining $X_{n+1}$:

$$\begin{array}{c} Y \xrightarrow{h_{n+1}} X_{n+1} \xrightarrow{x_{n+1}} FX_n \\ h_n \downarrow g_{n+1} \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \end{array}$$

This is valid because using the inductive assumptions about $h_n$ and $h_{n-1}$, we have

$$\begin{aligned} \epsilon_{X_n} \circ Fh_n \circ y &= h_n \circ \epsilon_Y \circ y \\ &= h_n \end{aligned}$$

and

$$\begin{aligned} Fg_n \circ Fh_n \circ y &= F(g_n \circ h_n) \circ y \\ &= Fh_{n-1} \circ y \\ &= x_n \circ h_n, \end{aligned}$$

and the two triangles relating to $h_{n+1}$ show that it has the necessary properties.

Now, the equations $g_{n+1} \circ h_{n+1} = h_n$ imply there is an induced map $h_{\infty} : Y \rightarrow X_{\infty}$, such that $x_{\infty} \circ h_{\infty}$ is induced by the composites $x_{n+1} \circ h_{n+1}$. But $x_{n+1} \circ h_{n+1} = Fh_n \circ y$, and the morphisms $Fh_n$ induce the limit map $Fh_{\infty}$. Thus, $h_{\infty}$ is an F-coalgebra morphism.

Finally, suppose $k : Y \rightarrow X_{\infty}$ is any F-coalgebra morphism, so we have $x_{\infty} \circ k = Fk \circ y$. Then $k$ is uniquely determined by the maps $k_n : Y \rightarrow X_n$, and we have $x_{n+1} \circ k_{n+1} = Fk_n \circ y$. But this equation implies by induction that $k_n = h_n$ for all $n$, hence $k = h_{\infty}$. $\square \triangleleft$

### 4.5.2 Displayed coinductive types

Let $\mathcal{C}$ be a dTT natural model with levels, telescopes, décalage, telescope display, type display respecting $\Pi$-types and universes, and $\Pi$-telescopes. We will apply theorem 4.45 in $\text{Tel} \parallel (\Gamma \cdot \widehat{\bullet}_{\Delta \square} \mid \Phi)$, in which the fibrations are the morphisms isomorphic to the dependent projection from some telescope,

$$(\Gamma \cdot \widehat{\bullet}_{\Delta \square} \mid \Phi \mid \Theta \mid Y) \rightarrow (\Gamma \cdot \widehat{\bullet}_{\Delta \square} \mid \Phi \mid \Theta).$$

83