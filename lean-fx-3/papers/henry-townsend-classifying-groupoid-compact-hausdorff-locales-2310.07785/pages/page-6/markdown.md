## 4 Geometric stacks

We now provide some conditions for when a stack on **Loc** is a stack of principal bundles for some localic groupoid.

**Definition 4.1** *A stack $M : \mathbf{Loc}^{op} \longrightarrow \mathfrak{GPD}$ of groupoids is geometric if there exists a localic groupoid $\mathbb{G}$ such that $M(X) \simeq \operatorname{Prin}_{\mathbb{G}}(X)$ naturally for every locale $X$.*

**Proposition 4.2** *Let $M : \mathbf{Loc}^{op} \longrightarrow \mathfrak{GPD}$ be a stack of groupoids. Assume that:*

*(1) there exists a locale $G_0$ and an object $C$ of $M(G_0)$ such that for any $X$ and any $A \in M(X)$ there exists an effective descent morphism $q : Y \longrightarrow X$ and a morphism $x : Y \longrightarrow G_0$ such that $M(q)(A) \cong M(x)(C)$*

*(2) there is a locale $G_1$ such that,*

$$\mathbf{Loc}(X, G_1) \cong \{(f, g, \theta) | f, g : X \longrightarrow G_0, \theta : M(f)(C) \xrightarrow{\cong} M(g)(C)\}$$

*naturally, for any other object $X$ of $\mathbf{Loc}$.*

*Then $M$ is geometric.*

*Proof:* Certainly $G_0$ and $G_1$ must determine a groupoid $\mathbb{G}$; for example, the identity $G_1 \longrightarrow G_1$ determines via (2) two maps, $d_0 : G_1 \longrightarrow G_0$ and $d_1 : G_1 \longrightarrow G_0$ and $\theta : M(d_0)(C) \longrightarrow M(d_1)(C)$. The maps $d_0$ and $d_1$ are the domain and codomain maps, and the image of $(d_1, d_0, \theta^{-1})$ under the isomorphism of (2) determines the inverse map $i : G_1 \longrightarrow G_1$. Note that therefore by naturality of (1) the image of any $\psi : X \longrightarrow G_1$ under the isomorphism of (1) is necessarily of the form $(d_0\psi, d_1\psi, \theta)$. For multiplication, by definition of the pullback $G_1 \times_{G_0} G_1$ (i.e. pull $d_1$ back along $d_0$) and using (2), morphisms $\phi : X \longrightarrow G_1 \times_{G_0} G_1$ are in bijection with 5-tuples $(d_0\pi_1\phi, d_1\pi_1\phi = d_0\pi_2\phi, d_1\pi_2\phi, \theta_1, \theta_2)$. Therefore any such $\phi$ gives rise to a morphism $X \longrightarrow G_1$ as the image under the isomorphism of (2) of

$$\begin{aligned} M(d_0\pi_1\phi)(C) &\cong M(\phi)M(\pi_1)M(d_0)(C) \xrightarrow{\theta_1} M(\phi)M(\pi_1)M(d_1)(C) \cong \\ M(\phi)M(\pi_2)M(d_0)(C) &\xrightarrow{\theta_2} M(\phi)M(\pi_2)M(d_1)(C) \cong M(d_1\pi_2\phi)(C). \end{aligned}$$

Define $m : G_1 \times_{G_0} G_1 \longrightarrow G_1$ via $\phi = Id_{G_1 \times_{G_0} G_1}$. The unit map $s : G_0 \longrightarrow G_1$ is the inverse image of the triple $(Id_{G_0}, Id_{G_0}, Id_C)$ under (2).

Given a principal $\mathbb{G}$-bundle $(Q_x, a)$ over $X$ (say via $q : Q \longrightarrow X$), there is a cocycle $(\psi^Q, x) : \mathbb{Q}_q \longrightarrow \mathbb{G}$. By applying (2) at $Q \times_X Q \longrightarrow G_1$ and exploiting the naturality of (2) we obtain an object, $(M(x)(C), \theta_Q)$, of $Des(M, q)$ which, by definition of stack, corresponds uniquely up to isomorphism to an object $A^Q$ of $M(X)$ with the property $M(p)(A^Q) = M(x)(C)$.

Next, let us clarify that if $r : P \longrightarrow Q$ is an effective descent morphism then the cocycle $(\psi^Q(r \times r), xr)$ gives rise to an object $(M(xr)(C), \theta_P)$ of $Des(M, qr)$

6