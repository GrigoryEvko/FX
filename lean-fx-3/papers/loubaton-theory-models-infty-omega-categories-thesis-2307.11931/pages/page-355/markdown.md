6.2. YONEDA LEMMA AND APPLICATIONS

Lemma 6.2.2.4. Suppose we have two morphisms $f : C \to D$ and $g : C \to D$ between locally U-small $(\infty, \omega)$-categories as well as a natural transformation $\nu : f \to g$. This induces a commutative diagram

$$\begin{array}{c} \hom_C(a, b) \longrightarrow \hom_D(g(a), g(b)) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow_{(\nu_a)!} \\ \hom_D(f(a), f(b)) \xrightarrow{(\nu_b)!} \hom_D(f(a), g(b)) \end{array}$$

natural in $a : C^t, b : C$.

Proof. Remark that $\hom_{[1]}(0, 1) \sim \hom_{[1]}(1, 1) \sim \hom_{[1]}(0, 0) = 1$. Using the naturality of the hom functor, we have a commutative diagram

$$\begin{array}{c} \hom_C(a, b) \times \hom_{[1]}(0, 0) \longrightarrow \hom_D(f(a), f(b)) \\ \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow_{(\nu_b)!} \\ \hom_C(a, b) \times \hom_{[1]}(0, 1) \longrightarrow \hom_D(f(a), g(b)) \\ \sim \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \uparrow_{(\nu_a)!} \\ \hom_C(a, b) \times \hom_{[1]}(1, 1) \longrightarrow \hom_D(g(a), g(b)) \end{array}$$

where the left-hand vertical morphisms are equivalences.

Proposition 6.2.2.5. Let $u : C \to D$ and $v : D \to C$ be two functors between locally U-small $(\infty, \omega)$-categories, $\mu : id_C \to vu$, $\epsilon : uv \to id_D$ be two natural transformations coming along with equivalences

$$(\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u \quad (v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v.$$

If we set $\phi$ as the composite

$$\hom_D(u(a), b) \to \hom_C(vu(a), v(b)) \xrightarrow{(\mu_a)!} \hom_C(a, v(b)),$$

the triple $(u, v, \phi)$ is an adjoint structure. Moreover, the unit of the adjunction is $\mu$ and its counit is $\epsilon$.

Proof. Suppose we have such data. We define $\psi$ as the composite

$$\hom_C(a, v(b)) \to \hom_D(u(a), uv(b)) \xrightarrow{(\epsilon_a)!} \hom_D(u(a), b)$$

natural in $a : C^t$ and $b : D$. We then have to show that these two morphisms are inverse

345