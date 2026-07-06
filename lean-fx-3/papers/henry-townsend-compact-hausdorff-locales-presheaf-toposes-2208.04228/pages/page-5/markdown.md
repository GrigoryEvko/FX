COMPACT HAUSDORFF LOCALES IN PRESHEAF TOPOSES

5

**Proposition 3.4.** *The order enriched category* **NDL** *is initial-lax complete with initial lax limits being created in* **Pos**.

*Proof.* Consider a diagram $D : \mathcal{J} \to \mathbf{NDL}$, such that $\mathcal{J}$ has an initial object. For any object $j$ of $\mathcal{J}$, write $\mathcal{Y} : 0 \to j$ for the unique map to $j$. We have commented already that the category of distributive lattices is lax complete. Since a morphism of normal distributive lattices is the same thing as a morphism of distributive lattices, we must just check that the distributive lattice

$$N = \{(a_j) \in \prod_j D(j) | D(f)a_i \le a_j \ \forall f : i \to j \in \mathcal{J}\}$$

is normal. Say $(a_j) \vee (b_j) = 1_N$. Then $a_0 \vee b_0 = 1_{D0}$. So as $D0$ is normal there exists $a'_0$ and $b'_0$ such that $a'_0 \wedge b'_0 = 0_{D0}$ and $a'_0 \vee b_0 = 1_{D0} = a_0 \vee b'_0$. Let $a'_j = D(\mathcal{Y})(a'_0)$ and $b'_j = D(\mathcal{Y})(b'_0)$. Then $(a'_j), (b'_j) \in N$ and $(a'_j) \wedge (b'_j) = 0_N, (a'_j) \vee (b_j) = 1_N = (a_j) \vee (b'_j)$, the last because $D(\mathcal{Y})(b_0) \le b_j$ and $D(\mathcal{Y})(a_0) \le a_j$ for every $j$. $\square$

**Construction 3.5.** Given a functor $F : \mathcal{C}^{op} \to \mathfrak{K}$, with $\mathfrak{K}$ an initial-lax complete order enriched category, then we can define a new functor $\tilde{F} : \mathcal{C}^{op} \to \mathfrak{K}$ by $\tilde{F}(a) = lim_{(\mathcal{C}/a)^{op}} \bigsqsubseteq ((\mathcal{C}/a)^{op} \xrightarrow{\Sigma_a^{op}} \mathcal{C}^{op} \xrightarrow{F} \mathfrak{K})$, with morphisms defined via the universal characterisation of the lax limit. (Recall $\Sigma_a : \mathcal{C}/c \to \mathcal{C}$ is the forgetful functor, and $\mathcal{C}/a$ has a terminal object for every object $a$ of $\mathcal{C}$.) We will use point set notation in what follows as a convenient notation; so,

$$\tilde{F}(a) = \{(x_f)_{f:b \to a} \in \prod_{f:b \to a} F(b) | F(g)x_f \sqsubseteq x_{fg} \ \forall c \xrightarrow{g} b \xrightarrow{f} a\}$$

and for $(x_f) \in \tilde{F}(a')$, and $h : a' \to a$ we define

$$(\tilde{F}(h))_{f'} = x_{hf'}$$

for all $f' : b' \to a'$.

**Construction 3.6.** Let $F_1, F_2 : \mathcal{C}^{op} \to \mathfrak{K}$ be two functors, with $\mathfrak{K}$ an initial-lax complete order enriched category.

If $\phi : F_1 \xrightarrow{\sqsubseteq} F_2$ is a lax natural transformation, define $\tilde{\phi} : \tilde{F}_1 \to \tilde{F}_2$ by

$$[\tilde{\phi}_a((x))]_f = \phi_b(x_f)$$

for all $f : b \to a$. $\tilde{\phi}_a(x)$ is indeed an element of $\tilde{F}_2$ as for any $c \xrightarrow{g} b \xrightarrow{f} a$, we have

$$\begin{aligned} F_2(g)[\tilde{\phi}_a((x))]_f &= F_2(g)\phi_b(x_f) \\ &\sqsubseteq \phi_c(F_1(g)x_f) \sqsubseteq \phi_c(x_{fg}) = [\tilde{\phi}_a((x))]_{fg} \end{aligned}$$

And finally, $\tilde{\phi}$ is a natural transformation, as for any $h : a' \to a$ and $f' : b' \to a'$ we have

$$\begin{aligned} [\tilde{F}_2(h)](\tilde{\phi}_a((x)))]_{f'} &= [\tilde{\phi}_a((x))]_{hf'} \\ &= \phi_{b'}(x_{hf'}) = \phi_{b'}(([\tilde{F}_1(h))_{f'}) = [\tilde{\phi}_{a'}([\tilde{F}_1(h))]_{f'} \end{aligned}$$

This construction clearly defines an order enriched functor

$$(\tilde{\cdot}) : [\mathcal{C}^{op}, \mathfrak{K}]^{\sqsubseteq} \to [\mathcal{C}^{op}, \mathfrak{K}].$$