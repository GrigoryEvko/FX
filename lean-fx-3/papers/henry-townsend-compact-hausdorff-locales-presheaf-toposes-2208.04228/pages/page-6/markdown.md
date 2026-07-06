6

SIMON HENRY AND CHRISTOPHER TOWNSEND

**Lemma 3.7.** *Let $\mathfrak{K}$ be an initial-lax complete order enriched category and $F_1, F_2 : \mathcal{C}^{op} \rightarrow \mathfrak{K}$ two functors (i.e. two presheaves). Then the map $(\bullet) : Nat^{\sqsubseteq}[F_1, F_2] \rightarrow Nat[\tilde{F}_1, \tilde{F}_2]$ is an inclusion with a right adjoint (we which will write $\alpha \mapsto \psi^\alpha$). Further,*

(i) $\psi^{Id_{\tilde{F}}} = Id_F$ and $\psi^\beta \psi^\alpha \sqsubseteq \psi^{\beta \alpha}$; and,

(ii) $\psi^\alpha$ is lax-natural in $\alpha$.

*Proof.* We first observe that if $F : \mathcal{C}^{op} \rightarrow \mathfrak{K}$ is any presheaf, there are two maps $\mu : \tilde{F} \rightarrow F$ and $\epsilon : F \rightarrow \tilde{F}$, defined as follows:

$$\epsilon_a^F : \begin{array}{ccc} F(a) & \rightarrow & \tilde{F}(a) \\ x & \mapsto & (F(f)x)_{f:b \rightarrow a} \end{array} \quad \mu_a^F : \begin{array}{ccc} \tilde{F}(a) & \rightarrow & F(a) \\ (y_f)_{f:b \rightarrow a} & \mapsto & y_{Id_a} \end{array}$$

One easily checks that $\epsilon$ is a natural transformation (and takes values in $\tilde{F}(a)$) and $\mu$ is a lax natural transformation. Now, given a natural transformation $\alpha : \tilde{F}_1 \rightarrow \tilde{F}_2$, we define $\psi^\alpha : F_1 \xrightarrow{\sqsubseteq} F_2$ as the composite $\psi^\alpha : \mu^{F_2} \circ \alpha \circ \epsilon^{F_1}$; explicitly,

$$\psi_a^\alpha(x) = (\alpha_a((F_1(f)x)_{f:b \rightarrow a}))_{Id_a}$$

We then observe that

$$\begin{aligned} \psi_a^{\tilde{\phi}}(x) &= (\tilde{\phi}((F(f)(x))_{f:b \rightarrow a}))_{Id_a} \\ &= ((\phi_b F(f)(x))_{f:b \rightarrow a}))_{Id_a} \\ &= \phi(x) \end{aligned}$$

And finally for any natural transformation $\alpha : \tilde{F}_1 \rightarrow \tilde{F}_2$, $\tilde{\psi}^\alpha(x_f) = (\psi_b^\alpha(x_f))_{f:b \rightarrow a}$. But for each $f : b \rightarrow a$,

$$\begin{aligned} \psi_b^\alpha(x_f) &= (\alpha_b((F_1(g)(x_f))_{g:c \rightarrow b}))_{Id_b} \\ &\sqsubseteq (\alpha_b((x_{fg})_{g:c \rightarrow b}))_{Id_b} \\ &= (\alpha_a((x_f)_{f:b \rightarrow a}))_f \end{aligned}$$

where the last line is by naturality of $\alpha$ at $f$ and the second last line uses that $F_1(g)(x_f) \sqsubseteq x_{fg}$. Hence $\tilde{\psi}^\alpha \sqsubseteq \alpha$. Together this shows that $(\bullet) \dashv \psi(\bullet)$ and that $(\bullet) : Nat^{\sqsubseteq}[F_1, F_2] \rightarrow Nat[\tilde{F}_1, \tilde{F}_2]$ is injective.

For the 'further' part (i), the preservation of identities is immediate from construction, and the inequality is clear as $\epsilon_a^F \mu_a^F \sqsubseteq Id$ by definition of $\tilde{F}(a)$. Part (ii) follows as $\mu$ is natural in $F$ and $\epsilon$ lax natural (explicitly we are asserting that if $\phi_i : F_i \rightarrow G_i$, $i = 1, 2$ are two lax natural transformations such that $\beta \tilde{\phi}_1 = \tilde{\phi}_2 \alpha$, then $\psi^\beta \phi_1 \sqsubseteq \phi_2 \psi^\alpha$).

**Remark 3.8.** What is happening here is that $\epsilon$ and $\mu$ defined above are the unit and co-unit of a KZ-adjunction between $(\bullet) : [\mathcal{C}^{op}, \mathfrak{K}]^{\sqsubseteq} \rightarrow [\mathcal{C}^{op}, \mathfrak{K}]$ and the forgetful functor $[\mathcal{C}^{op}, \mathfrak{K}] \rightarrow [\mathcal{C}^{op}, \mathfrak{K}]^{\sqsubseteq}$. The notion of KZ-adjunction is introduced in section 4.1 of [BF06] and is sometimes called a *lax-idempotent* adjunction.

#### 4. EXAMPLES OF OUR 'LAX TO ORDINARY' FUNCTOR $(\bullet)$ IN ACTION

Given the forgoing we must now provide some 'real life' examples of $(\bullet)$ in action. The last one below corresponds to the relative version of the construction $C$ introduced in Proposition 2.3.