6.2. YONEDA LEMMA AND APPLICATIONS

By naturality, for any object $c$ of $C$, the pullback of the previous equivalence along $C^t \times \{c\}$ is the identity. In particular, the induced morphism $\hom(c, c) \to \hom(c, c)$ between the fibers over $(c, c)$ preserves the object $\{id_c\}$. According to lemma 6.2.1.17, the previous equivalence induces a morphism

$$\int_{C^t \times \widehat{C}} \hom_{\widehat{C}}(y_-, \_) \to \int_{C^t \times \widehat{C}} \mathrm{ev} \, . \tag{6.2.1.19}$$

that comes along, by construction, with a commutative square

$$\begin{array}{c} \{id_{y_c}\} \longrightarrow \hom_{\widehat{C}}(y_c, y_c) \sim \{y_c\}^* \int_{\widehat{C}} \hom_{\widehat{C}}(y_c, \_) \\ \Big\| \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big\downarrow \\ \{id_c\} \longrightarrow \hom_C(c, c) \sim \{y_c\}^* \int_{\widehat{C}} \mathrm{ev}(c, \_) \end{array}$$

for any object $c$ of $C$. The restriction of the morphism (6.2.1.19) to $\widehat{C} \times \{c\}$ is then equivalent to the natural transformation given in proposition 6.2.1.14, and is an equivalence. As equivalences between left cartesian fibrations are detected on fibers, this concludes the proof.

**Corollary 6.2.1.20.** *The universal left cartesian fibration with U-small fibers is the canonical projection $\underline{\omega}_{1/}^\sharp \to \underline{\omega}^\sharp$.*

*Proof.* The corollary 6.2.1.20 implies that universal left cartesian fibration with U-small fibers is $\int_{\underline{\omega}} id$. The Yoneda lemma implies that this left cartesian fibration is equivalent to $\int_{\underline{\omega}} \hom_{\underline{\omega}}(1, \_)$. Eventually, the proposition 6.2.1.10 states that this left cartesian fibration is equivalent to $\underline{\omega}_{1/}^\sharp \to \underline{\omega}^\sharp$.

### 6.2.2 Adjoint functors

**Definition 6.2.2.1.** Let $C$ and $D$ be two locally U-small $(\infty, \omega)$-categories and $u : C \to D$, $v : D \to C$ two functors. An *adjoint structure* for the pair $(u, v)$ is the data of a invertible natural transformation

$$\phi : \hom_D(u(\_), \_) \sim \hom_C(\_, v(\_))$$

In this case, $u$ is a *left adjoint* of $v$ and $v$ is a *right adjoint* of $u$.

**Proposition 6.2.2.2.** *Let $u : C \to D$ be a functor between locally U-small $(\infty, \omega)$-categories. For $b$ an object of $D$, we define $(C^t)_{b/}^\sharp$ and $C_{b/}^\sharp$ as the marked $(\infty, \omega)$-categories fitting in the cartesian squares:*

$$\begin{array}{ccc} (C^t)_{/b}^\sharp & \longrightarrow & (D^t)_{b/}^\sharp & C_{b/}^\sharp \longrightarrow D_{b/}^\sharp \\ \downarrow & \downarrow & \downarrow & \downarrow \\ (C^t)^\sharp & \xrightarrow{u^t} & (D^t)^\sharp & C^\sharp \xrightarrow{u} D^\sharp \end{array}$$

343