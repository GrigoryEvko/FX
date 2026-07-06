1.2. GRAY OPERATIONS

#### 1.2.2.16. There are two canonical morphisms

$$\nabla : \Sigma K \rightarrow \Sigma K \vee [1] \qquad \nabla : \Sigma K \rightarrow [1] \vee \Sigma K$$

that are the unique ones fulfilling

$$\nabla(\{0\}) := \{0\} \quad \nabla(\{1\}) := \{2\} \quad \nabla([x, 1]) := \begin{cases} [x, 1] + e_1 & \text{if } |x| = 0 \\ [x, 1] & \text{if } |x| > 0 \end{cases}$$

When we write $\Sigma K \rightarrow \Sigma K \vee [1]$ and $\Sigma K \rightarrow [1] \vee \Sigma K$ and nothing more is specified, it will always mean that we considered the morphisms $\nabla$.

**Proposition 1.2.2.17.** *Let $K$ be an augmented directed complex. There is a natural transformation between the colimit of the following diagram*

$$[1] \vee [K, 1] \longleftarrow [K \otimes \{0\}, 1] \longrightarrow [K \otimes [1], 1] \longleftarrow [K \otimes \{1\}, 1] \longrightarrow [K, 1] \vee [1]$$

and $[K, 1] \otimes [1]$.

*Proof.* The cone is induced by morphisms

$$\begin{aligned} & [1] \vee [K, 1] \rightarrow [K, 1] \otimes [1] \\ & (\text{resp. } [K, 1] \vee [1] \rightarrow [K, 1] \otimes [1]) \end{aligned}$$

sending an element $x$ in the basis of $[1]$ to $\{0\} \otimes x$ (resp. $\{1\} \otimes x$), an element $y$ in the basis of $[K, 1]$ to $y \otimes \{1\}$ (resp. $y \otimes \{0\}$), and by the morphism

$$f : [K \otimes [1], 1] \rightarrow [K, 1] \otimes [1]$$

defined by the formula

$$f([x \otimes y, 1]) := [x, 1] \otimes y$$

for $x$ in the basis of $K$ and $y$ in the basis of $[1]$. We leave it to the reader to check the compatibilities of this three morphisms. $\square$

### 1.2.3 Gray operations on $(0, \omega)$-categories

We follow Ara-Maltsiniotis [AM20] for the definitions and first properties of Gray operations on $(0, \omega)$-categories. Originally, these authors work with $\omega$-categories, and not with $(0, \omega)$-categories. However, this modification does not affect proof, and we then allow ourselves to use their results in our framework.

**Theorem 1.2.3.1** (Steiner, Ara-Maltsiniotis). *There is a unique colimit preserving monoidal structure on $(0, \omega)$-cat, up to a unique monoidal isomorphism, making the functor $\nu_{|\text{ADC}_\text{B}} : \text{ADC}_\text{B} \rightarrow (0, \omega)$-cat a monoidal functor, when $\text{ADC}_\text{B}$ is endowed with the monoidal structure given by the Gray tensor product.*

*Proof.* This is [AM20, theorem A.15]. $\square$

53