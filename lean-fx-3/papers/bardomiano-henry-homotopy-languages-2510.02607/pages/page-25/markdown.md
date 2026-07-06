## 2.4 The language of a weak model category and two invariance theorems

Construction 2.33. Given $\mathcal{M}$ a weak model category, the category $\mathcal{M}^{\mathrm{COF}}$ of cofibrant objects with cofibrations between them forms a coclan. We define the language of $\mathcal{M}$ to be the language of the coclan $\mathcal{M}^{\mathrm{COF}}$. For any regular cardinal $\lambda$, we denote by $\mathbb{L}_{\lambda}^{\mathcal{M}}$ the $\lambda$-boolean algebra $\mathbb{L}_{\lambda}^{\mathcal{M}^{\mathrm{COF}}}$ over $\mathcal{M}^{\mathrm{COF}}$.

Note that for each cofibrant object $X \in \mathcal{M}$, we have a set (or possibly a class if $\mathcal{M}$ is large) of formulas $\mathbb{L}_{\lambda}^{\mathcal{M}}(X)$.

Remark 2.34. There is a size issue to be mentioned here. In most practical examples, $\mathcal{M}^{\mathrm{COF}}$ is a large category while the construction of $\mathbb{L}_{\lambda}^{\mathcal{M}^{\mathrm{COF}}}$ developed in section 2.3 assumes it is a small category. We can deal with this by invoking a larger Grothendieck universe, but this has a practical consequence: The set of formulas $\mathbb{L}_{\lambda}^{\mathcal{M}}(X)$ might not be a small set. Indeed, it lives in the same Grothendieck universe as the one in which $\mathcal{M}^{\mathrm{COF}}$ is small.

Construction 2.35. If $X \in \mathcal{M}$ then we can define a model of the coclan $\mathcal{M}^{\mathrm{COF}}$ using the restricted Yoneda embedding:

$$\begin{array}{c c c c} \updownarrow_{X}: & (\mathcal{M}^{\mathrm{COF}})^{\mathrm{op}} & \to & \mathbf{Set} \\ & c & \mapsto & \mathrm{Hom}(c, X), \end{array}$$

which defines a functor $\updownarrow : \mathcal{M} \to \mathrm{Mod}(\mathcal{M}^{\mathrm{COF}})$.

Definition 2.36. Let $\mathcal{M}$ be a weak model category. For $c \in \mathcal{M}$ a cofibrant object, and $X \in \mathcal{M}$ any object, $v : c \to X$ and $\phi \in \mathbb{L}_{\lambda}^{\mathcal{M}}(c)$ we write

$$X \vdash \phi(v)$$

to mean

$$\updownarrow_{X} \vdash \phi(v)$$

where $v$ is seen as an element of $\updownarrow_{X}(c) = \mathrm{Hom}(c, X)$.

Remark 2.37. In the special case where $\mathcal{M} = \mathrm{Mod}(T)$ is the category of models of a generalized $\kappa$-algebraic theory (or more generally of a $\kappa$-coclan), then $\mathbb{L}_{\lambda}^{\mathcal{M}}$ is the initial $\lambda$-boolean algebra over the coclan of all cofibrant objects of $\mathcal{M}$, while the syntactic category of $T$ is equivalent to a full sub-$\kappa$-coclan of that. In particular, there is a morphism of $\lambda$-boolean algebras over the syntactic category $\mathcal{C}_T$

$$\mathbb{L}_{\lambda}^{T}(X) \to \mathbb{L}_{\lambda}^{\mathcal{M}}(X) \qquad (\mathrm{For}\ X \in \mathcal{C}_T).$$

25