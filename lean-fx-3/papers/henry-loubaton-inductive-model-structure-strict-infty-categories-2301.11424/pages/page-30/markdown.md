Using again the right lifting property against $\mathbf{eq}_{n,n}^{\circ\cdots}$, we deduce that there are two marked arrows $(a^{-1})^{-1}$ and $\beta$ such that:

$$\beta: (a^{-1})^{-1} \#_n a^{-1} \rightarrow \mathbb{I}.$$

Finally, in the same way, we obtain a marked arrow:

$$\beta^{-1}: \mathbb{I} \rightarrow (a^{-1})^{-1} \#_n a^{-1}.$$

We then define $\epsilon: a \#_n a^{-1} \rightarrow \mathbb{I}$ as the composite:

$$\begin{array}{ccc} a \#_n a^{-1} & & \mathbb{I} \\ \beta^{-1} \#_n a \#_n a^{-1} \downarrow & & \uparrow \beta \\ (a^{-1})^{-1} \#_n a^{-1} \#_n a \#_n a^{-1} & \xrightarrow{(a^{-1})^{-1} \#_n \nu \#_n a^{-1}} & (a^{-1})^{-1} \#_n a^{-1} \end{array}$$

As it is a composite of marked arrows, $\epsilon$ is also marked. This then shows that $a^{-1}$ is an inverse of $a$. $\square$

### 3.24 Lemma. *Fibrant objects are prefibrant.*

*Proof.* Lemma 3.23 implies the first condition. For the second one, let $y: x \rightarrow b$ be a marked arrow where $b$ is marked. The right lifting property against $\mathbf{sat}_{n,n}^{\circ\cdots}$, choosing $a$ to be an identity, implies that $x$ is marked. Now suppose given a marked arrow $y: b \rightarrow x$ where $x$ is marked. We have a marked arrow $y^{-1}: x \rightarrow b$, and thus $b$ is also marked. $\square$

### 3.25 Proposition. *For an $m$-marked $\infty$-category $C$, the following assertions are equivalent:*

1. (1) $C$ is prefibrant in the sense of Definition 3.18.
2. (2) All equations have solutions in $C$, and whenever $a$ and $c: a \rightarrow b$ are marked, so is $b$.
3. (3) $C$ has the right lifting property against all equations and saturations.
4. (4) $C$ is fibrant for the left semi-model structure of Theorem 2.43.

*Proof.* The implication $(1) \Rightarrow (2)$ is a consequence of Proposition 3.19 and Lemma 3.20. Lemma 3.21 states $(2) \Rightarrow (3)$. By Proposition 3.8, generating anodyne cofibrations are either equations or saturations, and thus $(3) \Rightarrow (4)$. Eventually, the implication $(4) \Rightarrow (1)$ is the content of Lemma 3.24. $\square$

## 3.3 Isofibrations

In this section, we provide a simpler characterization of fibrations between fibrant objects as the “isofibrations” in the following sense:

### 3.26 Definition. A morphism between $m$-marked $\infty$-categories is said to be an *isofibration* if it has the lifting property against the maps:

$$i_n^+: \mathbb{D}_n^b \rightarrow (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$$

where $e_{n+1}$ is the unique non-identity arrow of $\mathbb{D}_{n+1}$.

30