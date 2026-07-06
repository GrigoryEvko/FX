And,

$$[\mathcal{H}, \mathbb{C}]_1 \Rightarrow [\mathcal{H} \times \mathcal{H}, \mathbb{C}]_1$$

where $\mathcal{H} \times \mathcal{H}$ is endowed with the norm $\|x_1\| + \|x_2\|$ and the two maps are given by: $f \mapsto ((x, y) \mapsto f(x + y))$ and $f \mapsto ((x, y) \mapsto f(x) + f(y))$.

A map $X \rightarrow \text{Fn } \mathcal{H}$ is then exactly the data (internally to $X$) of a metric map from $\mathcal{H} \rightarrow \mathbb{C}$ which is additive and linear with respect to complex numbers smaller than 1. As it is also linear with respect to integers, it is linear on $nD_1$ for all $n$ and this forms an open cover of $\mathbb{C}$ so it concludes the proof.

If now $\mathcal{C}$ is a unital $C^*$ locale, then one defines $\text{Spec } \mathcal{C}$ as the intersection of the two previous equalizers with the pull-back of $\{1\} \subset \mathbb{C}$ by the map of evaluation on the unit on $[\mathcal{C}, \mathbb{C}]_1$ and with the equalizer of the following diagram:

$$[\mathcal{C}, \mathbb{C}]_1 \Rightarrow [B_1 0 \times B_1 0, \mathbb{C}]$$

where $B_1 0$ is the open unit ball of $\mathcal{C}$, and the distance $B_1 0 \times B_1 0$ is given by the max distance. The two maps are given by $f \mapsto ((x, y) \mapsto f(x)f(y))$ and $f \mapsto ((x, y) \mapsto f(xy))$.

A map factoring into $\text{Spec } \mathcal{C}$ exactly corresponds to an internal character of $\mathcal{C}$.

#### 4.2.4. The following result is a localic version of the Banach-Alaoglu theorem.

**Proposition :** *Let $\mathcal{H}$ be a Banach locale, $\mathcal{C}$ a unital commutative $C^*$ locale, then the locales $\text{Fn } \mathcal{H}$ and $\text{Spec } \mathcal{C}$ are compact regular locales.*

##### **Proof :**

Compact regular locales descend along open surjections: for example because for a locale being compact and regular is the same thing as having a map to the point which is both proper and separated (see [12] C.3.2.10) and because both proper maps and separated maps descend along open morphisms, (see [12]C5.1.7). Hence it is enough to prove that some pull-back of $\text{Fn } \mathcal{H}$ and $\text{Spec } \mathcal{C}$ by an open surjection is compact and regular to conclude. In particular, by 2.3.17 one can freely assume that $\mathcal{H}$ and $\mathcal{C}$ are weakly spatial and hence that it is the completion of some Banach space $H$ or $C^*$ algebra $C$. But in this situation, a linear form or a character on the Banach locale is exactly the same as a linear form or a character on the set of points (by extension to the completion) and hence (the pull-back of) $\text{Fn } \mathcal{H}$ and $\text{Spec } \mathcal{C}$ classify the same theory as the locale $\text{Fn } H$ and $\text{Spec } C$ (also called $\text{MFn } C$) studied in [16] and [1] for the case of Grothendieck toposes, and in [6] and [7] for general elementary toposes. These references prove that these locales are indeed compact (completely) regular. $\square$

56