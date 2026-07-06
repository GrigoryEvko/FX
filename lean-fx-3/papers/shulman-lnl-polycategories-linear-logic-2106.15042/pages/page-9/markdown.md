Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:9

A dual is equivalently a universal morphism $\psi \in \mathcal{P}(|; A, \underline{A}^*)$; see e.g. [BZ20].

These universal properties specialize in the case $\Theta = \emptyset$ to the like-named ones in the symmetric polycategory $\mathcal{P}^{\mathrm{L}}$. Thus, as shown in [CS97, BZ20], if an LNL polycategory has all $\otimes, \Im, \mathbb{1}, \perp$ then $\mathcal{P}^{\mathrm{L}}$ is a **linearly distributive category**, and if it also has all $(\cdot)^*$ then $\mathcal{P}^{\mathrm{L}}$ is **\*-autonomous** [Bar79, Bar91, CS97].

We similarly have tensors and units of *nonlinear* objects, but these turn out to coincide with cartesian *products*, by the following folklore analogue of the equivalence between positive and negative presentations of product types in structural logic.

**Proposition 2.11.** *The following are equivalent for objects $X, Y$ and $X \times Y$ of an LNL polycategory.*

(i) *There is a universal morphism $\psi \in \mathcal{P}(X, Y; \underline{X \times Y})$. In other words, composing with $\psi$ induces bijections*

$$\begin{aligned} \mathcal{P}(\Theta, X \times Y; Z) &\xrightarrow{\sim} \mathcal{P}(\Theta, X, Y; Z) \\ \mathcal{P}(\Theta, X \times Y \mid \Gamma; \Delta) &\xrightarrow{\sim} \mathcal{P}(\Theta, X, Y \mid \Gamma; \Delta). \end{aligned}$$

(ii) *There is a morphism $\psi \in \mathcal{P}(X, Y; X \times Y)$ inducing bijections*

$$\mathcal{P}(\Theta, X \times Y; Z) \xrightarrow{\sim} \mathcal{P}(\Theta, X, Y; Z)$$

(iii) *There are $\pi_1 \in \mathcal{P}(X \times Y; X)$ and $\pi_2 \in \mathcal{P}(X \times Y; Y)$ inducing bijections*

$$\mathcal{P}(\Theta; X \times Y) \xrightarrow{\sim} \mathcal{P}(\Theta; X) \times \mathcal{P}(\Theta; Y).$$

(iv) *There are morphisms $\psi \in \mathcal{P}(X, Y; X \times Y)$ and $\pi_1 \in \mathcal{P}(X \times Y; X)$ and $\pi_2 \in \mathcal{P}(X \times Y; Y)$ such that the composites*

$$\begin{aligned} (X, Y) \xrightarrow{\psi} X \times Y \xrightarrow{\pi_1} X & (X, Y) \xrightarrow{\psi} X \times Y \xrightarrow{\pi_2} Y \\ (X \times Y, X \times Y) \xrightarrow{(\pi_1, \pi_2)} (X, Y) \xrightarrow{\psi} X \times Y \end{aligned}$$

*are the image of identities under structural maps.*

*Proof.* Of course (i) implies (ii), so it suffices to prove that (ii) and (iii) each imply (iv) and that (iv) implies (i) and (iii).

Assuming (ii), let $\pi_1: X \times Y \to X$ be the image of $1_X$ under the composite

$$\mathcal{P}(X; X) \to \mathcal{P}(X, Y; X) \xrightarrow{\sim} \mathcal{P}(X \times Y; X),$$

of a structural map and the universal property of (ii), and similarly for $\pi_2$. The equations in (iv) hold by the universal property.

Assuming (iii), $\psi: (X, Y) \to X \times Y$ is the image of $(1_X, 1_Y)$ under the composite

$$\mathcal{P}(X; X) \times \mathcal{P}(Y; Y) \to \mathcal{P}(X, Y; X) \times \mathcal{P}(X, Y; Y) \to \mathcal{P}(X, Y; X \times Y)$$

of structural maps with the universal property of (iii). Again, the equations in (iv) hold by the universal property.

Conversely, assuming (iv), the right-to-left directions of (i) are composing with $(\pi_1, \pi_2)$ and a structural map, while the right-to-left direction of (iii) is composing with $\psi$ and a structural map. These are inverses by the equations in (iv). $\square$