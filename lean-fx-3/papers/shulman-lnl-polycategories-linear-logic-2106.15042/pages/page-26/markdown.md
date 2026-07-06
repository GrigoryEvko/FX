1:26

M. SHULMAN

Vol. 19:2

- For symmetric polycategories, cartesian morphisms specialize to the cartesian and opcartesian morphisms of [BZ20].
- For categories, cartesian morphisms specialize to the traditional notion of cartesian and opcartesian morphism.

Example 4.7. Cartesian morphisms can express restricted universal properties. For instance, in Definition 4.6 let $\mathcal{Q} = \text{CBPV}$, and let $f \in \mathcal{P}(X^-, A^+)$ for a nonlinear $X$ and linear $A$, with vertex $K = A^+$. Then the hom-set $\mathcal{Q}(\pi K^\bullet, \pi \Psi)$ is empty unless $\Psi$ contains exactly one positive linear object and the rest nonlinear. Thus, $f$ is cartesian just when it exhibits $A$ as $\mathsf{F}X$ with the universal property of (3.1).

Example 4.8. Cartesian morphisms can also express adjunctions that behave similarly to $\mathsf{F} \dashv \mathsf{U}$ but stay inside the linear or nonlinear world. For instance, let SMADJ be the LNL multicategory with two objects $\mathsf{P}, \mathsf{N}$, both linear, a unique morphism $\Gamma \to \mathsf{P}$ when $\Gamma$ consists entirely of $\mathsf{P}$'s, and a unique morphism $\Gamma \to \mathsf{N}$ for any $\Gamma$. Then an object $\mathcal{P}$ of LNLPoly/SMADJ is a symmetric multicategory with a partition of its objects into "positive" and "negative" ones, such that any morphism with a negative object in its domain has a negative codomain. Suppose in addition that

- For any positive object $A$, there is a negative object $B$ and a morphism $A \to B$ that is cartesian in $B$ over the unique morphism $\mathsf{P} \to \mathsf{N}$ in SMADJ.
- For any negative object $B$, there is a positive object $A$ and a morphism $A \to B$ that is cartesian in $A$ over the unique morphism $\mathsf{P} \to \mathsf{N}$ in SMADJ.

By an argument like that of Proposition 3.1, such a $\mathcal{P}$ is uniquely determined by an adjunction of symmetric multicategories. Further cartesian liftings can specialize this to an adjunction of symmetric monoidal categories, with strong left adjoint and lax right adjoint.

Example 4.9. As an even simpler example, let ADJ have two linear objects $\mathsf{p}, \mathsf{N}$ and only one nonidentity morphism $\mathsf{P} \to \mathsf{N}$. Then an object of LNLPoly/ADJ is an ordinary category with its objects partitioned into positive and negative ones, such that there are no morphisms from a negative object to a positive one. Such a category is precisely the "collage" of a profunctor between the categories $\mathcal{P}$ and $\mathcal{N}$ of positive and negative objects. If all cartesian liftings of the morphism $\mathsf{P} \to \mathsf{N}$ exist in one direction, then the profunctor is representable by a functor $\mathcal{P} \to \mathcal{N}$; if they exist in the other direction, it is representable by a functor $\mathcal{N} \to \mathcal{P}$; and if both exist, it is representable by an adjunction $\mathcal{P} \rightleftarrows \mathcal{N}$.

As an example of the value of the entries-only framework, we can now prove (a generalization of) Proposition 2.16 without a division into 25-odd cases:

Proposition 4.10. Given $\pi : \mathcal{P} \to \mathcal{Q}$, if $f \in \mathcal{P}(\Phi_1, K)$ is $\pi$-cartesian in $K$ and $g \in \mathcal{P}(K^\bullet, \Phi_2, L)$ is $\pi$-cartesian in $L$, then their composite $g \circ_K f \in \mathcal{P}(\Phi_1, \Phi_2, L)$ is $\pi$-cartesian in $L$.

Proof. In the following diagram:

$$\begin{array}{c} \mathcal{P}(L^\bullet, \Psi) \xrightarrow{-\circ_{L}g} \mathcal{P}(K^\bullet, \Phi_2, \Psi) \xrightarrow{-\circ_K f} \mathcal{P}(\Phi_1, \Phi_2, \Psi) \\ \pi \downarrow \qquad \qquad \qquad \pi \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{Q}(\pi L^\bullet, \pi \Psi) \xrightarrow{-\circ_{(\pi L)}(\pi g)} \mathcal{Q}(\pi K^\bullet, \pi \Phi_2, \pi \Psi) \xrightarrow{-\circ_{(\pi K)}(\pi f)} \mathcal{Q}(\pi \Phi_1, \pi \Phi_2, \pi \Psi) \end{array}$$

both squares are pullbacks since $f$ and $g$ are $\pi$-cartesian, hence so is the rectangle.

□