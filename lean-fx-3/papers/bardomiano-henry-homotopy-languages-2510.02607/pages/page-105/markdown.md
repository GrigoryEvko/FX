Then theorem A.28 implies that the compositions as given is well-defined. Finally, in order to get the correct morphisms, we need to know that the equivalence relation on interpretations is compatible with the composition. Another advantageous consequence is that this it gives us criteria to establish whether two interpretations are equivalent.

**Corollary A.29.** *If $I$ and $J$ are interpretations from $T$ to $T'$ then $I \approx J$ if and only if for any type element judgment $r$, $\widehat{I}(r) \approx \widehat{J}(r)$.*

*Proof.* This follows from theorem A.28 and (3) of theorem A.3. $\square$

**Corollary A.30.** *If $I$ and $J$ are interpretations from $T$ to $T'$ and $I'$ and $J'$ are interpretations from $T'$ to $T''$ then from $I \approx J$ and $I' \approx J'$ we conclude that $I' \circ I \approx J' \circ J$.*

*Proof.* [Car78, pp. 1.72]. $\square$

The category $\kappa$-GAT has morphisms equivalence classes of interpretations [Car78, pp. 1.72].

### A.5 Construction and properties of the syntactic category $\mathbb{C}_T$

Let $T$ be a generalized $\kappa$-algebraic theory. The category $\mathbb{C}_T$ has the following data:

- Objects: Equivalence classes of contexts under the relation $\approx$. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context then the object in $\mathbb{C}_T$ is denoted $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$.
- Morphisms: A morphism between $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$ and $[\{x_\beta : \Omega_\mu\}_{\beta < \mu}]$ is the equivalence class of a map

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$$

induced by the relation $\approx$. We denote this set by

$$\hom_{\mathbb{C}_T}([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}], [\{x_\beta : \Omega_\mu\}_{\beta < \mu}]).$$

- Composition: This is induced by the composition of maps between contexts. This is again well-defined in view of 2 of theorem A.21.
- Identity: For a context $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ its identity is the equivalence class of the obvious map $\langle x_\alpha \rangle_{\alpha < \lambda}$.

105