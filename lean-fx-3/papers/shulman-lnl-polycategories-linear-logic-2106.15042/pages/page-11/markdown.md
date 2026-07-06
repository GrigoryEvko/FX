Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:11

Thus, these various kinds of homs are characterized by bijections

$$\mathcal{P}(\Theta \mid \Gamma, A; \Delta, B) \cong \mathcal{P}(\Theta \mid \Gamma; \Delta, A \multimap B)$$

$$\mathcal{P}(\Theta \mid \Gamma, B; \Delta, A) \cong \mathcal{P}(\Theta \mid \Gamma, B \triangleleft A; \Delta)$$

$$\mathcal{P}(\Theta, X; Y) \cong \mathcal{P}(\Theta; X \to Y)$$

$$\mathcal{P}(\Theta, X \mid \Gamma; \Delta, B) \cong \mathcal{P}(\Theta \mid \Gamma; \Delta, X \multimap B)$$

$$\mathcal{P}(\Theta \mid A; B) \cong \mathcal{P}(\Theta; A \multimap B)$$

$$\mathcal{P}(\Theta, X \mid ; B) \cong \mathcal{P}(\Theta; X \multimap B).$$

In particular:

- If $\otimes, \mathbb{1}, \multimap$ exist then the monoidal structure $\otimes$ on $\mathcal{P}^{\mathrm{L}}$ is closed.
- If $\mathfrak{A}, \bot, \triangleleft$ exist then the monoidal structure $\mathfrak{A}$ on $\mathcal{P}^{\mathrm{L}}$ is coclosed.
- If $\times, 1, \to$ exist then $\mathcal{P}^{\mathrm{NL}}$ is cartesian closed.

The mixed homs suggest analogous **mixed tensor products**, such as universal morphisms $\psi \in \mathcal{P}(X \mid A; \underline{X \rtimes A})$, or $\psi \in \mathcal{P}(X, Y \mid ; \underline{X \boxtimes Y})$. However, lest we start to feel the zoo of universal properties is too large, we note that the more exotic sorts can be constructed from the simpler ones in the following sense.

**Proposition 2.16.** *If $\psi$ is universal in $R$, while $\phi$ contains $R$ in its domain or codomain and is universal in a different object $S$, then $\psi \circ_R \phi$ is universal in $S$.*

*Proof.* There are a number of different versions of this statement depending on the types of $R, S, \psi, \phi$ and whether the objects occur in domain or codomain, but they all reduce to "the composite of bijections is a bijection". See Proposition 4.10 for a more rigorous proof. $\square$

One instance of this is the associativity of tensors: given universal morphisms

$$\psi_1 \in \mathcal{P}(\mid A, B; \underline{A \otimes B}) \quad \psi_3 \in \mathcal{P}(\mid A \otimes B, C; \underline{(A \otimes B) \otimes C})$$

$$\psi_2 \in \mathcal{P}(\mid B, C; \underline{B \otimes C}) \quad \psi_4 \in \mathcal{P}(\mid A, B \otimes C; \underline{A \otimes (B \otimes C)})$$

the two composites

$$\psi_3 \circ_{A \otimes B} \psi_1 \in \mathcal{P}(\mid A, B, C; \underline{(A \otimes B) \otimes C})$$

$$\psi_4 \circ_{B \otimes C} \psi_2 \in \mathcal{P}(\mid A, B, C; \underline{A \otimes (B \otimes C)})$$

are both universal, hence by Proposition 2.9 there is an induced isomorphism

$$(A \otimes B) \otimes C \cong A \otimes (B \otimes C).$$

This is how $(\otimes, \mathbb{1})$ is shown to be a monoidal structure, and similarly for $(\mathfrak{A}, \bot)$ and (if we like) $(\times, 1)$.

Another familiar instance is that in a $*$-autonomous category, linear homs can be defined in terms of duals and cotensors if these exist. Given universal morphisms

$$\psi_1 \in \mathcal{P}(\mid \underline{A^*}, A;) \quad \psi_2 \in \mathcal{P}(\mid \underline{A^* \mathfrak{A} B}; A^*, B)$$

their composite $\psi_1 \circ_{A^*} \psi_2 \in \mathcal{P}(\mid \underline{A^* \mathfrak{A} B}, A; B)$ is universal in $A^* \mathfrak{A} B$, exhibiting it as $A \multimap B$. Similarly, we have $B \triangleleft A = A^* \otimes B$, and De Morgan duality:

$$A \mathfrak{A} B = (A^* \otimes B^*)^* \quad \bot = \mathbb{1}^* \quad \nexists X = (\mathsf{F}X)^* \quad \cap A = \mathsf{U}(A^*)$$