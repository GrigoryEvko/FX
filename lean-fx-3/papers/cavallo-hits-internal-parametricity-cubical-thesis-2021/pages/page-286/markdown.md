274

Programming in cohesive parametric type theory

The second key lemma is more specific to the smash product: we must know that it commutes with the discrete embedding. From a categorical perspective, this follows from the fact that Disc is both a left and right adjoint. Because it is a left adjoint (to Glo), it commutes with colimits, here in the guise of a higher inductive type; because it is a right adjoint (to cc), it commutes with products.

Lemma 15.4.5. For any pointwise pointed types (cc | $A_*, B_* : U_*$), we have a pointed isomorphism $\wedge$-disc $\in \text{Disc}_*(A_*) \wedge_* \text{Disc}_*(B_*) \simeq \text{Disc}_*(A_* \wedge_* B_*)$ @ par.

Proof. For the forward function $F \in \text{Disc}_*(A_*) \wedge \text{Disc}_*(B_*) \to \text{Disc}(A_* \wedge B_*)$ @ par, we go by induction on the smash product input. To cover the pair case, we define a map $F_{\text{pair}} \in \text{Disc}(A) \to \text{Disc}(B) \to \text{Disc}(A_* \wedge B_*)$ @ par.

$$F_{\text{pair}} := \lambda u. \lambda v. \left[ \begin{array}{l} \text{case } u, v \text{ of} \\ | \text{mod}(a), \text{mod}(b) \mapsto \text{mod}(\langle\langle a, b \rangle\rangle) \end{array} \right]$$

Next we have $F_L \in (v : \text{Disc}(B)) \to \text{Path}(\text{Disc}(A_* \wedge B_*), \text{mod}(\mathbb{R}^L), F_{\text{pair}}(\text{mod}(a_0))v)$ @ par.

$$F_L := \lambda v. \left[ \begin{array}{l} \text{case } u, v \text{ of} \\ | \text{mod}(b) \mapsto \lambda^\sharp y. \text{mod}(\text{spoke}^L(b, y)) \end{array} \right]$$

The symmetric $F_R \in (u : \text{Disc}(A)) \to \text{Path}(\text{Disc}(A_* \wedge B_*), \text{mod}(\mathbb{R}^R), F_{\text{pair}} u (\text{mod}(b_0)))$ @ par is likewise definable. We then assemble these to construct the inverse map $F$.

$$F := \lambda s. \left[ \begin{array}{l} \text{case } s \text{ of} \\ | \langle\langle u, v \rangle\rangle \mapsto F_{\text{pair}} u v \\ | \mathbb{R}^L \mapsto \text{mod}(\mathbb{R}^L) \\ | \text{spoke}^L(b, y) \mapsto F_L b y \\ | \mathbb{R}^R \mapsto \text{mod}(\mathbb{R}^R) \\ | \text{spoke}^R(a, x) \mapsto F_R a x \end{array} \right]$$

Note that $F \langle\langle \text{mod}(a_0), \text{mod}(b_0) \rangle\rangle = \text{mod}(\langle\langle a_0, b_0 \rangle\rangle) \in \text{Disc}(A_* \wedge B_*)$, so $F$ is a pointed function.

In the reverse direction, we make use of the adjunction between Disc and Glo, defining first an auxiliary $A_*, B_* : U_* \gg G' \in A_* \wedge B_* \to \text{Glo}(\text{Disc}_*(A_*) \wedge \text{Disc}_*(B_*))$ @ pt.

$$G' := \lambda s. \left[ \begin{array}{l} \text{case } s \text{ of} \\ | \langle\langle a, b \rangle\rangle \mapsto \text{mod}(\langle\langle \text{mod}(a), \text{mod}(b) \rangle\rangle) \\ | \mathbb{R}^L \mapsto \text{mod}(\mathbb{R}^L) \\ | \text{spoke}^L(b, y) \mapsto \text{mod}(\text{spoke}^L(\text{mod}(b), y)) \\ | \mathbb{R}^R \mapsto \text{mod}(\mathbb{R}^R) \\ | \text{spoke}^R(a, x) \mapsto \text{mod}(\text{spoke}^R(\text{mod}(a), x)) \end{array} \right]$$