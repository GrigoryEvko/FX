Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:15

**Proposition 3.1.** *An LNL multicategory in which the modality F exists is uniquely determined by a functor of symmetric multicategories*

$$\mathsf{F} : \mathcal{P}^{\mathrm{NL}} \to \mathcal{P}^{\mathrm{L}}$$

*where $\mathcal{P}^{\mathrm{NL}}$ is a cartesian multicategory and $\mathcal{P}^{\mathrm{L}}$ a symmetric one. Moreover:*

- (i) *The modality U also exists if and only if the functor F has a right adjoint (in the 2-category of symmetric multicategories).*
- (ii) *If $\times, 1, \otimes, \mathbb{1}$ exist, then F is equivalently a strong symmetric monoidal functor from a cartesian monoidal category to a symmetric monoidal one.*
- (iii) *Thus, an LNL multicategory with $\times, 1, \otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$ is equivalently an **LNL adjunction** [Ben95, Mel09]: a symmetric monoidal adjunction from a cartesian monoidal category to a symmetric monoidal one.*

*Proof.* Given the modality $\mathsf{F}$, we make it a functor by composing with $(Y \mid) \to \mathsf{F}Y$ and applying its universal property:

$$\mathcal{P}(X_1, \dots, X_n; Y) \to \mathcal{P}(X_1, \dots, X_n \mid ; \mathsf{F}Y) \xrightarrow{\sim} \mathcal{P}(\mid \mathsf{F}X_1, \dots, \mathsf{F}X_n; \mathsf{F}Y).$$

Conversely, given a functor $\mathsf{F}$, we define the general linear hom-sets by

$$\mathcal{P}(X_1, \dots, X_n \mid \Gamma; B) = \mathcal{P}^{\mathrm{L}}(\mathsf{F}X_1, \dots, \mathsf{F}X_n, \Gamma; B).$$

Thus, the universal property of $\mathsf{F}$ holds by definition. Statement (i) is then a multicategorical version of the standard equivalence between adjunctions defined with bijections of hom-sets and with unit and counit. We have already noted (ii), and (iii) follows immediately. $\square$

**Remark 3.2.** Benton [Ben95] assumed $\mathcal{P}^{\mathrm{NL}}$ cartesian *closed* and $\mathcal{P}^{\mathrm{L}}$ symmetric monoidal *closed*, but later authors such as [Mel09] have observed that this is unnecessary for the bare definition. If both categories are closed we will speak of a **closed LNL adjunction**.

Since left adjoints preserve colimits and right adjoints preserve limits, the following structures also form locally full sub-2-categories of LNLPoly:

- LNL adjunctions.
- LNL adjunctions with any desired limits and colimits in either category, such that colimits are preserved by the product or tensor product in each variable.
- Closed LNL adjunctions, with any desired limits and colimits in either category.

The notion of LNL adjunction does depend on having both $\otimes$ and $\times$, whereas LNL multicategories can specify the correct behavior of $\mathsf{F}$ and $\mathsf{U}$ even if $\otimes, \times$ may not exist. As evidence for this correctness, we note that $\times, 1$ are not necessary for the induced comonad on $\mathcal{P}^{\mathrm{L}}$ to coincide with a structure also existing in the literature.

**Proposition 3.3.** *If $\mathcal{P}$ is an LNL multicategory with $\otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$, the symmetric monoidal category $\mathcal{P}^{\mathrm{L}}$ admits a **linear exponential comonad** [BBdPH92, HS03], i.e. it is a **linear category** in the sense of [Ben95].*

*Proof.* Let $!$ be the comonad $\mathsf{FU}$. To give the map $!A \otimes !B \to !(A \otimes B)$, we act on the $\otimes$-universal morphism $(\mid A, B) \to A \otimes B$ as follows. The two noninvertible maps are composition with the U-universal morphisms $(\mathsf{U}A \mid) \to A$ and $(\mathsf{U}B \mid) \to B$ and with the