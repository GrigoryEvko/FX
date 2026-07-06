27:14

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

Unlike dependent sums or products, modal types do not have a universal property—an $\eta$ law—so they cannot be encoded by a single pullback. Instead we must describe the elimination principle separately. Following Gratzer et al. [GKNB21], we encode the elimination principle as an internal lifting structure.

**Definition 3.3** Definition 18 [Awo18]. An internal lifting structure $s : i \pitchfork \tau$ between a pair of morphisms $i : A \longrightarrow B$ and $\tau : X \longrightarrow Y$ is a section of canonical map $X^B \longrightarrow Y^B \times_{Y^A} X^A$.

Fix a pair of modalities $\mu : n \longrightarrow m$ and $\nu : o \longrightarrow n$ and write $c$ for the comparison map $F(\nu)^*(\mathcal{T}_o^\bullet) \longrightarrow F(\nu)^*(\mathcal{T}_o) \times_{\mathcal{T}_n} \mathcal{T}_n^\bullet$ induced by Diagram 3.3. The elimination principle for $\nu$-modal types with a framing modality $\mu$ is encoded by a lifting structure of the following type:

$$F(\mu)^*(c) \pitchfork F(\mu \circ \nu)^*(\mathcal{T}_o) \times \tau_m : \mathbf{PSh}(F(o))/F(\mu \circ \nu)^*(\mathcal{T}_o)$$

This definition is somewhat obstruse, but we will soon be in a position to formulate a far more intuitive version of it by taking advantage of a richer version of the internal language in Section 3.3.

As models of a particular GAT, models of MTT assemble into a category. A morphism between models $F$ and $G$ is given by a 2-natural transformation $F \longrightarrow G$ along with natural assignments of terms and types of $F$ to the terms and types of $G$. All of these operations are required to strictly preserve term, type, and context formers. We refer the reader to Gratzer et al. [GKNB21] for a precise description.

Finally, a standard result of GATs is that the *syntactic model* occupies a distinguished place in the category of models:

**Theorem 3.4.** *Syntax is the initial model of MTT.*

**3.2. MTT cosmoi.** As mentioned in Section 1, normalization is proven through the construction of a model of MTT together with a map from this model to syntax. Models of MTT and morphisms between them are difficult to construct, however, because of the extreme strictness of morphisms and the requirement that each $\tau_m$ be a representable natural transformation. Prior to normalization, therefore, we introduce a weakened notion of model: an MTT cosmos. An MTT cosmos is an axiomatization of a natural model of MTT, but rather than working in presheaf topoi and requiring that $\tau_m$ is a representable natural transformation a cosmos requires only that $\tau_m$ be a morphism in a locally cartesian closed category equipped with structure such as Diagrams 3.2 and 3.3.

**Definition 3.5.** A *cosmos* is a pseudofunctor $F : \mathcal{M} \longrightarrow \mathbf{Cat}$ such that each $F(m)$ is a locally cartesian closed category and each $F(\mu)$ has a left adjoint $F_!(\mu) \dashv F(\mu)$.

One should imagine a cosmos $F$ as arising from some model of MTT $F_0$ with $F(m) = \mathbf{PSh}(F_0(m))$. The adjunction $F(\mu)_! \dashv F(\mu)$ is then recording the adjunction given by precomposition and left Kan extension $F_0(\mu)_! \dashv F_0(\mu)^*$. In particular, the left adjoint to $F(\mu)$ allows us to capture the left adjoint action of a modality on contexts $(-\{\mu\})$ while $F(\mu)$ is more intended to record the modality itself. While this example is strictly 2-functorial, we allow a general cosmos to be pseudofunctorial. The formal connection between models and cosmoi is given by the following example:

**Example 3.6.** A model of MTT $F$ assembles into a cosmos $G$ by taking $G(m) = \mathbf{PSh}(F(m))$ and $G(\mu) = F(\mu)^*$. In particular, we write $\mathcal{S} : \mathcal{M} \longrightarrow \mathbf{Cat}$ for the cosmos induced by the initial model of MTT specified by Theorem 3.4.