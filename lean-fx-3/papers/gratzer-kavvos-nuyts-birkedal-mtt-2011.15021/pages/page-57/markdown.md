Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:57

The closest we can get to defining internal transposition (without using an initial modality) amounts to the following two functions.

$$\mathbf{transp}_{\nu \to \mu}^{\rightarrow} : \langle \mu \mid \langle \nu \mid A^{\eta} \rangle \rightarrow B \rangle \rightarrow A \rightarrow \langle \mu \mid B \rangle$$

$$\mathbf{transp}_{\nu \to \mu}^{\rightarrow} \triangleq \lambda f. \ \lambda x. \ f \circledast_{\mu} \mathbf{unit}(x)$$

$$\mathbf{transp}_{\nu \to \mu}^{\leftarrow} : \langle \nu \mid A \rightarrow \langle \mu \mid B \rangle \rangle \rightarrow \langle \nu \mid A \rangle \rightarrow B^{\epsilon}$$

$$\mathbf{transp}_{\nu \to \mu}^{\leftarrow} \triangleq \lambda f. \ \lambda x. \ \mathbf{counit}(f \circledast_{\nu} x)$$

The first is an equivalence (again up to function extensionality), but neither have the expected type. The first transposition $\mathbf{transp}_{\nu \to \mu}^{\rightarrow}$ is not without precedent: it is the internal formulation of transposition for adjunctions between monoidal closed categories when the left adjoint preserves monoidal products.

10.5. Crisp induction. Having internalized the definition of an adjunction, it is natural to ask whether standard facts about adjoint functors carry over. In this section we prove an internal version of the fact that left adjoints preserve colimits. Within type theory this result takes the form of crisp induction principles for various types that arise from colimits.

As a first approximation to the notion of crisp induction, recall the rule for modal induction, i.e. the elimination rule for modal types from Section 2:

$$\begin{array}{c} \mu : n \rightarrow m \qquad \nu : m \rightarrow o \qquad \Gamma, x : (\nu \mid \langle \mu \mid A \rangle) \vdash B \ \mathbf{type}_1 \circledast o \\ \Gamma, \widehat{\bullet}_{\nu} \vdash M_0 : \langle \mu \mid A \rangle \circledast m \qquad \Gamma, x : (\nu \circ \mu \mid A) \vdash M_1 : B[\mathbf{mod}_{\mu}(x)/x] \circledast o \\ \hline \Gamma \vdash \mathbf{let}_{\nu} \ \mathbf{mod}_{\mu}(x) \leftarrow M_0 \ \mathbf{in} \ M_1 : B[M_0/x] \circledast o \end{array}$$

Notice that there is an “extra” modality parameterizing this rule, $\nu$, which modifies $M_0$ as well as the data supplied to $M_1$. This extra generality is not frivolous: we can only define the equivalence $\mathbf{comp}_{\mu,\nu}$ of Section 3 because we can eliminate one modality ‘under’ another.

One might hope for a similar level of flexibility in all positive eliminators. However, the elimination rule for booleans—stated here in its algebraic form of Section 4—does not allow it:

$$\begin{array}{c} \Gamma \ \mathbf{ctx} \circledast m \qquad \Gamma.(1 \mid \mathbb{B}) \vdash A \ \mathbf{type}_1 \circledast m \\ \Gamma \vdash M_t : A[\mathbf{id.tt}] \circledast m \qquad \Gamma \vdash M_f : A[\mathbf{id.ff}] \circledast m \qquad \Gamma.\widehat{\bullet}_1 \vdash N : \mathbb{B} \circledast m \\ \hline \Gamma \vdash \mathbf{if}(A; M_t; M_f; N) : A[\mathbf{id.N}] \circledast m \end{array}$$

Were we to replace 1 with an arbitrary modality, then this rule would state something considerably stronger: not only would we have the expected elimination principle for $\mathbb{B}$, but all of our modalities would preserve $\mathbb{B}$. Semantically, this is nonsense: modalities intuitively correspond to right adjoints, and therefore do not necessarily preserve colimits. For example, the later $\blacktriangleright$ modality of Section 9 does not preserve booleans.

Yet, in some circumstances—e.g. when a modality is a left adjoint—the stronger rule is valid. This is the idea behind Shulman’s crisp induction principles [Shu18, §5]: cohesive type theory enables the proof of elimination principles for the coproducts and the identity type under the left adjoint in the adjunction $\flat \dashv \sharp$. We will demonstrate that similar principles are derivable within MTT with mode theory $\mathcal{M}_{\mathrm{adj}}$.

Fix a motive $\Gamma, \widehat{\bullet}_{\nu \circ \mu}, b : (\nu \mid \mathbb{B}) \vdash C \ \mathbf{type}_1 \circledast n$. Crisp induction is given by a term

$$\Gamma \vdash \mathbf{crisp\_if}_C : (b : (\nu \mid \mathbb{B})) \rightarrow \langle \nu \circ \mu \mid C(\mathbf{tt}) \rangle \rightarrow \langle \nu \circ \mu \mid C(\mathbf{ff}) \rangle \rightarrow C^{\epsilon}(b) \circledast n$$

This is a well-formed type, as $\Gamma, b : (\nu \mid \mathbb{B}) = \Gamma, \widehat{\bullet}_1, b : (\nu \mid \mathbb{B}) \vdash C^{\epsilon} \ \mathbf{type}_1 \circledast m$.