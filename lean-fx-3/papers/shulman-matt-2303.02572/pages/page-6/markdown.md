18-6

Semantics of multimodal adjoint type theory

is, say, locally finite (this is true for for 1-categories [6]).

## 3 Natural models of MATT

We now generalize the modal natural models of [12] to MATT. We first recall some definitions.

- A natural model [2] is a representable morphism \(\tau : \mathrm{Tm} \to \mathrm{Ty}\) in a presheaf category \(\mathcal{P}\mathcal{D}\). Thus for any \(A \in \mathrm{Ty}(\Gamma)\) we have an object \(\Gamma \triangleright A \in \mathcal{D}\), a morphism \(\mathfrak{p}_A : \Gamma \triangleright A \to \Gamma\), and a pullback square

\[
\begin{array}{c} \mathfrak {L} (\Gamma \triangleright A) \longrightarrow \mathrm{Tm} \\ \mathfrak {p} _ {A} \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \\ \mathfrak {L} (\Gamma) \xrightarrow [ A ]{} \mathrm{Ty} \end{array} \tag {3.1}
\]

where \(\mathfrak{L}:\mathcal{D}\to \mathcal{P}\mathcal{D}\) denotes the Yoneda embedding. A natural model is equivalent to a category with families. We refer to \(\Gamma \triangleright A\) as the comprehension of \(A\), and \(\mathfrak{p}_A\) as its type projection.

- A modal context structure [12, Definition 5.1] is a 2-functor \(\mathcal{D}:\mathcal{M}^{\mathrm{coop}}\to \mathcal{C}at\) such that each \(\mathcal{D}_p\) has a terminal object. We write its action on morphisms and 2-cells as \(\mathcal{D}^{\mu}\) and \(\mathcal{D}^{\alpha}\) respectively.
- A modal natural model [12, Definition 5.4] is a modal context structure \(\mathcal{D}\) with a morphism \(\tau_p: \mathrm{Tm}_p \to \mathrm{Ty}_p\) in each presheaf category \(\mathcal{P}\mathcal{D}_p\), such that for any \(\mu: p \to q\) in \(\mathcal{M}\), the transformation \((\mathcal{D}^\mu)^*\tau_p\) is representable in \(\mathcal{P}\mathcal{D}_q\). (Taking \(\mu = 1_p\), this implies that each \(\mathcal{D}_p\) is a natural model.) We write the comprehension of \(A \in \tau_p(\mathcal{D}^\mu(\Gamma))\) as \(\mathfrak{p}_A^\mu: \Gamma \triangleright^\mu A \to \Gamma\), and write \(\Gamma \triangleright^1 A\) as \(\Gamma \triangleright A\).

Definition 3.2 Let \(\mathcal{M}\) be an adjoint mode theory. A modal context structure \(\mathcal{D}:\mathcal{M}^{\mathrm{coop}}\to \mathcal{C}at\) is an adjoint modal natural model if we have a morphism \(\tau_p:\mathrm{Tm}_p\to \mathrm{Ty}_p\) in each \(\mathcal{P}\mathcal{D}_p\) such that \((\mathcal{D}^{\mu})^{*}\tau_{p}\) is representable for all tangible \(\mu\). (Since identities are tangible, each \(\mathcal{D}_p\) is still a natural model.)

Definition 3.3 (See [12, §5.2.1]) A \(\Pi\)-structure on an adjoint modal natural model \(\mathcal{D}\) consists of, for any sharp \(\mu : p \to q\), and any \(\Gamma \in \mathcal{D}_q\) and \(A \in \mathrm{Ty}_p(\mathcal{D}^\mu(\Gamma))\) with \(B \in \mathrm{Ty}_q(\Gamma \triangleright^\mu A)\), a type \(\Pi(A, B) \in \mathrm{Ty}_q(\Gamma)\) such that \(\Gamma \triangleright \Pi(A, B)\) is a pushforward of \(\Gamma \triangleright^\mu A \triangleright B\) along \(\mathfrak{p}_A : \Gamma \triangleright^\mu A \to A\), all natural in \(\Gamma\).

Definition 3.4 (See [12, §5.2.2]) An adjoint modal natural model \(\mathcal{D}\) has positive modalities if for any sharp \(\mu : p \to q\) we have:

(i) For any \(\Gamma \in \mathcal{D}_q\) and \(A \in \mathrm{Ty}_p(\mathcal{D}^\mu(\Gamma))\), we have a type \(\mu \boxdot A \in \mathrm{Ty}_q(\Gamma)\) and a map \(j_{\Gamma, A}^\mu : \Gamma \triangleright^\mu A \to \Gamma \triangleright (\mu \boxdot A)\) over \(\Gamma\), all varying naturally in \(\Gamma\).
(ii) For any transparent \(\varrho: q \to r\) and \(\Gamma \in \mathcal{D}_r\) with \(A \in \mathrm{Ty}_p(\mathcal{D}^{\varrho \circ \mu}(\Gamma))\), define the dashed map \(\ell\) below by the universal property of pullbacks and full-faithfulness of \(\mathfrak{L}\):

\[
\begin{array}{c c} \mathfrak {L} (\Gamma \triangleright^ {\varrho \circ \mu} A) \xrightarrow {\mathfrak {L} (\ell)} \mathfrak {L} (\Gamma \triangleright^ {\varrho} (\mu \boxdot A)) \longrightarrow (\mathcal {D} ^ {\varrho}) ^ {*} \mathrm{Tm} _ {q} & = \\ \Big \downarrow & \Big \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \\ \mathfrak {L} (\Gamma) \xlongequal {} \mathfrak {L} (\Gamma) \xrightarrow [ \mu \boxdot A ]{\text {   }} (\mathcal {D} ^ {\varrho}) ^ {*} \mathrm{Ty} _ {q} & = \\ & \Big \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \end{array}
\]

Then for any commutative square as below there is a chosen diagonal filler, natural in \(\Gamma\):

\[
\begin{array}{c} \Gamma \triangleright^ {\varrho \circ \mu} A \longrightarrow \Gamma \triangleright^ {\varrho} (\mu \boxdot A) \triangleright B \\ \ell \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Gamma \triangleright^ {\varrho} (\mu \boxdot A) = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = \\ \end{array}
\]

Definition 3.5 (See [11, Definition 4]) An adjoint modal natural model \(\mathcal{D}\) has negative modalities if