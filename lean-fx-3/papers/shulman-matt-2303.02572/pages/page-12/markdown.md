18–12

Semantics of multimodal adjoint type theory

Proof. Suppose we have \(\mu : q \to r\) in \(\mathcal{L}\) and \(\nu : q \to p\) in \(\mathcal{S}\), and also \(\Gamma \in \widehat{\mathcal{C}}_r\) and \(A \in \widehat{\mathrm{Ty}}_p^! (\widehat{\mathcal{C}}_\nu \widehat{\mathcal{C}}^\mu \Gamma) = \mathrm{Ty}_p(\mathsf{L}^p \widehat{\mathcal{C}}_\nu \widehat{\mathcal{C}}^\mu \Gamma)\) with \(B \in \widehat{\mathrm{Ty}}_r^! (\Gamma \triangleright^{\mu \circ \nu^\dagger} A) = \mathrm{Ty}_r(\mathsf{L}^r (\Gamma \triangleright^{\mu \circ \nu^\dagger} A))\). Applying \(\mathsf{L}^r\) to the defining pullback (5.6) of \(\Gamma \triangleright^{\mu \circ \nu^\dagger} A\), and using pseudonaturality and the fact that \(\mathsf{L}^q \mathsf{R}_q \cong 1\), we have a pullback

\[
\begin{array}{c} \mathsf {L} ^ {r} (\Gamma \triangleright^ {\mu \circ \nu^ {\dagger}} A) \longrightarrow \mathscr {C} _ {\mu} \mathscr {C} _ {\nu^ {\dagger}} (\mathsf {V} _ {A} \triangleright \mathsf {E} _ {A}) \\ \mathsf {L} ^ {r} (\widehat {\mathfrak {p}} _ {A}) \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \end{array} \tag {5.13}
\]

Thus, Definition 5.10 says \(\mathsf{L}^r (\widehat{\mathfrak{p}}_A)\) is type-exponentiable, hence the pushforward of \(B\) along it is a type projection; it remains to construct a local universe making it strictly stable. Let \(\mathsf{V}_{\Pi (A,B)}\) be the universal object with maps \(\pi_A:\mathsf{V}_{\Pi (A,B)}\to \mathcal{C}_\omega (\mathsf{V}_A)\) and \(\pi_B:\pi_A^* (\mathcal{C}_\omega (\mathsf{V}_A\triangleright \mathsf{E}_A))\to \mathsf{V}_B\). By Definition 5.10, \(\pi_A^* (\mathcal{C}_\omega (\mathsf{p}_{\mathsf{E}_A}))\) is type-exponentiable, so the pushforward of \(\mathsf{E}_B[\pi_B]\in \mathrm{Ty}_q(\pi_A^* (\mathcal{C}_\omega (\mathsf{V}_A\triangleright \mathsf{E}_A)))\) along it is represented by a type \(\mathsf{E}_{\Pi (A,B)}\in \mathrm{Ty}_q(\mathsf{V}_{\Pi (A,B)})\). Now the bottom map in (5.13) and \(B':\mathsf{L}^q (\Gamma \triangleright^\omega A)\to \mathsf{V}_B\) induce a map \(\Pi (A,B):\mathsf{L}^q\Gamma \to \mathsf{V}_{\Pi (A,B)}\). Together, these data define \(\Pi (A,B)\in \widehat{\mathrm{Ty}}_p^!\) (\(\Gamma\)), such that \(\mathsf{L}^p\Gamma \triangleright \mathsf{E}_{\Pi (A,B)}[\Pi (A,B)]\) is a pushforward of \(\mathsf{L}^q (\Gamma \triangleright^\omega A)\triangleright \mathsf{E}_B[\Pi ']\) along \(\mathsf{L}^q (\Gamma \triangleright^\omega A)\to \mathsf{L}^q\Gamma\). The comprehension \(\Gamma \triangleright \Pi (A,B)\) in \(\widehat{\mathcal{C}}_q\) is defined by applying \(\mathsf{R}_q\) to this and pulling back along the unit \(\Gamma \to \mathsf{R}_q\mathsf{L}^q\Gamma\). Thus, Lemma 5.11 implies the desired universal property of \(\Pi (A,B)\).

### 5.4 Positive modalities

Definition 5.14 In a natural pseudo-model, a map \( f: \Gamma \to \Delta \) is anodyne if for any \( B \in \mathrm{Ty}(\Delta) \) and any \( g: \Gamma \to \Delta \triangleright B \) lifting \( f \), there exists a diagonal filler:

\[
\begin{array}{c} \Gamma \xrightarrow {g} \Delta \triangleright B \\ f \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \end{array}
\]

A map is stably anodyne if any pullback of it is anodyne.

Definition 5.15 A modal pre-model \(\mathcal{C}\) has positive pre-modalities if for any sharp \(\mu : p \to q\) and \(\Gamma \in \mathcal{C}_p\) with \(A \in \mathrm{Ty}_p(\Gamma)\), there exists \(\mu \square A \in \mathrm{Ty}_q(\mathcal{C}_\mu \Gamma)\) and a map \(i_{\Gamma, A}^\mu : \mathcal{C}_\mu (\Gamma \triangleright A) \to \mathcal{C}_\mu \Gamma \triangleright (\mu \square A)\) over \(\mathcal{C}_\mu \Gamma\). such that for any transparent \(\varrho : q \to r\), the map \(\mathcal{C}_{\varrho}(i_{\Delta, A}^\mu)\) is stably anodyne.

Lemma 5.16 In an adjoint modal pre-model, let \(\theta : \Gamma \to \Delta\) be a map in \(\widehat{\mathcal{C}}_p\). If \(\mathsf{L}^p\theta\) is anodyne in \(\mathcal{C}_p\), then \(\theta\) is anodyne in \(\widehat{\mathcal{C}}_p\).

Proof. Suppose given \( B \in \widehat{\mathrm{Ty}}_p^!(\Delta) = \mathrm{Ty}_p^!(\mathsf{L}^p\Delta) \), and a commutative square as at left below.

\[
\begin{array}{c} \Gamma \longrightarrow \Delta \triangleright B \longrightarrow R _ {p} (V _ {B} \triangleright E _ {B}) \\ \theta \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \Delta \xlongequal {} \Delta \xrightarrow {r _ {B ^ {\prime}}} R _ {p} V _ {B} \end{array}
\]

\[
\begin{array}{c} \mathsf {L} ^ {p} \Gamma \longrightarrow \mathsf {V} _ {B} \triangleright \mathsf {E} _ {B} \\ \mathsf {L} ^ {p} \theta \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \mathsf {L} ^ {p} \Delta \xrightarrow {r _ {B ^ {\prime}}} \mathsf {V} _ {B} \end{array}
\]

It suffices to find a filler for the outer rectangle at left above; and by adjunction, this is equivalent to finding a filler in the square at right above. But such a filler exists precisely because  \( L^{p}\theta \)  is anodyne. ☐