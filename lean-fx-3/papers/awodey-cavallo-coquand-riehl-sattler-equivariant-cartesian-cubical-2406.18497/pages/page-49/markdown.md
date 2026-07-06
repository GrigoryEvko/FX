In particular, a map \( f \colon \mathbb{Y} \to \mathbb{X} \) of cubical species is a fibration if and only if it is an unbiased fibration, i.e., the parametrized path space map

\[
\mathbb {Y} ^ {\mathrm{I}} \times \mathbb {I} \xrightarrow {\operatorname{ev} \hat {\circ} f} \mathbb {P} ^ {\mathrm{I}} \mathbb {Y}
\]

is a trivial fibration.

Proof. The category of uniform fibrations is defined by right lifting against the category of arrows \( J \colon \int \Omega \times \mathbb{I} \to (\mathsf{cSet}^{\mathbb{I}})^2 \) defined in Construction 4.3.6. In terms of the functor \( I \colon \int \Omega \to (\mathsf{cSet}^{\mathbb{I}})^2 \) of Construction 2.2.13, the functor \( J \) is the top horizontal composite:

\[
\begin{array}{c} \int \Omega \times \mathbb {I} \xrightarrow {\Sigma^ {*} I} (\mathsf {c S e t} _ {/ \mathbb {I}} ^ {\mathbb {I}}) ^ {2} \xrightarrow {- \hat {\times} \delta} (\mathsf {c S e t} _ {/ \mathbb {I}} ^ {\mathbb {I}}) ^ {2} \xrightarrow {\Sigma} (\mathsf {c S e t} ^ {\mathbb {I}}) ^ {2} \\ \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \int \Omega \xrightarrow [ I ]{} (\mathsf {c S e t} ^ {\mathbb {I}}) ^ {2} \end{array}
\]

Thus, by adjunction, \( f \in (\mathsf{cSet}^{\mathbb{I}})^2 \) is a uniform fibration if and only if \( \{\widehat{\delta, f \times \mathbb{I}}\}_{\mathbb{I}} \in (\mathsf{cSet}_{/ \mathbb{I}}^{\mathbb{I}})^2 \) lifts on the right against the category \( \Sigma^{*}I \colon \int \Omega \times \mathbb{I} \to (\mathsf{cSet}_{/ \mathbb{I}}^{\mathbb{I}})^2 \). As solutions to lifting problems in slice categories are created by the forgetful functor, this is the case if and only if \( \operatorname{ev} \hat{\circ} f \cong \Sigma \{\widehat{\delta, f \times \mathbb{I}}\}_{\mathbb{I}} \in (\mathsf{cSet}^{\mathbb{I}})^2 \) is a uniform trivial fibration as claimed.

The left maps of an algebraic weak factorization system satisfy additional closure properties, arising from the fact that comonadic functors create colimits [BG16]. In particular, colimits in the arrow category, of diagrams that factor through the generating category, are trivial cofibrations. The following lemma provides an example of this paradigm.

Lemma 4.3.15. For any of the \(2^{\omega}\) points \(\vec{\epsilon}\) of \(\mathbb{I}\), the map \(\vec{\epsilon} \colon \mathbb{1} \to \mathbb{I}\), is a trivial cofibration.

Proof. For any vertex \(\vec{v} \in I^k\) we have a triangle

\[
\begin{array}{c c c c c} \emptyset \xrightarrow {\quad ! \quad} 1 & \\ I ^ {k} & \sim & \mathbb {F} _ {k} 1 & \\ & \Biggl \downarrow [ \vec {v} ] & \leftrightarrow & \Biggl \downarrow_ {\mathbb {P} ^ {\Sigma_ {k}}} \\ & & \mathbb {F} _ {k} 1 \times \mathbb {I} & \\ & & & \Sigma_ {k} \times I ^ {k} \end{array} \tag {4.3.16}
\]

The map of \(\Sigma_{k}\)-cubical sets on the right sends \(\sigma \in \Sigma_{k}\) to the pair \((\sigma, \sigma \cdot \vec{v})\). However, recall from Remark 4.2.6 that a point of \(\mathbb{I}\) is specified by choosing either point \(\vec{0} \colon 1 \to I^{k}\) or \(\vec{1} \colon 1 \to I^{k}\) for each component. Note these are the only two points in the \(\Sigma_{k}\)-cubical set \(I^{k}\), since the other points in the underlying cubical set are permuted by the regular action. By contrast, since these points are fixed we have automorphisms

\[
\begin{array}{c c c} \emptyset & \text {   =   } & \emptyset \\ ! \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} \\ 1 & \text {   =   } & 1 \\ \vec {0} \Big \downarrow & \Big \downarrow^ {\vec {0}} & \\ I ^ {k} & \xleftarrow {\sigma} & I ^ {k} \end{array} \qquad \qquad \begin{array}{c c c} \emptyset & \text {   =   } & \emptyset \\ ! \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} \\ 1 & \text {   =   } & 1 \\ \vec {1} \Big \downarrow & \Big \downarrow^ {\vec {1}} & \\ I ^ {k} & \xleftarrow {\sigma} & I ^ {k} \end{array}
\]

for each \(\sigma \in \Sigma_k\). Thus \(\Sigma_k^{\mathrm{op}}\) acts on the open boxes \([\vec{0}] \colon \mathbb{F}_k 1 \mapsto \mathbb{F}_k 1 \times \mathbb{I}\) and \([\vec{1}] \colon \mathbb{F}_k 1 \mapsto \mathbb{F}_k 1 \times \mathbb{I}\) and these automorphisms lie in the generating category. The colimits yield the maps \(\vec{0} \colon 1 \to I^k\) and \(\vec{1} \colon 1 \to I^k\) in \(\Sigma_k\)-cubical sets, where the codomains have the regular action. Thus, these maps are

49