isomorphism in A restricts in the obvious way to a natural isomorphism between the boundaries of the corresponding representable functors, which thus assemble into profunctors

\[
\overleftarrow {\partial} \mathsf {A} _ {n} \hookrightarrow \mathsf {A} _ {n} \in \operatorname{Set} ^ {\mathsf {G} (n) ^ {\mathrm{op}} \times \mathsf {A}} \quad \text { and } \quad \overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} ^ {n} \in \operatorname{Set} ^ {\mathsf {A} ^ {\mathrm{op}} \times \mathsf {G} (n)}.
\]

When we compose these profunctors over  \( \mathsf{G}(n) \) , we obtain a profunctor from A to A which is the “generalized cell” attached to form  \( sk_{n}A \)  from  \( sk_{n-1}A \)  [Rie, §4]:

Theorem 6.2.5. The inclusion \(\emptyset \hookrightarrow A\) has a canonical presentation as a generalized cell complex:

\[
\begin{array}{c} \overleftarrow {\partial} \mathsf {A} _ {n} \underline {{\times}} _ {\mathsf {G} (n)} \mathsf {A} ^ {n} \cup \mathsf {A} _ {n} \underline {{\times}} _ {\mathsf {G} (n)} \overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} _ {n} \underline {{\times}} _ {\mathsf {G} (n)} \mathsf {A} ^ {n} \\ \circ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \emptyset \hookrightarrow \operatorname{sk} _ {0} \mathsf {A} \dots\dots\partial_ {\mathrm{sk} _ {n - 1}} \mathsf {A} \xleftarrow {} \operatorname{sk} _ {n} \mathsf {A} \dots\dots\partial_ {\mathrm{colim} _ {n}} \operatorname{sk} _ {n} \mathsf {A} \cong \mathsf {A}, \end{array}
\]

i.e., a composite of pushouts of cells constructed as coends of exterior Leibniz products

\[
(\overleftarrow {\partial} \mathsf {A} _ {n} \hookrightarrow \mathsf {A} _ {n}) \underline {{\times}} _ {\mathsf {G} (n)} (\overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} ^ {n}) := \int^ {a \in \mathsf {G} (n)} (\overleftarrow {\partial} \mathsf {A} _ {a} \hookrightarrow \mathsf {A} _ {a}) \underline {{\times}} (\overrightarrow {\partial} \mathsf {A} ^ {a} \hookrightarrow \mathsf {A} ^ {a}),
\]

attached at stage n.

As a corollary of Theorem 6.2.5, any natural transformation \( f \colon X \to Y \in \mathsf{E}^{\mathsf{A}^{\mathrm{op}}} \) valued in a cocomplete category \( \mathsf{E} \) admits a canonical presentation as a generalized cell complex, obtained by applying the Leibniz construction to the weighted colimit bifunctor \( *_{\mathsf{A}} \colon \mathsf{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}} \times \mathsf{E}^{\mathsf{A}^{\mathrm{op}}} \to \mathsf{E}^{\mathsf{A}^{\mathrm{op}}} \).

Corollary 6.2.6. Let A be a Reedy category and let E be bicomplete. Any morphism  \( f: X \to Y \in E^{A^{op}} \)  is a generalized cell complex

\[
X \to X \cup_ {\mathrm{sk} _ {0} X} \mathrm{sk} _ {0} Y \to \dots \to X \cup_ {\mathrm{sk} _ {n - 1} X} \mathrm{sk} _ {n - 1} Y \to X \cup_ {\mathrm{sk} _ {n} X} \mathrm{sk} _ {n} Y \to \dots \to \operatorname{colim} \cong Y
\]

with the generalized cell

\[
(\overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} ^ {n}) \stackrel {*} {\ast_ {\mathsf {G} (n)}} \widehat {\ell_ {n}} f \tag {6.2.7}
\]

attached at stage n.

Here \(\widehat{\ell}_n f \in \mathsf{E}^{\mathsf{G}(n)^{\mathrm{op}}}\) is the diagram formed by the Leibniz weighted colimit of \(f\) and \(\overleftarrow{\partial}\mathsf{A}_n \hookrightarrow \mathsf{A}_n\). Its component at \(a \in \mathsf{A}\) of degree \(n\) is the relative latching map, the Leibniz weighted colimit defined by the pushout of the map \(L_a f := \overleftarrow{\partial}\mathsf{A}_a *_{\mathsf{A}} f\):

\[
\widehat {\ell} _ {a} f := (\overleftarrow {\partial} \mathsf {A} _ {a} \hookrightarrow \mathsf {A} _ {a}) \stackrel {*} {\ast} _ {\mathsf {A}} f \qquad \qquad \begin{array}{c} L _ {a} X \xrightarrow {L _ {a} f} L _ {a} Y \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X _ {a} \xrightarrow {} \ell_ {a} f \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ f _ {a} \end{array}
\]

We now specialize to the case E = Set and impose the Eilenberg–Zilber hypothesis on A. Let X be a presheaf on an Eilenberg–Zilber category A. An element  \( x \in X_{a} \)  is degenerate if there exists a non-invertible split epimorphism  \( \pi: a \twoheadrightarrow b \)  and a  \( y \in X_{b} \)  so that  \( x = y\pi \) ; and non-degenerate otherwise. For degenerate x, we refer to the factorization  \( x = y\pi \)  as an Eilenberg–Zilber decomposition of x. As observed in [BM11, 6.9–10], the axioms of Definition 6.2.1 imply that Eilenberg–Zilber decompositions are essentially unique, which implies that the latching maps  \( L_{a}X \mapsto X_{a} \)  are monomorphisms whose images are the degenerate elements. Moreover, the following relative version of this result holds:

70