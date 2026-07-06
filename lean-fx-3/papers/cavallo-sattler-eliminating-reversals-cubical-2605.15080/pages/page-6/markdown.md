6

Eliminating reversals from cubical type theories

a “syntactic” RMC  \( \mathbb{C}\mathrm{L}(T) \)  [37, §4.8] whose objects are environments  \( \Phi \)  over T and whose morphisms are instantiations: an instantiation  \( I\colon\Phi\to\Psi \)  where  \( \Psi=(\mathbb{A}_{1}:\Gamma_{1}\to e_{1},\ldots,\mathbb{A}_{n}:\Gamma_{n}\to e_{n}) \)  is an assignment  \( (\mathbb{A}_{1}:=\langle\vec{\mathbf{a}_{1}}\rangle t_{1},\ldots,\mathbb{A}_{n}:=\langle\vec{\mathbf{a}_{n}}\rangle t_{n}) \)  sending each metavariable  \( A_{i} \)  in the target to an expression  \( t_{i}:e_{i} \)  in context  \( \vec{a}_{i}:\Gamma_{i} \)  over  \( T[\Phi] \) . An instantiation is representable when it is isomorphic to the projection  \( \Phi:\Gamma\to\Phi \)  for an extension of an environment  \( \Phi \)  by a context  \( \Gamma \) . For concrete SOGATs, we usually suppress  \( \mathbb{C}\mathrm{L}(-) \)  and use the same name for the SOGAT and its induced RMC.

The RMC \(\mathbb{C}\mathrm{L}(T)\) has a (2, 1)-categorical universal property that characterizes RMC functors \(\mathbb{C}\mathrm{L}(T) \to \mathbb{R}\) up to isomorphism as interpretations [37, Theorem 4.8.18]. An interpretation of \(T\) in \(\mathbb{S}\) is a specification of the image of each declaration of \(T\) inside \(\mathbb{S}\). For example, an RMC functor \(F: \mathbb{M}\mathrm{LTT} \to \mathbb{S}\) is determined up to isomorphism by an object \(FTy \in \mathbb{S}\) and a representable map \(F\pi_{\mathrm{Tm}}: FTm \to FTy\), which specifies the image of \(\pi_{\mathrm{Tm}}: (\mathbb{A}: Ty, \mathbb{a}: Tm(\mathbb{A})) \to (\mathbb{A}: Ty)\). As a special case, we can speak of interpretations of a SOGAT \(T\) in another SOGAT \(S\) as interpretations of \(T\) in \(\mathbb{C}\mathrm{L}(S)\).

### 2.3 Models

An interpretation  \( \mathbb{C}\mathrm{L}(T)\to\mathbb{S} \)  is a model of a SOGAT as a second-order theory. To recover a notion of first-order model, corresponding for example to categories with families [16] for MLTT, Uemura uses presheaf categories with representable maps:

▶ Definition 8 ([37, §3.2.4]). A model  \( \mathcal{M} = (\mathcal{C}, M) \)  of an RMC R is a category C with a terminal object and an RMC functor  \( M: R \to \mathrm{PSh}(\mathcal{C}) \)  to the presheaf RMC of Example 7. We write  \( \mathcal{M}(\star) \)  for C and  \( \mathcal{M}(X) := MX \in \mathrm{PSh}(\mathcal{M}(\star)) \)  for  \( X \in R \) .

A morphism \(\mathcal{F} = (F, \alpha) \colon \mathcal{M} \to \mathcal{N}\) between models is a functor \(F \colon \mathcal{M}(\star) \to \mathcal{N}(\star)\) and family of natural transformations \(\alpha_X \colon \mathcal{M}(X) \to F^*\mathcal{N}(X)\), natural in \(X \in \mathbb{R}\), such that for each representable \(f \colon Y \to X\), the naturality square for \(\alpha\) at \(f\) satisfies a Beck-Chevalley condition. For \(c \in \mathcal{M}(\star)\), we write \(\mathcal{F}(c) \in \mathcal{N}(\star)\) for \(Fc\). For \(x \colon \& c \to \mathcal{M}(X)\) in \(\mathrm{PSh}(\mathcal{C})\), we write \(\mathcal{F}_X(x) \colon \& \mathcal{F}(c) \to \mathcal{N}(X)\) for the map corresponding by Yoneda to \(\alpha_X \circ x \colon \& c \to F^*\mathcal{N}(X)\).

Models of MLTT in this sense correspond directly to natural models as defined by Awodey [4], and thereby to categories with families:  \( \mathcal{M}(\star) \)  interprets the context judgment, and  \( \mathcal{M}(\mathrm{Ty}) \)  and  \( \mathcal{M}(\mathrm{Tm}) \)  the type and term judgments over a context. With an appropriate notion of 2-morphism, the collection of models of an RMC R forms a (2,1)-category  \( \mathbf{Mod}(\mathbb{R}) \) .

▶ Definition 9 ([37, Definitions 5.1.4 & 5.1.6]). The class of contextual objects in  \( \mathcal{M}(\star) \)  for a model  \( \mathcal{M} \in \text{Mod}(\mathbb{R}) \)  is inductively generated as follows:

1. terminal objects \(1 \in \mathcal{M}(\star)\) are contextual;
2. for each contextual \( c \in \mathcal{M}(\star) \), representable \( f: Y \to X \) in \( \mathbb{R} \), and pullback square

\[
\begin{array}{c} \mathbb {A} d \longrightarrow \mathcal {M} (Y) \\ \Big \downarrow^ {\perp} \qquad \qquad \qquad \Big \downarrow_ {\mathcal {M} (f)} \\ \mathbb {A} c \longrightarrow \mathcal {M} (X) \end{array}
\]

with \(d\in \mathcal{M}(\star)\) , the object \(d\) is contextual.

A model is democratic when all of its objects are contextual. The heart (or contextual core) \(\mathcal{M}^{\heartsuit}\in\mathbf{Mod}(\mathbb{R})\) of \(\mathcal{M}\) is defined by taking \(\mathcal{M}^{\heartsuit}(\star)\) to be the full subcategory of contextual objects in \(\mathcal{M}(\star)\) and \(\mathcal{M}^{\heartsuit}(X)\) to be the restriction of \(\mathcal{M}(X)\) to a presheaf on \(\mathcal{M}^{\heartsuit}(\star)\).