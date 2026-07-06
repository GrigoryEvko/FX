Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:31

laboriously by [New18, §2.3.14]. A more conceptual proof is given by [Uem19, Cor. 3.14] in the language of discrete fibrations.

We then require that all connectives  \( (\prod, \sum, \text{refl}) \)  strictly commute with these morphisms. Finally, we can extend this to a model of MTT by requiring not just a functor, but a natural transformation  \( C \Rightarrow D \) , where  \( C, D : M^{coop} \to Cat \)  satisfy the obvious generalizations of the conditions written above. Specifying this formally:

Definition 5.8. A morphism between two models of MTT, C, D, is given by a 2-natural transformation  \( \alpha : C \Rightarrow D \) . Moreover, we require a choice of commuting squares:

\[
\begin{array}{c} \widetilde {\mathcal {U}} _ {\mathcal {C} [ m ]} \xrightarrow {\widetilde {\varphi} _ {m}} \alpha_ {m} ^ {*} \widetilde {\mathcal {U}} _ {\mathcal {D} [ m ]} \\ \tau_ {\mathcal {C} [ m ]} \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Biggl \downarrow \alpha^ {*} \tau_ {\mathcal {D} [ m ]} \\ \mathcal {U} _ {\mathcal {C} [ m ]} \xrightarrow {\varphi_ {m}} \alpha^ {*} \mathcal {U} _ {\mathcal {D} [ m ]} \end{array}
\]

Moreover, we require that \((\varphi, \widetilde{\varphi})\) strictly commutes with all operations.

\[
\alpha_ {m} (\Gamma . (\mu \mid A)) = \alpha_ {m} (\Gamma). (\mu \mid \varphi (A))
\]

\[
\prod \circ (\varphi , \varphi) = \varphi \circ \prod
\]

\[
\sum \circ (\varphi , \varphi) = \varphi \circ \sum
\]

\[
\mathbf {M o d} _ {\mu} \circ [ [ \widehat {\mathbf {B}} _ {\mu} ] ] ^ {*} \varphi = \varphi \circ \mathbf {M o d} _ {\mu}
\]

\[
\mathbf {B o o l} = \varphi \circ \mathbf {B o o l}
\]

\[
\mathbf {I d} \circ (\varphi , \widetilde {\varphi}, \widetilde {\varphi}) = \varphi \circ \mathbf {I d}
\]

\[
\mathbf {l a m} \circ (\varphi , \widetilde {\varphi}) = \widetilde {\varphi} \circ \mathbf {l a m}
\]

\[
\mathbf {p a i r} \circ (\varphi , \widetilde {\varphi}) = \widetilde {\varphi} \circ \mathbf {p a i r}
\]

\[
\mathbf {m o d} _ {\mu} \circ [ [ \widehat {\mathbf {B}} _ {\mu} ] ] ^ {*} \widetilde {\varphi} = \widetilde {\varphi} \circ \mathbf {m o d} _ {\mu}
\]

\[
\mathbf {o p e n} _ {\mu} ^ {\nu} \circ (\widetilde {\varphi}, [ [ \widehat {\mathbf {B}} _ {\mu} ] ] ^ {*} \widetilde {\varphi}) = \widetilde {\varphi} \circ \mathbf {o p e n} _ {\mu} ^ {\nu}
\]

\[
\mathbf {t t} = \widetilde {\varphi} \circ \mathbf {t t} \quad \mathbf {f f} = \widetilde {\varphi} \circ \mathbf {f f}
\]

\[
\mathbf {i f} \circ (\widetilde {\varphi}, \widetilde {\varphi}, \widetilde {\varphi}) = \widetilde {\varphi} \circ \mathbf {i f}
\]

\[
\mathbf {r e f l} \circ \widetilde {\varphi} = \widetilde {\varphi} \circ \mathbf {r e f l}
\]

\[
\mathbf {J} \circ (\widetilde {\varphi}, \widetilde {\varphi}) = \widetilde {\varphi} \circ \mathbf {J}
\]

Remark 5.9 (The Initiality of Syntax). Under this definition of homomorphism, we immediately have an initial model [Car78, KKA19]. We will define this model to be our syntax and designate it \((\mathbb{S}[m])_{m\in \mathcal{M}}\).

## 6. CANONICITY

Equipped with the generalized algebraic theory of Section 4 and its reformulation through natural models in Section 5, we are ready to show that the syntax of MTT is well-behaved. In this section we will sketch the main parts of a proof of canonicity for MTT. This is a basic well-behavedness property which guarantees that terms of ground type, e.g. B, can be normalized. As expected, the proof is independent of the mode theory.

Proposition 6.1. If \(\vdash M:\mathbb{B}@\mathfrak{m}\), then either \(\vdash M = \mathfrak{tt}:\mathbb{B}@\mathfrak{m}\) or \(\vdash M = \mathfrak{ff}:\mathbb{B}@\mathfrak{m}\).

This kind of result would traditionally be established by producing a rewriting system along with a lengthy PER model construction. We will instead opt for a proof given by constructing a glued model [Coq19, KHS19]. The contexts, types, and terms of this model