Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:3

LSR17]. A mode theory gives rise to the following correspondence:

object \(\sim\) mode  
morphism \(\sim\) modality  
2-cell \(\sim\) natural map between modalities

The equations between morphisms and between 2-cells in a mode theory can be used to precisely specify the interactions we want between different modalities. We will illustrate this point with an example.

Instantiating MTT. Suppose we have a mode theory M with a single object m, a single generating morphism  \( \mu : m \to m \) , and no non-trivial 2-cells. Equipping MTT with M produces a type theory with a single modal type constructor,  \( \langle\mu \mid -\rangle \) . This is the simplest non-trivial setting, and we can prove very little about it without additional 2-cells.

If we add a 2-cell \(\epsilon : \mu \Rightarrow 1\) to \(\mathcal{M}\), we can define a function

\[
\operatorname{extract} _ {A}: \langle \mu | A \rangle \rightarrow A
\]

inside the type theory. If we also add a 2-cell \(\delta : \mu \Rightarrow \mu \circ \mu\) then we can also define

\[
\mathsf {d u p l i c a t e} _ {A}: \langle \mu | A \rangle \to \langle \mu | \langle \mu | A \rangle \rangle
\]

Furthermore, we can control the precise interaction between duplicate \( _{A} \) and extract \( _{A} \) by adding more equations that relate \( \epsilon \) and \( \delta \). For example, we may ask that M be the walking comonad [SS86] which leads to a type theory with a dependent S4-like modality [Pfe01, dR15, Shu18]. We can be even more specific, e.g. by asking that \( (\mu,\epsilon,\delta) \) be idempotent.

Thus, a morphism \(\mu : n \to m\) introduces a modality \(\langle \mu | - \rangle\), and a 2-cell \(\alpha : \mu \Rightarrow \nu\) of \(\mathcal{M}\) allows for the definition of a function of type \(\langle \mu | A \rangle \to \langle \nu | A \rangle\) at mode \(m\).

Relation to other modal type theories. Most work on modal type theories still defies classification. However, we can informatively position MTT with respect to two qualitative criteria, viz. usability and generality.

Much of the prior work on modal type theory has focused on bolting a specific modality onto a type theory. The benefit of this approach is that the syntax can be designed to be as convenient as possible for the application at hand. For example, spatial/cohesive type theory [Shu18] features two modalities, b and  \( \sharp \) , and is presented in a dual-context style. This judgmental structure, however, is applicable only because of the particular properties of b and  \( \sharp \) . Nevertheless, the numerous pen-and-paper proofs in op. cit. demonstrate that the resulting system is easy to use.

At the other end of the spectrum, the framework of Licata-Shulman-Riley (LSR) [LSR17] comprises an extremely general toolkit for simply-typed, substructural modal type theory. Its dependent generalization, which is currently under development, is able to handle a very large class of modalities. However, this generality comes at a price: its syntax is complex and unwieldy, even in the simply-typed case.

MTT attempts to strike a delicate balance between those two extremes. By avoiding substructural settings and some kinds of modalities we obtain a noticeably simpler apparatus. Unlike LSR, we need not annotate our term formers with delayed substitutions, and our approach extends to dependent types in a straightforward manner. Most of the pleasant type-theoretic behaviour of MTT is achieved by ensuring that none of its rules 'trim' the context, which would necessitate either delayed substitutions  \( [BGC^{+}16, LSR17] \)  or delicate proofs of the admissibility of substitution  \( [BGM17, BCM^{+}20, GSB19a] \) . We also show that