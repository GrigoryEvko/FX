Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

this data we may reconstruct a functor  \( (-)_{\mathbb{I}}:\langle b\mid\mathcal{U}\rangle\to\langle b\mid\mathcal{U}\rangle \) . Crucially, this axiom only applies when A is b-annotated; Licata et al. [18] show that requiring it for arbitrary types forces  \( I=1 \) , contradicting  \( 0\neq1:I \) . Moreover, as noted earlier, this axiom is not validated by the model of STT in simplicial spaces; it is only after shifting to cubical spaces that Axiom 8 is valid. Concretely, it is often the case that even if A is known to be simplicial, the same will not be true of  \( A_{I} \) . Our main use of this axiom is to “transpose” various b-annotated predicates  \( X^{I}\to HProp \)  into predicates  \( X\to HProp \) . For convenience, we bundle up this process into the following lemma:

Lemma 2.9. If \(\phi :_{\mathfrak{b}} \mathcal{U}^{\mathbb{I}^{n}} \to \mathrm{HProp}\), there is a \(\bar{\phi} :_{\mathfrak{b}} \mathcal{U} \to \mathrm{HProp}\) equipped with a canonical equivalence:

\[
\prod_ {A \ni X \to \mathcal {U}} \langle b | (x: X) \to \bar {\phi} (A x) \rangle \simeq \langle b | (x: X ^ {\mathbb {I} ^ {n}}) \to \phi (A \circ x) \rangle
\]

Finally, Gratzer et al. [10] have shown that  \( TT_{\mathbb{S}} \)  (MTT with this mode theory extended with all of the above axioms) has a model in cubical spaces. They further show, based on a result of Riehl and Shulman [33], that categories in  \( TT_{\mathbb{S}} \)  are realized by a standard model of  \( \infty \) -categories: complete Segal spaces [31].

Theorem 2.10. There is a model of \(TT_{\mathbb{S}}\) in cubical spaces \(\mathrm{PSh}_{\mathrm{eSet}}(\square)\). In this model, categories are realized by complete Segal spaces.

### 2.4 Category theory in triangulated type theory

We require some of the category theory developed previously in  \( TT_{\Sigma} \)  and STT [5, 10, 11, 33]. To keep this paper more self-contained, we recall the relevant results and definitions here.

As noted by Riehl and Shulman [33], a natural transformation between functors \(f, g: C \to D\)—i.e., an element of \(\hom(f, g)\)—corresponds precisely to a family \(\prod_{c: C} \hom(f, c, g, c)\). Consequently, a pointwise invertible natural transformation is invertible. We note a refinement of this statement by Gratzer et al. [11] which further reduces this to \(b\) elements (i.e., objects) of \(C\):\( ^{3} \)

Lemma 2.11. If \(C, D \ni_{\mathfrak{b}} \mathcal{U}\) are categories and \(f, g \ni_{\mathfrak{b}} C \to D\), then a natural transformation \(\alpha \ni_{\mathfrak{b}} \hom(f, g)\) is invertible if and only if for all \(c \ni_{\mathfrak{b}} C\) the map \(\alpha(c): \hom(f, c, g, c)\) is invertible.

We similarly have a synthetic version of the classical result that full, faithful and essentially surjective functors are equivalences.

Lemma 2.12. If \(C, D \ni_{\mathfrak{b}} \mathcal{U}_{\mathrm{isCat}}\), then \(f \ni_{\mathfrak{b}} C \to D\) is invertible iff \(f\) is essentially surjective and fully faithful on \(b\)-elements of \(C\).

Our calculations with cocartesian fibrations in Sections 3 and 4 will rely on the theory of adjunctions in \(\mathrm{TT}_{\mathbb{S}}\). To begin with, an adjunction between two functors \(f: C \to D\) and \(g: D \to C\) is given by a collection of equivalences:

\[
\alpha : \prod_ {c: C} \prod_ {d: D} \hom (f c, d) \simeq \hom (c, g d)
\]

Note that we do not require any additional naturality constraints on \(\alpha\), these are automatically enforced by virtue of working synthetically. We say \(f\) is a left adjoint if there exists a (necessarily unique) \((g, \alpha)\), and dually that \(g\) is a right adjoint if there exists \((f, \alpha)\). It is often difficult to construct such a family of equivalences directly, so we often use the following result of Gratzer et al. [11]:

\( ^{3} \) Gratzer et al. [11] prove Lemmas 2.11 and 2.13 using the twisted arrow modality, which we have chosen not to include in TT \( _{S} \) for simplicity. More elementary proofs merely relying on Axiom 6 are possible and so there is no issue with their use in TT \( _{S} \).

Lemma 2.13. If \(C, D \ni_{\mathfrak{b}} \mathcal{U}\) are categories, then \(f \ni_{\mathfrak{b}} C \to D\) is a left adjoint iff for all \(d \ni_{\mathfrak{b}} D\) there exists \(c \ni_{\mathfrak{b}} C\) and \(\epsilon \ni_{\mathfrak{b}} \hom(f(c), d)\) such that the following is an equivalence for all \(c' \ni_{\mathfrak{b}} C\):

\[
\epsilon_ {*} \circ f: \hom (c ^ {\prime}, c) \to \hom (f (c ^ {\prime}), d)
\]

We shall also have use for the various concrete examples of categories constructed by Gratzer et al. [10]. Foremost among these is the category of groupoids S—the  \( \infty \) -categorical analog of the category of sets. Like our eventual definition of the category of categories, this is characterized through a universal property.

Definition 2.14. A family of types \(A: X \to \mathcal{U}\) is covariant if it is right orthogonal to the inclusion \(\{\emptyset\} \to \mathbb{I}\).

More intuitively, covariant families are families of groupoids such that synthetic homomorphisms of the base lift coherently to functors of the fibers. We shall give more exposition of this idea indirectly in Section 3 when we study their generalization: cocartesian families. Covariant families are closed under numerous properties, including precomposition, \(\Sigma\)-types, etc. We now define \(S\) as the base of the universal covariant family:

Definition 2.15. S is the unique subtype of the universe such that  \( S \to U \)  is covariant, and for all  \( X \ni_{b} U \) , the canonical map  \( \langle b | X \to S \rangle \to \langle b | \sum_{A:X \to U} \text{isCov}(A) \rangle \)  is an equivalence.

Consequently, the type of objects of S, i.e.,  \( \langle b \mid S \rangle \) , is immediately seen to be equivalent to b-covariant families over 1. These, in turn, are equivalent to b-groupoids. The main result of Gratzer et al. [10] extends this characterization to synthetic morphisms:

Theorem 2.16. S is a category, and there is a canonical equivalence  \( \hom_{S}(A,B) \simeq (A \to B) \) . Moreover, under this equivalence, identities and composition of synthetic morphisms are realized by identity functions and ordinary function composition.

Finally, we record a minor but useful result stating that \(\mathbb{I}\), and some types derived from it, form categories [10].

Lemma 2.17. \(\mathbb{I},\mathbb{I}^n\) , and \(\Delta^n\) all form categories.

## 3 Recollections on cocartesian fibrations

Our eventual goal of characterizing \(\langle b | X \to \mathrm{Cat} \rangle\) crucially depends on the theory of cocartesian families [13, 19]. These are a subset of type families \(A: X \to \mathcal{U}\) for which (1) each \(Ax\) is a category, and (2) each morphism \(f: \hom(x, y)\) in \(X\) induces a transport function \(Ax \to Ay\). We shall require that these transport functions are functorial, and that the coherences enforcing functoriality are themselves coherent, etc. In order to structure all of this data, we ask for \(A\) to satisfy a number of propositions that, when combined, give rise to (1) and (2) above. While somewhat indirect, this accounts for the infinite hierarchy of coherences that would otherwise be impossible to write down. This material has been developed within STT [5]. We recall it for the reader's benefit.

### 3.1 The definition of cocartesian families

Consider a family \(A: X \to \mathcal{U}\) and write \(\rho^A\) for the canonical map given by restriction and projection \(\widetilde{A}^{\Delta^2} \to \widetilde{A}^{\Delta_0^2} \times_{X^{\Delta_0^2}} X^{\Delta^2}\). Note that the restriction \(\widetilde{A}^{\Delta^2}\) to \(\widetilde{A}^{\{\emptyset \to 1\}}\) along with the corresponding