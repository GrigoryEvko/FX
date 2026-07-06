Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

we take a different approach by isolating a particular universal property for the embedding Cat $\hookrightarrow$ $\mathcal{U}$ and arguing that all the other properties of Cat stem from this single property.

The universal property in question is an $\infty$-categorical version of the Grothendieck correspondence, often referred to as straightening-unstraightening in the $\infty$-categorical context. Classically, the Grothendieck correspondence states there is an equivalence between pseudofunctors $C \to \text{Cat}$ for some 1-category $C$ and pairs of a category $\mathcal{E}$ and a cocartesian family $\mathcal{E} \to C$.$^2$ Naively, this suggests a simple universal property for the type Cat: We should require for every $\infty$-category $C$ an equivalence between the type of functions $C \to \text{Cat}$ and the type $\sum_{E:\mathcal{U}} \sum_{\pi:E \to C} \text{isCocart}(\pi)$. Unfortunately, this definition is too straightforward: if such a Cat existed we would be able to show that isCocart held for every map $\pi$ which is certainly not true.

The problem is familiar to cubical type theorists: we are essentially asking for Cat to be a universal fibration, where isCocart is our notion of fibrancy. It is well-known that one cannot give universal property for the univalent universe in the extensional type theory of cubical sets [30]: the naive equivalence is only valid with respect to closed elements and cannot be internalized this way into type theory where it would also apply to elements in an arbitrary context. A solution to this problem in cubical type theory was presented by Licata et al. [18]. There the authors give a description of a universal fibration in an extensional type theory for cubical sets using modal type theory. They supplement type theory with an idempotent comonad $b$, such that the modal type $\langle b \mid A \rangle$ contains only the global elements of $A$. After further extending type theory with a right adjoint to $\mathbb{I} \to -$, they are then not only able to express the desired universal property (appropriately annotated with $b$), but also use the aforementioned right adjoint to derive it.

This idea has been adapted to variants of simplicial type theory first by Weaver and Licata [42] and later by Gratzer et al. [10] to construct a category of discrete $\infty$-categories (spaces). We follow on this line of work—specifically Gratzer et al. [10]—and use the $b$ modality to state the correct universal property for the category of categories and produce a type satisfying it. In particular:

**Theorem 4.3.** Cat is the base of the universal cocartesian family, i.e., for any $C \ni_b \mathcal{U}$, we have $\langle b \mid C \to \text{Cat} \rangle \simeq \langle b \mid \sum_{E:C \to \mathcal{U}} \text{isCocart}(E) \rangle$.

On its own, this statement is not worth much. We do not know whether Cat is a category itself, let alone to what its objects and morphisms correspond. To resolve this, we give a detailed analysis of the structure of cocartesian fibrations over certain categories, relying on the established results in simplicial type theory. As a particular case of these results, we conclude that cocartesian fibrations over $\mathbb{I}$ are determined by (1) a pair of categories $C, D$ along with (2) a function $C \to D$. Consequently, we are able to prove the directed univalence theorem for Cat:

**Corollary 5.5** (Directed univalence). If $A, B$ are $b$-elements of Cat, then there is a equivalence $\text{dua}: \hom_{\text{Cat}}(A, B) \simeq \langle b \mid A \to B \rangle$.

Here we see the first major divergence between the case of categories and the previously considered case of discrete categories. Directed univalence for Cat only guarantees that $\hom_{\text{Cat}}(A, B)$ is

equivalent to $\langle b \mid A \to B \rangle$ whereas in the discrete case one obtains an equivalence with $A \to B$. This is inevitable: no category can have hom-spaces equivalent to $A \to B$ for arbitrary categories $A, B$. However, the appearance of modalities in directed univalence is a significant complication.

Further consequences of our analysis prove that Cat is a category and that composition of synthetic morphisms corresponds (under directed univalence) to composition of ordinary functions. In total then, we show that the universal property of Cat is sufficient to derive all the expected behavior of a category of categories as well as uniquely characterize Cat itself.

Directed univalence opens up a wide array of applications. For instance, we use it to show that Cat contains a number of recognizable reflective subcategories (truncated categories, partial orders, spaces, etc.). It also allows us to build new and important categories by combining Cat with existing type-theoretic connectives. As a simple example, we show that $\sum_{c:\text{Cat}} c$ can be analyzed using directed univalence and use its attendant structure homomorphism principle (SHP) to see that $\sum_{c:\text{Cat}} c$ is the lax slice category 1 $\nmid$ Cat.

Finally, while Theorem 4.3 is a form of the Grothendieck correspondence, it is not the strongest form possible. This would state that there is an equivalence of $\infty$-categories between cocartesian families over $C$ and the functor category $C \to \text{Cat}$. We adapt an argument sketched by Cisinski et al. [6] to STT to show that Theorem 4.3 upgrades to an equivalence of categories and thereby give a synthetic proof of the straightening-unstraightening theorem [19].

## 1.2 Contributions and outline

Our main contribution is the first construction of a directed univalent category of categories within STT together with a verification of all its essential properties. This is the last major primitive missing from the theory of $\infty$-categories in simplicial type theory and, additionally, also constitutes a new and novel approach to a foundational theorem in $\infty$-category theory itself. With this in place, we also note that a putative full directed type theory can be interpreted into $\infty$-categories by giving a mere syntactic translation to the appropriate fragment of STT.

- We extend the methodology of Licata et al. [18] to construct a universal cocartesian family $\text{Cat}_\bullet \to \text{Cat}$.
- We derive purely from this universal property that Cat is a category, satisfies directed univalence, etc.
- We prove various properties of Cat and showcase the novel applications of SHP it enables.
- Finally, we give a fully synthetic proof of the foundational straightening-unstraightening theorem.

Over all, we demonstrate how type theory (through STT) is highly effective for proving major results in higher category theory.

The remainder of the paper is organized as follows. In Section 2 we recall the main ideas of simplicial type theory, its triangulated type theory variant, and the modal extensions thereof. This, along with Section 3 on cocartesian fibrations, is intended to make the paper as self-contained as possible. In Section 4 we define Cat and prove Theorem 4.3, the main construction of this paper. In Section 5, we combine our new results on cocartesian fibrations along with the results of the prior section to prove Corollary 5.5 along with the fact that Cat is a category. Finally, in Sections 6 and 7, we

$^2$In the 1- and 2-categorical literature these are often referred to as Grothendieck opfibrations. We use "cocartesian" as it is the standard term in $\infty$-category theory.