Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

unique composition witness. To define this formally, we note that maps $\Lambda_1^2 \to A$ precisely capture the data of composable arrows:

Definition 2.2. A type $A$ is Segal if isEquiv($A^{\Lambda^2} \to A^{\Lambda_1^2}$) holds.

Notation 2.3. If $f, g: A^\ell$ and $p: f(1) = g(0)$, we write $[f, g, p]$ for the induced map $A^{\Lambda_1^2}$ and, if $A$ is Segal, $g \circ_p f$ for the composite. Furthermore, we shall subsequently have use for the outer horns $\Lambda_0^2 = \sum_{i,j:\mathbb{I}} i = j \lor j = 0$ and $\Lambda_2^2 = \sum_{i,j:\mathbb{I}} i = 1 \lor i = j$. Finally, we write $i$ for the element of $\Delta^{n+i}$ given by $(1, \dots, 1, 0, \dots)$ of $i$ copies of 1 followed by $n$ copies of 0.

Segal types enjoy a unique composition operation given by the inverse of the map $A^{\Lambda^2} \to A^{\Lambda_1^2}$, and calculation shows that the aforementioned definition of the identity morphism is a left and right unit for composition. However, objects in a pre-category have two distinct notions of sameness: via either the identity type or synthetic isomorphism. By the latter, we mean a morphism $f: \hom(a, b)$ equipped with $g, h: \hom(b, a)$ along with composition witnesses showing that $g(h)$ is left (right) inverse to $f$. One can define $\mathbb{E} = \Delta^2 \sqcup_{\Lambda_1^2} \mathbb{I} \sqcup_{\Lambda_2^2} \Delta^2$ such that $\mathbb{E} \to X$ precisely corresponds to an equivalence in $X$ [5, §4.2]). A distinctive feature of $\infty$-category theory is that these two notions (object equality and isomorphism) can be made to coincide; a property similar to the univalence axiom. We therefore also single out those types which satisfy this local univalence condition:

Definition 2.4. A type $A$ is Rezk if isEquiv(const: $A \to A^\mathbb{E}$).

Definition 2.5. A simplicial, Segal, and Rezk type is called a category. A category whose morphisms are all invertible is a groupoid.

Remark 2.6. The general results of Rijke et al. [34] show that categories and groupoids are modal types for idempotent monads. We write $\bigcirc_{\text{grpd}}$ for the idempotent modality associated with groupoids in particular, i.e., nullification at $\mathbb{I}$.

We shall also have occasion to use the relative versions of the Segal and Rezk conditions. Given a family of types $A: X \to \mathcal{U}$, we say that $A$ is (right) orthogonal to a map $I \to J$ if the following canonical map is an equivalence:

$$\left(\sum_{x:X} A(x)\right)^J \to X^J \times_{X^J} \left(\sum_{x:X} A(x)\right)^I$$

The relative Segal condition asks that a family of types $A: X \to \mathcal{U}$ be right orthogonal to $\Lambda_1^2 \to \Delta^2$ and the relative Rezk condition asks the same for $\mathbb{E} \to \mathbf{1}$. A Segal family is called inner and a family that is both Segal and Rezk is iso-inner.

For use in Section 4, we note that we can phrase the requirement that a family be inner using the following predicate:

$$\text{isInner}: (\Delta^2 \to \mathcal{U}) \to \text{HProp}$$

$$\text{isInner } A = \text{isEquiv}\left(\left(\prod_{t:\Delta^2} A t\right) \to \left(\prod_{t:\Lambda_1^2} A t\right)\right)$$

A family $A: X \to \mathcal{U}$ is inner if and only if $\prod_{h:\Delta^2 \to X} \text{isInner}(A \circ h)$ holds.

Notation 2.7. We shall often identify a family $A: X \to \mathcal{U}$ with its associated total space projection $\pi$ from $\overline{A} := \sum_{x:X} A x$ to $X$. We shall say that an arbitrary map of types $f: X \to Y$ is, for instance, inner if the associated map $Y \to \mathcal{U}$ sending $y$ to $f^{-1}(y)$ is inner.

Given a family $A: X \to \mathcal{U}$ and an arrow $f: \mathbb{I} \to X$ we define dependent arrows over $f$ from $a: A(f0)$ to $a': A(f1)$ as follows:

$$\hom_f^A(a, a') := \sum_{\alpha: (t:\mathbb{I}) \to A(f t)} (\alpha 0 = a) \times (\alpha 1 = a')$$

In an inner family there exists an induced composition operation for dependent arrows [5].

## 2.2 Multimodal type theory

The next step in $\text{TT}_{\mathbb{Q}}$ is to include modalities: special type constructors that violate key properties we ordinarily require in type theory, such as stability under substitution. We use these modalities to internalize crucial operations from our intended model of cubical spaces such as the discrete and codiscrete endofunctors, the opposite functor, etc. To this end, we recall some of the details of the modal extension to type theory, MTT, following [9]. See Gratzer [8] for a more detailed account. Since our primary goal is to write programs in MTT, we focus on the "informal" version of the syntax and defer the formal rules (replete with de Bruijn indices and a substitution calculus) to Appendix A.

First, MTT is parameterized by a mode theory $\mathcal{M}$. This is a strict 2-category describing the modalities (as 1-cells) and transformations between them (as 2-cells). While MTT also permits distinct type theories to be related by modalities by considering mode theories with multiple modes (0-cells), we do not need this generality and therefore assume that mode theories have only one object. We shall also only be concerned with mode theories with at most one 2-cell between every pair of 1-cells i.e., 2-categories that are merely poset-enriched. As such, our mode theories are simply given by ordered monoids. The mode theory required for $\text{TT}_{\mathbb{Q}}$ is described in Section 2.3, but we continue with an arbitrary mode theory satisfying these constraints for the moment.

The main extension of MTT is to add a new modal type $\langle \mu \mid - \rangle$ for each modality $\mu \in \text{Arr}(\mathcal{M})$. However, as already mentioned modal types are somewhat peculiar, and to accommodate them MTT also modifies context extension. Specifically, each variable in an MTT context is annotated with a "formal division" of modalities $x:_{\mu/\nu} A$. We write $\Gamma/\nu$ for the operation which modifies each annotation in $\Gamma$ to send $x:_{\mu/\nu_0} A$ to $x:_{\mu/\nu_0 \circ \nu} A$. The variable rule is then modified to account for these formal divisions as follows:

$$\frac{\mu \le \nu \quad x:_{\mu/\nu} A \in \Gamma}{\Gamma \vdash x: A}$$

Note that one can recover the ordinary rules for variables by considering the annotation id/id. As a matter of notation therefore, we generally suppress division by id and omit the annotation entirely for id/id so that we instead write $x:_{\mu} A$ or $x: A$.

These annotations are then manipulated by the modal operators $\langle \mu \mid - \rangle$. In particular, they are added by the formation and introduction rules. The (somewhat lengthy) elimination rule, on the other hand, papers over the difference between annotations on a variable and modal types by allowing us to convert a binding $x:_{\nu/\text{id}} \langle \mu \mid A \rangle$