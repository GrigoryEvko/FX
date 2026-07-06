arXiv:2506.23651v2 [math.CT] 17 Mar 2026

# DOUBLY WEAK DOUBLE CATEGORIES

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

ABSTRACT. We propose a definition of double categories whose composition of 1-cells is weak in both directions. Namely, a doubly weak double category is a double computad — a structure with 2-cells of all possible double-categorical shapes — equipped with all possible composition operations, coherently. We also characterize them using “implicit” double categories, which are double computads having all possible compositions of 2-cells, but no compositions of 1-cells; doubly weak double categories are then obtained by a simple representability criterion. We also show that they are equivalent to Verity’s double bicategories satisfying a simple additional condition that has appeared previously in the literature, and to a similar enhancement of Garner’s cubical bicategories.

# CONTENTS

|  1. Introduction | 1  |
| --- | --- |
|  2. Bicategories | 8  |
|  3. Doubly weak double categories | 12  |
|  4. Double computads | 17  |
|  5. Algebraic definitions | 23  |
|  6. Icons and 2-monads | 28  |
|  7. Double bicategories | 34  |
|  8. Cubical bicategories | 44  |
|  9. A finite axiomatization | 51  |
|  Appendix A. Transformations and modifications | 59  |
|  References | 70  |

# 1. INTRODUCTION

1.1. The problem of doubly weak double categories. A double category is a structure like a 2-category but with two different sorts of 1-cells, horizontal and vertical, and 2-cells shaped like squares (with two 1-cells of each sort on their boundaries):

Just as there are strict and weak versions of 2-categories, there are strict and weak versions of double categories. Strict double categories are easy to define, as internal categories in the category Cat of categories (whereas 2-categories are enriched

The second author was supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.

1

2

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

categories in **Cat**). The two different sorts of 1-cell are then, respectively, the morphisms in the category-of-objects and the objects in the category-of-morphisms. Now just as a bicategory is a “weakly enriched category” in the 2-category *Cat* of categories, the definition of internal category can be weakened so that it satisfies the usual associativity and unit laws only up to coherent isomorphism (a so-called “internal pseudo-category” [Fer06]). This results in the *pseudo double categories* from [GP99].

However, pseudo double categories are weak in only one direction: composition of morphisms in the category-of-objects is still strict. Many of the weak double categories arising naturally do satisfy this constraint (e.g. the double category of categories, whose two sorts of 1-cells are functors, which compose in a strict way, and profunctors, which do not). But there are some situations in which one would like a notion of double category where composition is weak in both directions. For example:

- Every strict 2-category $\mathcal{C}$ has a strict double category of “squares” a.k.a. “quintets”,$^{1}$ where both sorts of 1-cells are those of $\mathcal{C}$, and the squares are 2-cells in $\mathcal{C}$ of the form

But if $\mathcal{C}$ is a *bicategory*, then this would have to be a double category that is weak in both directions.

- As shown in [BHKP02], any topological space has a fundamental double groupoid consisting of points as 0-cells, continuous paths as both kinds of 1-cells, and homotopy classes of homotopies as 2-cells. The double groupoid constructed in [BHKP02] is made strict by quotienting the paths by “thin homotopy”, but it would be more natural to have weak composition in both directions, since concatenation of paths is not strictly associative.
- A *proarrow equipment* [Woo82] can be defined as a pseudofunctor of bicategories $\mathcal{C} \rightarrow \mathcal{D}$ that is bijective on objects, locally full and faithful, and such that every 1-cell in its image is a left adjoint. This is intended as an abstraction of examples such as the pseudofunctor $\mathcal{C}at \rightarrow \mathcal{P}rof$ assigning to each functor its representable profunctor. As observed in [Ver92, Shu08], a proarrow equipment gives rise to a double category, whose objects are those shared by $\mathcal{C}$ and $\mathcal{D}$, whose two sorts of 1-cell are those of $\mathcal{C}$ and $\mathcal{D}$ respectively, and whose 2-cells come from $\mathcal{D}$. However, this is only a pseudo double category if $\mathcal{C}$ is a strict 2-category. When $\mathcal{C}$ and $\mathcal{D}$ are both bicategories, this double category should be weak in both directions.

In practice, often $\mathcal{C}$ is strict, but not always. Two examples where it is not are the inclusion $\mathcal{S}pan(\mathbf{E}) \rightarrow \mathcal{P}oly(\mathbf{E})$ of the bicategory of spans in the bicategory of polynomials [KG13, Web15], for any locally cartesian closed category $\mathbf{E}$; and the inclusion $\mathcal{C}atAna(\mathbf{E}) \rightarrow \mathcal{P}rof(\mathbf{E})$ of internal anafunctors [Bar06, Rob12] into internal profunctors, for any topos $\mathbf{E}$.

- A special case of an equipment is when the 1-cells of $\mathcal{C}$ are defined to be adjunctions in $\mathcal{D}$ (pointing in the direction of the left adjoints; these are

$^{1}$This unlovely term arises from the fact that to determine a 2-cell in this double category requires five data: a 2-cell in $\mathcal{C}$ and four 1-cells in $\mathcal{C}$ that form its boundary (the decomposition of its source and target as composites not being determined by the 2-cell itself).

DOUBLY WEAK DOUBLE CATEGORIES

3

sometimes called *maps*). The resulting double category was used in [KS74] to formalize the functoriality of the “mates” correspondence in $\mathcal{D}$. To do the same when $\mathcal{D}$ is a bicategory would require a doubly weak double category.

- If $\mathcal{C}$ and $\mathcal{D}$ are strict 2-categories, there is a strict double category that we denote $\operatorname{Hom}_{\operatorname{co}/\operatorname{lax}}(\mathcal{C}, \mathcal{D})$ whose objects are functors $\mathcal{C} \to \mathcal{D}$, whose horizontal and vertical 1-cells are *lax* and *colax* transformations respectively, and whose 2-cells are a general notion of modification. This should also be true if $\mathcal{C}$ and $\mathcal{D}$ are bicategories, but in that case this double category would be weak in both directions.
- Similarly, if $T$ is a 2-monad on a 2-category $\mathcal{C}$, there is a strict double category whose objects are $T$-algebras and whose horizontal and vertical 1-cells are *lax* and *colax* $T$-morphisms respectively. (Such double categories were first considered by [GP04].) This should also be true if $T$ is a pseudomonad on a bicategory, but in that case this double category would again be weak in both directions.

We evidently cannot define doubly weak double categories as any sort of internal category in categories (since the arrows of a category compose strictly associatively). But we can write out the definition of a double category explicitly, with sets of 0-cells, vertical and horizontal 1-cells, and squares, and then try to insert coherence isomorphisms relating compositions of 1-cells. However, it is surprisingly tricky to make this work, for the following reason.

Note first that the usual associativity and unit constraint isomorphisms in a bicategory are *globular*:

![img-0.jpeg](img-0.jpeg)

In a pseudo double category, and presumptively in a doubly weak double category, the corresponding requirement would be that they are squares bordered by vertical identity 1-cells, simulating globular 2-cells:

![img-1.jpeg](img-1.jpeg)

In order to state the usual coherence conditions that these globular 2-cells should satisfy, we must be able to compose them. But when *vertical* composition of 1-cells is not strictly unital, vertical composition of squares takes squares that are bordered by vertical identities to squares that are not; thus the usual coherence conditions on these squares are not well-typed (the vertical boundaries of the two sides of the

4

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

equation are not equal).

![img-2.jpeg](img-2.jpeg)

We might try to correct this by horizontally composing with vertical unitors, but this in turn affects the bordering horizontal 1-cells; and so on, *ad infinitum*. For instance, we cannot even compose a putative isomorphism $\alpha$ with its putative inverse and other coherence cells to yield an identity on the source or target:

![img-3.jpeg](img-3.jpeg)

At least two ways around this problem have been proposed to date.

- In [Ver92] Verity defined a *double bicategory* to consist of horizontal and vertical bicategories with the same set of objects, together with sets of squares that are acted on by the 2-cells of the bicategories and can be composed with each other horizontally and vertically.

This includes the important examples, but it does not quite capture all their structure, since nothing in a double bicategory allows us to identify the 2-cells in the horizontal and vertical bicategories with the squares bordered by identities, whereas in examples these two are always the same.

It is possible to correct this problem by assuming an additional axiom. This axiom was already mentioned by Verity [Ver92, Lemma 1.4.9], and was called “saturation” in [RvdWAN25]. We will discuss this further in Sections 1.3 and 7.

- In [Gar10a] Garner proposed a definition of *cubical bicategory* that consists of the data of a double category (objects, horizontal and vertical 1-cells, and squares) with 1-cell composition and identities (satisfying no axioms), plus a way to compose any grid of squares along any way of composing up its boundaries, satisfying appropriate coherence axioms.

This also describes the important examples, but also does not capture all of their structure. In particular, with this definition there is no obvious way to extract (say) a horizontal bicategory consisting of objects, horizontal arrows, and squares bordered by vertical identities.

In this paper we propose a new definition of doubly weak double category, which is closely related to the above approaches but is not subject to either of their problems. We will show that our doubly weak double categories are equivalent to

DOUBLY WEAK DOUBLE CATEGORIES

5

double bicategories satisfying the “saturation” condition (which we call “tidiness”), and also to cubical bicategories satisfying an analogous condition. Furthermore, from a certain perspective, our doubly weak double categories are simply the double-categorical analogue of bicategories, as we will explain next.

1.2. **Implicit structures.** Bicategories are typically regarded as more complicated than strict 2-categories. But from another point of view, bicategories are simpler than strict 2-categories. Roughly, a bicategory is like a strict 2-category but *without* equalities between compositions of 1-cells.

From this perspective, just like a group has “fewer ingredients” than a ring, a bicategory has “fewer ingredients” than a strict 2-category. In particular, when a definition of a 2-categorical shape (e.g. the shape of an adjunction, a monad, or a module) makes no reference to equality between compositions of 1-cells, it actually belongs in the more general setting of bicategories.

Let us make this more precise. We start with a **2-computad** (introduced by Street in [Str76]²), a “2-category without composition”. Explicitly, this consists of

- a collection of 0-cells,
- a collection of 1-cells, each with a source and a target 0-cell, and
- a collection of 2-cells, each with a source and a target string of 1-cells (where these 1-cells match along 0-cells as appropriate).

A 2-computad is the sort of structure that generates a free 2-category, just as a directed graph (a.k.a. 1-computad, a “category without composition”) is the sort of structure that generates a free category; indeed, Street observed in [Str76] that 2-categories are monadic over 2-computads. We can draw a 2-cell either as a pasting diagram or a string diagram (the topological dual):

![img-4.jpeg](img-4.jpeg)

There is also an intermediate notion between a 2-computad and a 2-category: a structure in which the 2-cells can be composed, but the 1-cells cannot. We call this essentially algebraic structure an **implicit 2-category**. It consists of

- a 2-computad,
- 2-cell composition and identity operations (horizontal and vertical), and
- associativity, unit, and interchange laws.

In other words, it has 0-cells, 1-cells, 2-cells with composition, and equalities between compositions of 2-cells. The compositions of 2-cells can be drawn for example as follows:

![img-5.jpeg](img-5.jpeg)

²Street’s computads were later generalized to n- and ∞-computads by Burroni [Bur93] (who introduced them independently, calling them *polygraphs*), Batanin [Bat98, Bat02], and Makkai [HMZ08].

6

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

Equivalently, an implicit 2-category can be defined as a *strict* 2-category whose underlying 1-category is freely generated; the 1-cells of the implicit 2-category then being the *generating* 1-cells of this free category.

An implicit 2-category is already quite close to a bicategory, but one more detail is required. An implicit 2-category is called **representable**$^{3}$ if each string of compatible 1-cells is isomorphic to a single 1-cell. (It is sufficient to require this for binary and nullary strings.) This allows the 1-cells to be “composed”, where a “composite” 1-cell is defined up to isomorphism only.

![img-6.jpeg](img-6.jpeg)

![img-7.jpeg](img-7.jpeg)

In Section 2 we will show that the category of bicategories and pseudofunctors is equivalent to that of representable implicit 2-categories and implicit 2-category functors (homomorphisms of the essentially algebraic structure). This alternative definition of bicategory is appealing for several reasons. First of all, there are no coherence axioms. Secondly, there is no extraneous structure present that is not respected by isomorphism of bicategories; it is not possible to even express equality between compositions of 1-cells, which is conceptually clarifying.

Having considered the situation for 2-categories, we proceed to treat double categories in just the same way. A **double computad** is the sort of structure that generates a free double category: it has 0-cells, horizontal and vertical 1-cells, and 2-cells bordered by strings of compatible 1-cells. We can draw 2-cells in a double computad either as pasting diagrams or string diagrams (string diagrams for double categories are discussed in [Mye16]):

![img-8.jpeg](img-8.jpeg)

a.k.a.

![img-9.jpeg](img-9.jpeg)

An **implicit double category** is then a double computad with composition operations on 2-cells like in a double category, but *without* any composition of 1-cells (neither horizontal nor vertical). We can then define a **doubly weak double category** to be an implicit double category that is representable, i.e. every string of compatible 1-cells (horizontal or vertical) has a composite. Thus defined, doubly weak double categories are the algebras for a finitary monad on double computads.

*Remark 1.1.* Implicit structures are related to the *virtual* structures of [CS10] (generalized multicategories). For instance, a *virtual 2-category* is like an implicit 2-category but requires the targets of all 2-cells to be length-1 paths (and restricts compositions to those that preserve this property). A *virtual double category* likewise restricts the lower boundaries of 2-cells to be length-1 paths, but as with pseudo double categories, the vertical 1-cells compose strictly, breaking the horizontal/vertical symmetry.

$^{3}$This usage of “representable” traces back to the representable multicategories of [Her00].

DOUBLY WEAK DOUBLE CATEGORIES

7

In fact, after this paper was completed, we learned that Keisuke Hoshino has characterized virtual double categories, and also augmented virtual double categories [Kou20] (which also allow length-0 paths as lower boundaries), as implicit double categories with appropriate composition and decomposition operations.

Like implicit structures, virtual structures allow the characterization of weak structures without explicit coherence axioms, but there are two main differences. Firstly, in an implicit 2-category we can define composites simply in terms of isomorphisms internal to the structure, whereas in a virtual 2-category composites must be defined by way of universal properties (since an inverse of a many-to-one morphism would be a one-to-many morphism, which virtual structures do not have). Secondly, both representable implicit 2-categories and representable virtual 2-categories can be identified with bicategories; however, the maps of implicit 2-categories (using the definition of homomorphism that is automatic from the essentially algebraic presentation) correspond to pseudofunctors, whereas the maps of virtual 2-categories correspond to *lax* functors.

Moreover, virtual structures apparently cannot be used to define doubly weak double categories, since there does not seem to be a sensible notion of a double category that is both horizontally and vertically virtual.

1.3. **Other definitions.** The presentation outlined in Section 1.2 gives a monad on double computads whose algebras are doubly weak double categories (with chosen composites). But we may also describe the algebras of this monad more directly, without factoring through the intermediate step of implicit double categories: a doubly weak double category is a double computad equipped with 1-cell composition and identities (satisfying no axioms), plus a way of composing any formal diagram of 2-cells$^{4}$ along any way of composing up its boundaries, satisfying appropriate coherence axioms (see Corollary 5.7).

This is similar to Garner's definition of cubical bicategory as described above in Section 1.1; the only difference is that our definition uses a double computad, whereas the 2-cells in Garner's definition are all *squares*, i.e. the horizontal and vertical sources and targets are length-1 paths. Indeed, we will show that Garner's and Verity's definitions both can be derived from ours by simply ignoring some of the structure of a double computad.

More precisely, the forgetful functor from doubly weak double categories to *double graphs* (double computads consisting of only 0-cells, 1-cells, and squares) induces a monad whose algebras are precisely Garner's cubical bicategories. Likewise, the forgetful functor to *double graphs with bigons* (double computads consisting of only 0-cells, 1-cells, squares, and horizontal and vertical bigons$^{5}$) induces a monad whose algebras are precisely Verity's double bicategories.

In particular, our doubly weak double categories are *not* monadic over double graphs or double graphs with bigons; additional shapes featured in a double computad are necessary. (This is perhaps surprising, since bicategories *are* monadic over 2-graphs, a.k.a. 2-globular sets.) However, these forgetful functors are 'the

$^{4}$Here we refer only to formal diagrams that 'ought to be composable in a double category'. There are other formal diagrams, such as 'pinwheels' [DP93, Daw95], that are not even composable in a strict double category, and these are not composable in our doubly weak double categories either. (Although one can also consider (strict or weak) double categories in which such diagrams are composable, e.g. [LR25].)

$^{5}$By a 'bigon' we mean a globular 2-cell, having two opposite boundary paths of length 1 and the other two opposite paths of length 0.

8

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

next best thing” to monadic: they are “of descent type”, which in this case means that the comparison functors from doubly weak double categories to double bicategories *and* to cubical bicategories are fully faithful. Thus we can indeed describe a doubly weak double category as *structure* on a double graph with bigons, or on a double graph, though these structures are not monadic.

We refer to the resulting equivalent notions of doubly weak double category respectively as *tidy double bicategories* and *tidy cubical bicategories*. Tidiness in both cases is a similar condition: it says that the operations of composing a square or bigon with an identity square are bijections. As noted above, tidiness for double bicategories is not a new condition; it already appeared without a name in Verity’s thesis [Ver92, Lemma 1.4.9], and in [RvdWAN25] it is called *saturation*. Our general theory shows that this apparently *ad hoc* condition does indeed yield a “correct” definition, in any reasonable sense.

With that said, an advantage of tidy double bicategories is that they yield an entirely *finite* presentation of doubly weak double categories, which we will show can be reduced to a double graph with binary composition and identity operations, and associator and unitor coherence squares, and appropriate axioms. This is perhaps the simplest definition, and the most amenable to checking all the pieces by hand in an example.

Finally, we give one last equivalent finite presentation, exhibiting doubly weak double categories as *monadic* over the category of double computads containing only 0-cells, 1-cells, squares, and all four kinds of *monogons*.

1.4. **Outline.** The structure of the paper is as follows. In Section 2, we spell out in detail the correspondence between bicategories and representable implicit 2-categories, using a quick definition of implicit 2-categories as strict 2-categories with free underlying 1-category. Then in Section 3, we by analogy quickly define implicit double categories, doubly weak double categories, and pseudofunctors between them, and give some examples (one with proofs postponed to Appendix A).

Then we move on to the computadic definitions. In Section 4, we introduce double computads. In Section 5, we present implicit structures, weak structures, and strict structures as monads on computads. And in Section 6, we upgrade the categories of implicit and weak structures to 2-categories, upgrade the monads to 2-monads, and prove coherence theorems.

Finally we consider alternative definitions and finite presentations: we discuss tidy double bicategories in Section 7, tidy cubical bicategories in Section 8, and monogons in Section 9.

1.5. **Acknowledgments.** We are grateful to Nathanael Arkor for a careful reading and several helpful suggestions and to Bob Paré for helpful discussions.

## 2. BICATEGORIES

We first spell out the equivalence between bicategories and representable implicit 2-categories, alluded to in the introduction (Section 1.2). Although it is helpful to view implicit 2-categories as *prior* to 2-categories, to get the main ideas across as quickly as possible, we start with a definition of implicit 2-categories in terms of strict 2-categories. Later we will give an alternative definition without reference to strict 2-categories, and describe 2-categories as extra structure on top of it.

DOUBLY WEAK DOUBLE CATEGORIES

9

**Definition 2.1.** An **implicit 2-category** is a strict 2-category whose category of 1-cells is free (i.e. freely generated by a directed graph).

We call the generating 1-cells simply **1-cells**, and we do not use this word for their compositions, which we rather call **paths of 1-cells**. The arrows and strings in our pasting diagrams and string diagrams always refer to generating 1-cells, and we draw these arrows with a distinguished arrowhead $\longrightarrow$. We call a 2-cell whose source and target are both length 1 paths a **bigon**.

A **functor** of implicit 2-categories is a strict 2-functor *that sends 1-cells to 1-cells*. We write **I-2-Cat** for the category of implicit 2-categories and such functors.

For clarity, we may call the strict 2-category associated to an implicit 2-category its **path 2-category**. (1-cells in the path 2-category are paths of 1-cells in the implicit 2-category.)

When a path of 1-cells is isomorphic to a single 1-cell, we call the latter a **composite** of the path. We call an implicit 2-category **representable** if each path of 1-cells has a composite.

![img-10.jpeg](img-10.jpeg)

**Remark 2.2.** An implicit 2-category with one 0-cell and one 1-cell is known elsewhere as a **PRO**; an implicit 2-category with one 0-cell (which we might call an “implicit monoidal category”) is often called a **colored PRO**.

The result to be shown, that bicategories are equivalent to representable implicit 2-categories, specializes to that monoidal categories are equivalent to representable colored PROs.

**Definition 2.3.** An implicit 2-category is **represented** if it has a *chosen* isomorphism between each length 2 or 0 path of 1-cells and a composite 1-cell.

It follows that every path of 1-cells has a composite (i.e. represented implies representable). We denote the chosen composite of 1-cells $f: A \rightarrow B$ and $g: B \rightarrow C$ by $fg: A \rightarrow C$ and we denote the chosen nullary composite at the 0-cell $A$ by $1_A: A \rightarrow A$. A functor between represented implicit 2-categories is called **strict** if it preserves the chosen composition isomorphisms.

**Remark 2.4.** One could alternatively suppose a chosen composition isomorphism for *every* path of 1-cells, instead of just binary and nullary paths. This would be equivalent to an *unbiased* bicategory.

To translate from bicategories to represented implicit 2-categories is the construction known as *strictification*. (Strictification of bicategories is typically described as a functor **W-2-Cat** $\rightarrow$ **2-Cat**, but it may be described slightly more precisely as a functor **W-2-Cat** $\rightarrow$ **I-2-Cat**.) For proof that this indeed defines a functor, we refer to e.g. [Gur13, Chapter 2];$^{6}$ showing this from the definitions below amounts to a series of straightforward verifications.

By a *bracketing* of a path of 1-cells in a bicategory, we mean a single 1-cell produced from the path by composing and introducing units. For example, a path

$^{6}$The definition of strictification in [Gur13] makes choices of parenthesizations whereas we use “cliques” of parenthesizations following [nLa25]; this makes no essential difference but we find the presentation with cliques helpful.

10

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

$f, g, h$ could be bracketed as $(fg)h$, $(f1)(gh)$, $((fg)h)(11)$, or infinitely many other ways. By the coherence theorem for bicategories, for any two bracketings of a path of 1-cells there is a canonical rebracketing isomorphism between them built from coherence isomorphism.

**Proposition 2.5.** Given a bicategory $\mathcal{C}$, the following data amount to a represented implicit 2-category:

- The 0-cells and 1-cells are as in $\mathcal{C}$.
- A 2-cell from $s_1, \ldots, s_m$ to $t_1, \ldots, t_n$ is a family consisting of a 2-cell in $\mathcal{B}$ for every possible bracketing of the source and target, such that these 2-cells are related by composing with the appropriate rebracketing coherence isomorphisms (a.k.a. a clique morphism).
- Composition of 2-cells (including identities) is induced by composition of 2-cells in $\mathcal{C}$.
- The composition isomorphisms are given by identities.

Proof. The coherence theorem for bicategories guarantees that each 2-cell from a bracketed form of $s_1 \cdots s_m$ to a bracketed form of $t_1 \cdots t_n$ determines, by composing with coherence isomorphisms, a unique corresponding 2-cell for every rebracketing of the source and target. Thus composition is well-defined, since rebracketing then composing 2-cells is the same as composing then rebracketing as appropriate. The axioms follow from coherence and the bicategory axioms. □

We call this the “underlying implicit 2-category” of a bicategory. Similarly, using coherence for pseudofunctors, we have:

**Proposition 2.6.** A pseudofunctor between bicategories $\mathcal{F}: \mathcal{C} \to \mathcal{D}$ induces a functor (not necessarily preserving chosen composition isomorphisms) between the underlying implicit 2-categories as follows:

- The maps of 0-cells and 1-cells are as in $\mathcal{F}$.
- The map on 2-cells is by applying $\mathcal{F}$ and composing with pseudofunctor coherence isomorphisms. (2-cells in $\mathcal{C}$ between $\mathcal{C}$-bracketed paths of 1-cells map to 2-cells in $\mathcal{D}$ between $\mathcal{D}$-bracketed paths of corresponding 1-cells.)

Moreover, this defines a functor $\mathbf{W}$-2-Cat $\to$ I-2-Cat. □

Next we see this functor $\mathbf{W}$-2-Cat $\to$ I-2-Cat is fully faithful, and its image consists of the representable implicit 2-categories.

**Proposition 2.7.** Given a represented implicit 2-category $\mathbf{C}$, the following data amount to a bicategory:

- The 0-cells are the 0-cells in $\mathbf{C}$.
- The category $\operatorname{Hom}(A, B)$ is the category of bigons between $A$ and $B$ in $\mathbf{C}$.
- Composition and identity for 1-cells is as in $\mathbf{C}$.
- Horizontal composition of 2-cells is by horizontally composing bigons in $\mathbf{C}$, and converting to a bigon (by vertically composing with composition

DOUBLY WEAK DOUBLE CATEGORIES

11

isomorphisms):

![img-11.jpeg](img-11.jpeg)

![img-12.jpeg](img-12.jpeg)

- The components of left and right unitors and associators are induced by the composition isomorphisms (by de-composing then re-composing):

![img-13.jpeg](img-13.jpeg)

![img-14.jpeg](img-14.jpeg)

![img-15.jpeg](img-15.jpeg)

![img-16.jpeg](img-16.jpeg)

Proof. Functoriality, naturality, pentagon, and triangle follow from composition isomorphisms cancelling with their inverses. □

We call this the “underlying bicategory” of a represented implicit 2-category.

**Proposition 2.8.** A functor between represented implicit 2-categories $F: \mathbf{C} \rightarrow \mathbf{D}$ (not necessarily preserving the chosen composition isomorphisms) induces a pseudofunctor between the underlying bicategories as follows:

- The functor is $F$ on 0-cells, 1-cells, and 2-cells (bigons).
- The coherence isomorphisms $1_{FA} \rightarrow F1_A$ and $(Ff)(Fg) \rightarrow F(fg)$ are built from the chosen composition isomorphisms (by de-composing in $\mathbf{D}$ and re-composing in $\mathbf{C}$):

![img-17.jpeg](img-17.jpeg)

![img-18.jpeg](img-18.jpeg)

12

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

![img-19.jpeg](img-19.jpeg)

![img-20.jpeg](img-20.jpeg)

*Proof.* Naturality and coherence axioms follow from composition isomorphisms cancelling with their inverses. □

Any represented implicit 2-category is canonically identified with the underlying implicit 2-category of its underlying bicategory: by composing with chosen isomorphisms, the 2-cells with arbitrary boundary are in composition-respecting correspondence with bracketed bigons. Likewise, any implicit 2-category functor is recovered from its underlying pseudofunctor: the underlying implicit 2-category functor is defined in the same way on bigons and composition isomorphisms, and therefore on all 2-cells. Hence, we obtain:

**Proposition 2.9.** *The category of bicategories (and pseudofunctors) is equivalent to the category of representable implicit 2-categories (and implicit 2-category functors).* □

Moreover, by construction, a pseudofunctor having identities as the coherence isomorphisms corresponds to an implicit 2-category functor preserving chosen composition isomorphisms on the nose, so we also obtain:

**Corollary 2.10.** *The category of bicategories and strict functors is equivalent to the category of represented implicit 2-categories and strict functors (functors that preserve the chosen composition isomorphisms).* □

*Remark 2.11.* Other characterizations of implicit 2-categories as structure on 2-categories are as follows: they are the flexible algebras of the strict 2-category 2-monad on **Cat**-enriched graphs (this can be deduced from [Lac02b, Theorem 4.8]); they are also the “pie” algebras of this 2-monad in the terminology of [BG13]; and they are the cofibrant objects in the canonical model structure on 2-categories from [Lac02b, Lac04]. Moreover the evident (path 2-category) functor **I-2-Cat** → **2-Cat** is comonadic, as shown in [Had21, Proposition 2.5]. In particular, pseudofunctors are *weak maps* of 2-categories in the sense of [Gar10b, BG16].

We also note that results analogous to those in this section appear in [Had19, Section 5] about a structure similar to an implicit 2-category, except not allowing 2-cells with nullary inputs or outputs or parallel composition, and with a different treatment of nullary composites. Results similar to our Appendix A (in which we discuss transformations and modifications) are covered there as well in the same context.

### 3. DOUBLY WEAK DOUBLE CATEGORIES

Now we quickly define doubly weak double categories, using strict double categories by analogy to Section 2. (Later in Section 4 and Section 5 we will use a more systematic approach, building the essentially algebraic implicit structures from the ground up.)

DOUBLY WEAK DOUBLE CATEGORIES

13

**Definition 3.1.** An **implicit double category** is a strict double category whose horizontal and vertical categories of 1-cells are free (i.e. each is freely generated by a directed graph).

We call the generating 1-cells simply **1-cells**, and we do not use this word for their compositions, which we rather call **paths of 1-cells**. (In particular, a length zero path of 1-cells consists of an object.) The arrows and strings shown in our pasting diagrams and string diagrams always refer to 1-cells.

We call a 2-cell whose horizontal and vertical sources and targets are all length 1 paths a **square**. If its horizontal sources and targets are length 1 and its vertical ones are length 0, we call it a **horizontal bigon**; dually we have **vertical bigons**.

A **functor** of implicit double categories is a strict double functor *that moreover sends 1-cells to 1-cells*. We write **IDblCat** for the category of implicit double categories and such functors.

When a path of 1-cells (horizontal or vertical) is isomorphic to a single 1-cell, we call the latter a **composite** of the path.

**Definition 3.2.** A **doubly weak double category** is an implicit double category in which each path of 1-cells (horizontal or vertical) has a composite.

We also use the adjective **representable** to describe such implicit double categories. We write **WDblCat** for this full subcategory of **IDblCat**.

We will often additionally assume our doubly weak double categories are equipped with specific choices of composites, just as it is customary to assume bicategories are equipped with specific choices of composites:

**Definition 3.3.** An implicit double category is **represented** when it is equipped with a *chosen* isomorphism between each horizontal or vertical length 2 or 0 path of 1-cells and a single composite 1-cell. It follows that every path of 1-cells has a composite (i.e. represented implies representable). We will refer to this too as simply a **doubly weak double category** where it is clear from context that we intend to have chosen composites.

We denote the chosen composite of 1-cells $f: A \rightarrow B$ and $g: B \rightarrow C$ by $fg: A \rightarrow C$ (diagrammatic order). We denote the chosen nullary composite at the 0-cell $A$ by $1_A: A \rightarrow A$ (and it will be clear from context whether we mean the horizontal or vertical one).

A functor between doubly weak double categories is **horizontally strict** if it preserves chosen horizontal composition isomorphisms. Similarly, it is **vertically strict** if it preserves chosen vertical composition isomorphisms, and it is simply **strict** if it preserves both. We denote by **WDblCat$_{st}$** the category of doubly weak double categories and strict functors.

*Remark 3.4.* One could give an alternative definition that supposes a chosen composition isomorphism for every path of 1-cells, instead of just binary and nullary paths. This would provide an *unbiased* definition of doubly weak double category, analogous to unbiased definitions of monoidal category or bicategory.

*Remark 3.5.* Just as every strict double category has underlying horizontal and vertical strict 2-categories (comprising the 2-cells that are respectively vertically and horizontally degenerate), every implicit double category has underlying horizontal and vertical implicit 2-categories. Note that if an implicit double category is

14

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

representable, then so are its underlying implicit 2-categories. Hence every doubly weak double category has underlying horizontal and vertical bicategories.

*Example 3.6.* In the other direction, just as every strict 2-category has an associated double category of squares — a.k.a. the quintet construction — every implicit 2-category has an associated implicit double category. (Indeed, if a strict 2-category has a free underlying 1-category, then its strict double category of quintets also has free underlying 1-categories.) If an implicit 2-category is representable, then so is its associated implicit double category. Hence every bicategory has an associated doubly weak double category of squares/quintets.

*Example 3.7.* Let $X$ be a topological space. There is an associated doubly weak double category, the *fundamental (doubly weak) double groupoid* of $X$. The 0-cells are points, 1-cells are continuous paths$^{7}$ $p : [0,1] \rightarrow X$, and the 2-cells with a given boundary loop correspond to relative homotopy classes of disks with that boundary. More precisely, given the boundary of a 2-cell, we compose each of the four sequences of paths to get a single path defined on $[0,1]$, and then a 2-cell with that boundary is a homotopy class of continuous maps $[0,1] \times [0,1] \rightarrow X$ relative to those four paths as the boundary. (Composing an empty sequence of paths yields a constant path.) Composing 2-cells is done as usual, plus we have to compose with reparametrizing homotopies to make the boundaries correct. Later we will construct this example in a more finitary way, in terms of composition of square 2-cells only, in Example 7.23.

Note that a doubly weak double category is more directly fitted to describing this structure than a strict double category (as in [BHKP02]), since composition of paths in a topological space is not strictly associative. Note also that although this example can be seen as a special case of squares in a bicategory, describing the composition of squares in a topological space is arguably simpler than describing the composition of 2-cells of globular shape (bigons), as discussed in [BHKP02].

*Example 3.8.* Given any strict double category, for each symmetry of the square we obtain a related strict double category. In particular, we obtain the *horizontal opposite* by interchanging the horizontal sources and targets of cells, the *vertical opposite* by interchanging the vertical sources and targets of cells, and the *transpose* by interchanging horizontal and vertical cells. Likewise, implicit double categories and doubly weak double categories are closed under these constructions. This makes the theory symmetric, so that any concept defined for horizontal arrows also makes sense for vertical arrows and vice versa.

In contrast, the traditional notion of (singly) weak double category, a.k.a. pseudo double category [GP99], is asymmetric: it has strict composition in one direction but weak composition in the other. Hence traditionally, a weak double category has no transpose. However, as we will see soon in Proposition 3.13, a pseudo double category is a special case of a doubly weak double category, so its transpose exists in the form of another doubly weak double category.

*Example 3.9.* Suppose $F : \mathbf{C} \rightarrow \mathbf{D}$ is a functor of implicit 2-categories that is bijective on objects. Then there is an implicit double category whose horizontal 1-cells are those of $\mathbf{D}$, whose vertical 1-cells are those of $\mathbf{C}$, and whose 2-cells are

$^{7}$In this example we use “path” with the topological meaning, rather than the categorical one of Definition 3.1.

DOUBLY WEAK DOUBLE CATEGORIES

15

those of $\mathbf{D}$ with $F$ applied to their vertical boundaries. Indeed, this construction can be performed on strict 2-categories and strict double categories, and preserves freeness of 1-cells. And if $\mathbf{C}$ and $\mathbf{D}$ are representable, so is the resulting implicit double category.

In particular, a **(proarrow) equipment** [Woo82, Woo85] is a bijective on objects and locally full and faithful pseudofunctor of bicategories $\mathcal{C} \rightarrow \mathcal{D}$ such that every 1-cell in the image is a left adjoint. This serves as an abstraction of e.g.

- • sets, functions, and relations;
- • rings, homomorphisms, and bimodules; and
- • categories, functors, and profunctors.

Thus, any proarrow equipment gives rise to a doubly weak double category. Analogous results were shown in [Ver92] using double bicategories, and in [Shu08] using pseudo double categories which requires $\mathcal{C}$ to be a strict 2-category. As in the latter case, the doubly weak double categories arising from equipments can be characterized as those where each vertical 1-cell has a horizontal *companion* and *conjoint*.

*Example 3.10.* For any strict 2-category $\mathcal{C}$, there are two double categories $\mathbf{Adj}(\mathcal{C})$ and $\mathbf{Adj}'(\mathcal{C})$ both of whose objects and horizontal 1-cells are those of $\mathcal{C}$ and both of whose vertical 1-cells are adjunctions $f^* \rightharpoonup f_*$ in $\mathcal{C}$ pointing in the direction of the left adjoint. The 2-cells in the two cases are as shown below, one involving the left adjoints and the other the right adjoints:

The *mates correspondence* [KS74] then yields an isomorphism $\mathbf{Adj}(\mathcal{C}) \cong \mathbf{Adj}'(\mathcal{C})$ that is the identity on 0-cells and 1-cells.

If instead $\mathbf{C}$ is an implicit 2-category, we have implicit double categories $\mathbf{Adj}(\mathbf{C})$ and $\mathbf{Adj}'(\mathbf{C})$ and an isomorphism between them defined in the same way, using the fact that adjunctions in a 2-category compose. And, if $\mathbf{C}$ is representable, so are $\mathbf{Adj}(\mathbf{C})$ and $\mathbf{Adj}'(\mathbf{C})$. Thus, we obtain a formalization of the mates correspondence for bicategories using double weak double categories.

*Example 3.11.* In Appendix A, we will show that for any two bicategories $\mathcal{C}$ and $\mathcal{D}$, there is a doubly weak double category $\mathrm{Hom}_{\mathrm{co/lax}}(\mathcal{C}, \mathcal{D})$ in which the objects are functors from $\mathcal{C}$ to $\mathcal{D}$, the horizontal and vertical 1-cells are lax and colax transformations, and the 2-cells are an appropriate kind of modification. More generally, for any two implicit 2-categories $\mathbf{C}$ and $\mathbf{D}$, there is an implicit double category $\mathrm{Hom}_{\mathrm{co/lax}}(\mathbf{C}, \mathbf{D})$, which is representable if $\mathbf{D}$ is.

Special cases of this general construction produce more examples. Taking $\mathbf{C}$ to be freely generated by a 1-cell, we obtain a doubly weak double category where the 1-cells are lax and colax squares in the bicategory $\mathcal{D}$. Taking $\mathbf{C}$ to be freely generated by a monad, we obtain a doubly weak double category of monads in $\mathcal{D}$, where the 1-cells are lax and colax monad maps.

**Definition 3.12.** A doubly weak double category is **horizontally strict** if its underlying horizontal bicategory is a strict 2-category.

16

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

Equivalently, for all horizontal $f: A \rightarrow B$, $g: B \rightarrow C$, and $h: A \rightarrow B$, we have $(fg)h = f(gh)$ and $1_A f = f = f1_B$, and likewise

![img-21.jpeg](img-21.jpeg)

Similarly, it is **vertically strict** if its underlying vertical bicategory is strict, and it is **strict** if it is both horizontally and vertically strict.

**Proposition 3.13.** *The category of vertically strict doubly weak double categories and vertically strict functors (resp. strict functors) is equivalent to the category of pseudo double categories and pseudofunctors (resp. strict functors).*

*Proof.* The proof follows the same blueprint as Proposition 2.9, which we walk through again in this case.

Every pseudo double category $\mathcal{C}$ has an underlying vertically strict doubly weak double category with the same 0-cells and 1-cells, and where a 2-cell with any boundary is a family consisting of a choice of square in $\mathcal{C}$ for every possible bracketing of the source and target in the weak (horizontal) direction, such that these squares are related by composing with the relevant coherence isomorphisms (a.k.a. a *clique morphism*). Composition is as in $\mathcal{C}$, and composition isomorphisms are given by identities, as in Proposition 2.5.

Likewise every pseudo double functor $\mathcal{F}$ has an underlying vertically strict functor of implicit double categories, defined as $\mathcal{F}$ on 0-cells and 1-cells, and with the map on 2-cells induced by composing with pseudofunctor coherence isomorphisms, as in Proposition 2.6. (Note that coherence for pseudofunctors of bicategories applies just as well here, since a pseudo double functor in particular includes pseudofunctors between underlying bicategories.)

Conversely, every vertically strict doubly weak double category $\mathbf{C}$ has an underlying pseudo double category with the same 0-cells, 1-cells, and *square* 2-cells (those bordered by length one paths), and with identities and compositions derived from those in $\mathbf{C}$:

![img-22.jpeg](img-22.jpeg)

![img-23.jpeg](img-23.jpeg)

DOUBLY WEAK DOUBLE CATEGORIES

17

![img-24.jpeg](img-24.jpeg)

(There are analogous diagrams for vertical identities and compositions.) The coherence data are built from the chosen composition isomorphisms just as in Proposition 2.7.

Likewise every vertically strict functor $F$ between vertically strict doubly weak double categories has an underlying pseudo double functor (see [GP99] for a precise definition of pseudo double functor), defined as $F$ on all cells, and with coherence data built from the chosen composition isomorphisms, just as in Proposition 2.8.

That these assignments constitute an equivalence of categories, as in Proposition 2.9, is a series of straightforward verifications. Moreover, strict functors of doubly weak double categories correspond to strict functors of pseudo double categories because preservation of chosen composition isomorphisms amounts to triviality of coherence isomorphisms, as in Corollary 2.10. $\square$

**Corollary 3.14.** *The category of strict doubly weak double categories and strict functors is equivalent to the category of strict double categories.* $\square$

*Remark 3.15.* Keisuke Hoshino has shown that there is an analogue of Remark 2.11 for double categories as well. That is, the category of implicit double categories is comonadic over that of strict double categories, with the comonad being a cofibrant replacement; thus double pseudofunctors are the *weak maps* of double categories in the sense of [Gar10b, BG16].

#### 4. DOUBLE COMPUTADS

We next embark on a more algebraic treatment of implicit and doubly weak double categories, starting with the definition of double computads. For comparison and later use, we first recall some details about computads for 1-categories and 2-categories. By a **1-computad** we will mean simply a directed (multi)graph, a.k.a. quiver. The category **1-Cptd** of 1-computads is a functor category $[\mathbb{C}_1, \mathbf{Set}]$ with domain $\mathbb{C}_1$ given by the category

$$1 \Rightarrow 0.$$

The category **1-Cat** of (small) 1-categories is monadic over 1-computads, via an adjunction which we write

$$\text{1-Cptd} \xleftarrow[\mathcal{U}_1]{\mathcal{F}_1} \text{1-Cat}$$

with induced monad $T_1 = \mathcal{U}_1\mathcal{F}_1$. When $X$ is a 1-computad, the 0-cells in $T_1X$ are the same as in $X$, and the 1-cells in $T_1X$ are paths in $X$. We denote by $\Rightarrow$ the 1-computad containing two objects and two parallel arrows between them.

**Definition 4.1.** A **2-computad** consists of a 1-computad $X_{\leq 1}$, together with a set $X_2$ of 2-cells and a function $\partial$ sending each 2-cell to a parallel pair of paths in

18

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

![img-25.jpeg](img-25.jpeg)

FIGURE 1.  \( C_{2} \)  consists of the “shapes of cell” in a 2-computad.

\(X_{\leq 1}\) (its boundary):

\[
\partial \colon X _ {2} \longrightarrow 1 - \mathbf {C p t d} (\Rightarrow , T _ {1} X _ {\leq 1}).
\]

We denote by 2-Cptd the category of 2-computads, defined as the comma category of Set over 1-Cptd( \( \Rightarrow T_{1}- \) ).

The following theorem allows us to quickly deduce that 2-Cptd is itself a presheaf category. \( ^{8} \)  Recall that a functor  \( G: C \to D \)  is a parametric right adjoint if C has a terminal object 1 and the induced  \( \widetilde{G}: C \to D/G1 \)  has a left adjoint.

Theorem 4.2 ([CJ95]). Given a functor between presheaf categories \( G \colon [\mathbb{C}, \mathbf{Set}] \to [\mathbb{D}, \mathbf{Set}] \), the comma category (a.k.a. Artin gluing) ([D, Set]/G) is again a presheaf category [E, Set] if and only if \( G \colon [\mathbb{C}, \mathbf{Set}] \to [\mathbb{D}, \mathbf{Set}] \) is a parametric right adjoint.

For functors between well-behaved categories such as presheaf categories  \( C = [C, Set] \)  and  \( D = [D, Set] \) , parametric right adjoints are equivalently the functors preserving connected limits. When moreover D = Set, parametric right adjoints are simply coproducts of representable functors.

Indeed, \( T_{1} \) and 1-Cptd(\( \Rightarrow \), -) are both parametric right adjoints, thus so is their composite; hence by Theorem 4.2 there is a category \( \mathbb{C}_2 \) such that 2-Cptd \( \cong [\mathbb{C}_2, \mathbf{Set}] \). Moreover the proof of this theorem in [CJ95] tells us how to explicitly describe the domain category, giving us the definition of \( \mathbb{C}_2 \) written below and shown graphically in Figure 1. (It is also not difficult to verify directly from the definition that functors \( \mathbb{C}_2 \to \mathbf{Set} \) are identified with 2-computads.)

The category \(\mathbb{C}_2\) has objects 0, 1, and \(2_{n}^{m}\) for natural numbers \(m, n \in \mathbb{N}\), and the morphisms are as follows:

- The full subcategory of objects 0 and 1 is \(\mathbb{C}_1\).
- The only arrows into the objects \(2_{n}^{m}\) are identities.
- For each \(m, n \in \mathbb{N}\), the homsets from \(2_{n}^{m}\) into 0 and 1, acted on by composing arrows in \(\mathbb{C}_1\), determine the 1-computad representing a pair of parallel paths of lengths \(m\) and \(n\):

![img-26.jpeg](img-26.jpeg)

\( ^{8} \) This fact was apparently first observed by Schanuel, as mentioned in [CJ95].

DOUBLY WEAK DOUBLE CATEGORIES

19

As in Section 2, we refer to 2-cells of shape \(2_{1}^{1}\) as bigons:

A 2-computad in which all 2-cells are bigons is called a 2-graph (a.k.a. 2-globular set). We denote this full subcategory of 2-Cptd by 2-Gph, also a functor category with domain a full subcategory of \(\mathbb{C}_2\):

\[
2 \Rightarrow 1 \Rightarrow 0.
\]

(composition laws as in \(\mathbb{C}_2\), where \(2 := 2_1^1\)).

The category 2-Gph is also a comma category (Set/1-Cptd( \( \Rightarrow \) , -)), so we have a functor from 2-Cptd = (Set/1-Cptd( \( \Rightarrow \) ,  \( T_{1}- \) )) to 2-Gph given by applying  \( T_{1} \)  to the 1-cells, which reinterprets all of the 2-cells in a 2-computad as bigons between paths.

![img-27.jpeg](img-27.jpeg)

This is more precisely a functor  \( \iota_{2} \) : 2-Cptd → 1-Cat-2-Gph where the codomain is 2-graphs equipped with 1-category structure on 1-cells. Note that this category 1-Cat-2-Gph is evidently monadic over 2-Gph.

The functor  \( \iota_{2} \)  is pseudomonic; its image consists of 2-graphs equipped with free 1-category structure and maps sending generating 1-cells to generating 1-cells. Thus 2-computads are equivalently such structured 2-graphs.

The category 2-Cat of (small, strict) 2-categories is also monadic over 2-Gph, essentially by definition (as a 2-graph equipped with various operations). The forgetful right adjoint evidently factors through an intermediate right adjoint 2-Cat → 1-Cat-2-Gph, which is also monadic by the following lemma.

Lemma 4.3 ([Bou92, Propositions 4 and 5]). If \( G_{3} = G_{2} \circ G_{1} \), where \( G_{2} \) and \( G_{3} \) are monadic and all three functors have left adjoints, then \( G_{1} \) is also monadic.

In the next section we will see that 2-Cat is monadic over 2-Cptd as well, but this is less straightforward. (Street [Str76] asserted this by a monadicity theorem, but it seems nontrivial to verify the hypotheses.)

It is time to move on to double computads. Here the roles of 1-computads and 1-categories are played by structures which we call  \( 1 \vee 1 \) -computads and  \( 1 \vee 1 \) -categories; these are like double categories but without any 2-cells.

Definition 4.4. A \(1 \vee 1\)-computad \(X\) consists of two 1-computads (directed graphs) with the same set of 0-cells (vertices) \(X_0\). We refer to the two kinds of 1-cell as horizontal and vertical and draw them accordingly. The category \(1 \vee 1\)-Cptd of \(1 \vee 1\)-computads is a functor category \([\mathbb{C}_{1 \vee 1}, \mathbf{Set}]\), with domain \(\mathbb{C}_{1 \vee 1}\) given by the category

\[
1 ^ {H} \Rightarrow 0 \Leftarrow 1 ^ {V}.
\]

Remark 4.5. This category \(\mathbb{C}_{1\vee 1}\) is the category of elements of the 1-computad \(A\colon \mathbb{C}_1\to \mathbf{Set}\) defined by \(A(0) = \{0\}\) and \(A(1) = \{1^{H},1^{V}\}\). Thus we can also write \(1\vee 1\text{-}\mathbf{Cptd} = 1\text{-}\mathbf{Cptd} / A\). There are hence projection functors

\[
\Diamond \colon \mathbb {C} _ {1 \vee 1} \to \mathbb {C} _ {1} \qquad \text { and } \qquad \Diamond_ {!} \colon 1 \vee 1 \text {- - Cptd} \to 1 \text {- - Cptd}
\]

20

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

which forget the distinction between horizontal and vertical arrows.

Similarly, a 1∨1-category consists of two categories with the same set of objects; 1∨1-categories are monadic over 1∨1-computads via an adjunction

$$1 \vee 1\text{-Cptd} \xrightarrow[\mathcal{U}_{1 \vee 1}]{\mathcal{F}_{1 \vee 1}} 1 \vee 1\text{-Cat}$$

with induced monad $T_{1 \vee 1}$. Let $\square$ denote the 1∨1-computad with four objects and two arrows of each sort, forming a square:

Definition 4.6. A double computad consists of a 1∨1-computad $X_{\leq 1}$, together with a set $X_2$ of 2-cells and a function $\partial$ sending each 2-cell to a square of paths in $X_{\leq 1}$ (its boundary):

$$\partial: X_2 \longrightarrow 1 \vee 1\text{-Cptd}(\square, T_{1 \vee 1} X_{\leq 1}).$$

We write DblCptd for the category of double computads, the comma category of Set over 1∨1-Cptd($\square$, $T_{1 \vee 1}$—).

Like $T_1$, the monad $T_{1 \vee 1}$ is a parametric right adjoint. Thus, by Theorem 4.2, DblCptd is also a functor category $[\mathbb{C}_d, \mathbf{Set}]$. We describe $\mathbb{C}_d$ by the same process we used to describe $\mathbb{C}_2$. We find that the objects are $0, 1^H, 1^V$, and $2_{c,d}^{a,b}$ for natural numbers $a, b, c, d \in \mathbb{N}$, and the morphisms are as follows:

- The full subcategory of objects $0, 1^H$, and $1^V$ is $\mathbb{C}_{1 \vee 1}$.
- The only arrows into the objects $2_{c,d}^{a,b}$ are identities.
- For $a, b, c, d \in \mathbb{N}$, the homsets from $2_{c,d}^{a,b}$ into $0, 1^H$, and $1^V$, acted on by composing arrows in $\mathbb{C}_d$, determine the 1∨1-computad representing a square of paths of lengths $a$ (top), $b$ (right), $c$ (left), and $d$ (bottom):

![img-28.jpeg](img-28.jpeg)

Remark 4.7. We also have that $\mathbb{C}_d$ is the category of elements of a certain 2-computad $B: \mathbb{C}_2 \to \mathbf{Set}$, which we can see in the following way.

Composing $\diamond_!: 1 \vee 1\text{-Cptd} \to 1\text{-Cptd}$ from Remark 4.5 with $1\text{-Cptd}(\Rightarrow, T_1-) : 1\text{-Cptd} \to \mathbf{Set}$ yields a functor $1 \vee 1\text{-Cptd} \to \mathbf{Set}$, which sends a 1∨1-computad to the set of pairs of parallel paths of 1-cells of either sort. We also have the functor $1 \vee 1\text{-Cptd}(\square, T_{1 \vee 1}-)$, which sends a 1∨1-computad to the set of parallel pairs of paths where the first consists of horizontal 1-cells followed by vertical 1-cells and the second consists of vertical 1-cells followed by horizontal 1-cells.

Forgetting this requirement on the pairs of paths yields a natural transformation $\alpha: 1 \vee 1\text{-Cptd}(\square, T_{1 \vee 1}-) \hookrightarrow 1\text{-Cptd}(\Rightarrow, T_1 \diamond_! -)$. This transformation is cartesian, i.e. its naturality squares are pullbacks. In this case, cartesianness

DOUBLY WEAK DOUBLE CATEGORIES

21

corresponds to the fact that whether an element of $1\text{-}\mathbf{Cptd}(\Rightarrow, T_1 \diamond! X)$ lifts to $1 \vee 1\text{-}\mathbf{Cptd}(\square, T_{1 \vee 1} X)$ is determined solely by its “shape”, i.e. the induced element of $1\text{-}\mathbf{Cptd}(\Rightarrow, T_1 \diamond! 1)$ (a pair of sequences of the values $1^H$ and $1^V$).

By the following lemma, we have $\mathbf{DblCptd} = 2\text{-}\mathbf{Cptd}/B$, where $B$ is the 2-computed in $1 \vee 1\text{-}\mathbf{Cptd} = 1\text{-}\mathbf{Cptd}/A$ corresponding to $\alpha_1: 1 \vee 1\text{-}\mathbf{Cptd}(\square, T_{1 \vee 1}1) \rightarrow 1\text{-}\mathbf{Cptd}(\Rightarrow, T_1 A)$.

**Lemma 4.8.** *If $\alpha$ is a cartesian natural transformation*

![img-29.jpeg](img-29.jpeg)

*then the comma category $(D/F)$ is a slice category of the comma category $(D/G)$. Namely, $(D/F) \cong (D/G)/\alpha_1$, the slice over the object $\alpha_1: F(1) \rightarrow G(c)$.*

*Proof.* Since $\alpha$ is cartesian, for any object $f: c' \rightarrow c$ of $C/c$ we have a pullback

$$\begin{array}{c} F(f) \xrightarrow{\alpha_f} G(c') \\ F(f) \downarrow \quad \downarrow \quad \downarrow G(f) \\ F(1) \xrightarrow{\alpha_1} G(c) \end{array}$$

Now, an object of the comma category $(D/F)$ consists of an object $d$ of $D$, an object $f: c' \rightarrow c$ of $C/c$, and an arrow $d \rightarrow F(f)$. By the universal property of the above pullback, to give such a $d \rightarrow F(f)$ is to give a commutative square

$$\begin{array}{c} d \longrightarrow G(c') \\ \downarrow \quad \downarrow G(f) \\ F(1) \xrightarrow{\alpha_1} G(c) \end{array}$$

And this is precisely an object of $(D/G)/\alpha_1$. The morphisms are also the same. $\square$

Explicitly, in this case we have $1 \vee 1\text{-}\mathbf{Cptd} = 1\text{-}\mathbf{Cptd}/B$ where $B: \mathbb{C}_2 \rightarrow \mathbf{Set}$ is defined by:

$$\begin{aligned} B(0) &= \{0\} \\ B(1) &= \{1^H, 1^V\} \\ B(2_n^m) &= \left\{2_{c,d}^{a,b} \mid a, b, c, d \in \mathbb{N},\ a+b=m,\ c+d=n\right\} \\ B(s_i)(2_{c,d}^{a,b}) &= \begin{cases} 1^H & \text{if } i \leq a \\ 1^V & \text{if } i > a \end{cases} \\ B(t_j)(2_{c,d}^{a,b}) &= \begin{cases} 1^V & \text{if } j \leq c \\ 1^H & \text{if } j > c \end{cases} \end{aligned}$$

(the action of all other arrows being trivial). The category $\mathbb{C}_d$ is the category of elements of this $B$.

22

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

*Remark 4.9.* We have a commutative diagram (moreover, a pullback square)

![img-30.jpeg](img-30.jpeg)

where each horizontal functor is the projection of a category of elements onto its domain, and the vertical functors are the obvious inclusions (each of which, incidentally, may also be viewed as projection of a category of elements onto its domain). We thereby obtain a similar diagram of functor categories:

![img-31.jpeg](img-31.jpeg)

Here $\blacklozenge^*$, $\diamond^*$, and both functors denoted $\tau$ are restrictions ($\tau$ means “truncation”); $\blacklozenge_!$, $\diamond_!$, and both functors denoted $\mathbf{sk}$ are left Kan extensions ($\mathbf{sk}$ means “skeleton”). We have the obvious commutativities $\diamond^*\tau \cong \tau\blacklozenge^*$ and $\mathbf{sk}\diamond_! \cong \blacklozenge_!\mathbf{sk}$, and the Beck-Chevalley property also holds, giving isomorphisms $\diamond_!\tau \cong \tau\blacklozenge_!$ and $\mathbf{sk}\diamond^* \cong \blacklozenge^*\mathbf{sk}$.

Viewing the left Kan extensions as slice category projections

$$\diamond_!: 1\text{-}\mathbf{Cptd}/A \rightarrow 1\text{-}\mathbf{Cptd} \quad \text{and} \quad \blacklozenge_!: 2\text{-}\mathbf{Cptd}/B \rightarrow 2\text{-}\mathbf{Cptd}$$

we have that the right adjoints $\diamond^*$ and $\blacklozenge^*$ are respectively given by product with $A$ and $B$ (pulling back $1\text{-}\mathbf{Cptd} = 1\text{-}\mathbf{Cptd}/1$ along $A \rightarrow 1$ and $2\text{-}\mathbf{Cptd} = 2\text{-}\mathbf{Cptd}/1$ along $B \rightarrow 1$). Explicitly, $\blacklozenge^*$ sends a 2-computed to a double computed whose 2-cells of shape $2_{c,d}^{a,b}$ are the 2-cells of shape $2_{c+d}^{a+b}$ therein (a.k.a. “quintets”).

![img-32.jpeg](img-32.jpeg)

We refer to 2-cells of shapes $2_{0,1}^{1,0}$, $2_{1,0}^{0,1}$, and $2_{1,1}^{1,1}$ in a double computed respectively as **horizontal bigons**, **vertical bigons**, and **squares**. We call a double computed in which all 2-cells are squares a **double graph**. We denote this full subcategory of **DblCptd** by **DblGph**, also a functor category with domain a full subcategory of $\mathbb{C}_d$:

![img-33.jpeg](img-33.jpeg)

(composition laws as in $\mathbb{C}_d$, where $2 := 2_{1,1}^{1,1}$).

DOUBLY WEAK DOUBLE CATEGORIES

23

The category **DblGph** is also a comma category (**Set**/1∨1-**Cptd**(□, −)). Hence we additionally have a functor from **DblCptd** = (**Set**/1∨1-**Cptd**(□, $T_{1\vee 1}$ −)) to **DblGph** by applying $T_{1\vee 1}$, which reinterprets all of the 2-cells in a double computad as squares of paths.

![img-34.jpeg](img-34.jpeg)

This is more precisely a functor $\iota_{\mathbf{d}}$: **DblCptd** $\rightarrow$ 1∨1-**CatDblGph** where the codomain is double graphs equipped with 1∨1-category structure on 1-cells. Note that this category 1∨1-**CatDblGph** is evidently monadic over **DblGph**.

The functor $\iota_{\mathbf{d}}$ is pseudomonic; its image consists of double graphs equipped with *free* 1∨1-category structure and maps sending generating 1-cells to generating 1-cells. Thus double computads are equivalently such structured double graphs.

The category **DblCat** of (small, strict) double categories is also monadic over **DblGph**, essentially by definition (as a double graph equipped with various operations). The forgetful right adjoint evidently factors through an intermediate right adjoint **DblCat** $\rightarrow$ 1∨1-**CatDblGph**, which is also monadic by **Lemma 4.3**. In the next section we will see that **DblCat** is monadic over **DblCptd** as well.

## 5. ALGEBRAIC DEFINITIONS

Now we are able to describe implicit 2-categories and implicit double categories (**Sections 2 and 3**) as algebras of monads on the presheaf categories 2-**Cptd** and **DblCptd** respectively, confirming their essentially algebraic nature.

In **Section 4**, we encountered several essentially algebraic structures presented by operations and equations (such as categories, strict 2-categories, and strict double categories), and we tacitly interpreted these as monads on presheaf categories. But we will soon need presentations of monads in more general situations, so we review a general method for presenting monads, following [Lac09, §5]. (Our definitions of implicit 2-categories and implicit double categories in this section will just be presentations of monads on presheaf categories as usual, but in **Section 6** we will also be interested in presenting 2-monads on non-presheaf categories.)

Let $\mathcal{V}$ be a locally finitely presentable (l.f.p.) monoidal category whose subcategory of finitely presentable objects $\mathcal{V}_f$ is closed under the monoidal structure, so we have a good theory of l.f.p. $\mathcal{V}$-enriched categories as in [Kel82b]; we will use $\mathcal{V} = \mathbf{Set}$ and $\mathcal{V} = \mathbf{Cat}$. Let $\mathcal{K}$ be an l.f.p. $\mathcal{V}$-category. Then by [Lac99], the category $\mathbf{Mnd}_f(\mathcal{K})$ of finitary monads on $\mathcal{K}$ is monadic over the category $[\mathrm{ob}\mathcal{K}_f, \mathcal{K}]$ of families of objects of $\mathcal{K}$ indexed by the set of finitely presentable objects of $\mathcal{K}$. Thus, we can *present* such monads using free monads generated by such families and colimits in $\mathbf{Mnd}_f(\mathcal{K})$; and because these free monads and colimits are *algebraic* [Kel80], such a presentation also determines the algebras for the presented monad. Specifically, given $A \in [\mathrm{ob}\mathcal{K}_f, \mathcal{K}]$, an algebra for the free finitary monad $FA$ it generates is an object $X \in \mathcal{K}$ with a family of maps $\mathcal{K}(c, X) \rightarrow \mathcal{K}(Ac, X)$ for all $c \in \mathcal{K}_f$; and an algebra for a colimit of finitary monads is an object with a compatible family of algebra structures for those monads.

24

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

As an example, we start with a definition of implicit 2-categories.

**Definition 5.1.** An **implicit 2-category** is a 2-computed $X$ equipped with

- horizontal composition operations

$$X(2^n)_n \times_0 X(2^{m'}_{n'}) \rightarrow X(2^{m+n'}_{n+n'})$$

(where the target 0-cell of the first factor is identified with the source 0-cell of the second factor),

- vertical composition operations

$$X(2^x_x)_x \times_1 X(2^x_n) \rightarrow X(2^n_n)$$

(where the target 1-cell path of the first factor is identified with the source 1-cell path of the second factor), and

- identity operations

$$\overbrace{X(1) \times_0 \cdots \times_0 X(1)}^n \rightarrow X(2^n_n)$$

(where the domain is length $n$ paths of 1-cells)

satisfying source and target laws, associativity and unit laws, and interchange laws.

To go from this definition to a monad on **2-Cptd** whose algebras are implicit 2-categories, we start with the following family $A \in [\text{ob } 2\text{-Cptd}_f, 2\text{-Cptd}]$, where we identify objects of $\mathbb{C}_1$ with their corresponding representable functors in **2-Cptd**:

$$Ac = \begin{cases} 2^{m+n'}_{n+n'} & \text{if } c = 2^n_n \sqcup_0 2^{m'}_{n'} \\ 2^n_n & \text{if } c = 2^x_x \sqcup_1 2^x_n \\ 2^n_n & \text{if } c = \overbrace{1 \sqcup_0 \cdots \sqcup_0 1}^n \end{cases}$$

(Note that all representables are finitely presentable, and pushouts of finitely presentable objects are finitely presentable.) Then an $FA$-algebra is a 2-computed $X$ equipped with three families of maps. The first consists of maps

$$2\text{-Cptd}(2^n_n \sqcup_0 2^{m'}_{n'}, X) \rightarrow 2\text{-Cptd}(2^{m+n'}_{n+n'}, X)$$

But by the universal property of colimits and the Yoneda lemma, this is equivalent to a map

$$X(2^n_n) \times_0 X(2^{m'}_{n'}) \rightarrow X(2^{m+n'}_{n+n'})$$

as in **Definition 5.1** above. The other two families similarly correspond to the other families of operations in **Definition 5.1**. An $FA$-algebra is then a 2-computed equipped with all these operations, but not satisfying any axioms.

To impose the axioms on such a structure, we specify another family $B \in [\text{ob } 2\text{-Cptd}_f, 2\text{-Cptd}]$ and a pair of morphisms $B \Rightarrow UFA$ in $[\text{ob } 2\text{-Cptd}_f, 2\text{-Cptd}]$, where $U$ is the forgetful right adjoint to $F$. For instance, the contribution to $B$ for associativity of vertical composition is

$$B(2^x_x \sqcup_1 2^y_x \sqcup_1 2^y_n) = 2^n_n.$$

We must then specify two morphisms $2^n_n \rightarrow FA(2^x_x \sqcup_1 2^y_x \sqcup_1 2^y_n)$, which is to say two 2-cells of shape $2^n_n$ in the free $FA$-algebra on a trio of 2-cells that could be composed to give one of shape $2^n_n$. In an $FA$-algebra, there are two ways to bracket the composition of such a trio that are not equal; we take these two bracketed compositions as the two desired 2-cells. All the other axioms are treated similarly.

DOUBLY WEAK DOUBLE CATEGORIES

25

Finally, we let $T_2^{\mathbf{I}}$ be the coequalizer of the two maps $FB \Rightarrow FA$ in $\mathbf{Mnd}_f(2\text{-Cptd})$. Then a $T_2^{\mathbf{I}}$-algebra is an $FA$-algebra $X$ whose two underlying $FB$-algebra structures are equal. In the case of associativity, this says precisely that the two possible composites of a vertically composable trio are equal in $X$, i.e. that $X$ obeys the associativity axiom; and similarly for the other axioms. Thus, $T_2^{\mathbf{I}}$-algebras are precisely implicit 2-categories as defined above.

As usual, we could give an equivalent “unbiased” definition using $n$-ary compositions, rather than just binary and nullary composition. This would lead to a different presentation, but an isomorphic monad.

The double-categorical case is entirely analogous, leading to a monad $T_{\mathbf{d}}^{\mathbf{I}}$ on **DblCptd** whose algebras are implicit double categories.

**Definition 5.2.** An **implicit double category** is a double computad $X$ with

- horizontal composition operations

$$X(2_{c,d}^{a,x}) \times_1 X(2_{x,d'}^{a',b'}) \rightarrow X(2_{c,d+d'}^{a+a',b'})$$

(where the vertical target 1-cell path of the first factor is identified with the vertical source 1-cell path of the second factor),

- horizontal identity operations

$$X(1^V) \times_0 \cdots \times_0 X(1^V) \rightarrow X(2_{n,0}^{0,n})$$

(where the domain is length $n$ paths of vertical 1-cells),

- vertical composition operations

$$X(2_{c,x}^{a,b}) \times_1 X(2_{c',d'}^{x,b'}) \rightarrow X(2_{c+c',d'}^{a,b+b'})$$

(where the horizontal target 1-cell path of the first factor is identified with the horizontal source 1-cell path of the second factor), and

- vertical identity operations

$$X(1^H) \times_0 \cdots \times_0 X(1^H) \rightarrow X(2_{0,n}^{n,0})$$

(where the domain is length $n$ paths of horizontal 1-cells)

satisfying source and target laws, associativity and unit laws, and interchange laws.

These definitions agree with those of Sections 2 and 3, since we have observed that 2-computads and double computads can be identified with 2-graphs and double graphs equipped with free category structure via the functors $\iota_2$ and $\iota_{\mathbf{d}}$, and the 2-cell operations and laws given here exactly enhance this to 2-category or double category structure.

*Remark 5.3.* We can also describe these monads in a more conceptual way. Observe that the free 2-category monad on **1-Cat-2-Gph** (2-graphs equipped with 1-category structure) restricts to the subcategory **2-Cptd** (2-graphs equipped with free 1-category structure and maps sending generating 1-cells to generating 1-cells); indeed, this free 2-category monad acts as identity on underlying 1-category structure. The algebras of this monad on **2-Cptd** are simply algebras of the monad on **1-Cat-2-Gph** that lie within the subcategory **2-Cptd**, namely those 2-categories with free underlying 1-categories; algebra morphisms are restricted to those that lie within the subcategory **2-Cptd**, namely those sending generating 1-cells to generating 1-cells. But these are precisely implicit 2-categories and their functors as

26

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

defined in Section 2, so the monad is the same as $T_2^1$ constructed above whose category of algebras is **I-2-Cat**.

Similarly, the free double category monad on $1 \vee 1$-**CatDblGph** (double graphs equipped with horizontal and vertical 1-category structure) restricts to the subcategory **DblCptd** (double graphs equipped with free 1-category structure and maps sending generating 1-cells to generating 1-cells). This induced monad on **DblCptd** is $T_{\mathbf{d}}^1$, whose category of algebras is **IDblCat**.

To upgrade these to definitions of bicategories and doubly weak double categories, we need only introduce the following additional operations.

**Definition 5.4.** A **represented** implicit 2-category $X$ is equipped with

- 1-cell composition 2-cells

$$X(1) \times_0 X(1) \rightarrow X(2_1^2) \quad \text{and} \quad X(1) \times_0 X(1) \rightarrow X(2_2^1)$$

(where the domain is length 2 paths of 1-cells) and

- 1-cell identity 2-cells

$$X(0) \rightarrow X(2_1^0) \quad \text{and} \quad X(0) \rightarrow X(2_0^1)$$

satisfying laws that ensure these 2-cells form inverse pairs from and to the given 1-cell paths.

Similarly, a **represented** implicit double category $X$ is equipped with

- 1-cell composition 2-cells

$$\begin{aligned} X(1^H) \times_0 X(1^H) &\rightarrow X(2_{0,1}^{2,0}), & X(1^H) \times_0 X(1^H) &\rightarrow X(2_{0,2}^{1,0}), \\ X(1^V) \times_0 X(1^V) &\rightarrow X(2_{2,0}^{0,1}), & X(1^V) \times_0 X(1^V) &\rightarrow X(2_{1,0}^{0,2}) \end{aligned}$$

(where the domains are length 2 paths of horizontal or vertical 1-cells) and

- 1-cell identity creation 2-cells

$$\begin{aligned} X(0) &\rightarrow X(2_{0,1}^{0,0}), & X(0) &\rightarrow X(2_{0,0}^{1,0}), \\ X(0) &\rightarrow X(2_{0,0}^{0,1}), & X(0) &\rightarrow X(2_{1,0}^{0,0}) \end{aligned}$$

satisfying laws that ensure these 2-cells form inverse pairs from and to the given 1-cell paths.

In Sections 2 and 3 respectively we characterized bicategories and doubly weak double categories as represented implicit 2-categories and double categories. Hence, by the above algebraic definitions:

**Proposition 5.5.** *The category $\mathbf{W-2-Cat_{st}}$ of bicategories and strict functors is monadic over the category 2-Cptd of 2-computads.*

*Likewise, the category $\mathbf{WDblCat_{st}}$ of doubly weak double categories and strict functors is monadic over the category DblCptd of double computads.* $\square$

Now by the cancellation lemma (Lemma 4.3), since **I-2-Cat** is also monadic over **2-Cptd**, we have that $\mathbf{W-2-Cat_{st}}$ is furthermore monadic over **I-2-Cat**; similarly, $\mathbf{WDblCat_{st}}$ is monadic over **IDblCat**. However, let us also say how to *present* these monads on **I-2-Cat** and **IDblCat**; we do this because in the next section, we will obtain 2-monads from the same presentations.

Since the category of algebras for a finitary monad on an l.f.p. category is again l.f.p., we can just apply the machinery of presentations of monads again with $\mathcal{H} =$

DOUBLY WEAK DOUBLE CATEGORIES

27

**I-2-Cat** and **IDblCat**. Thus, considering the double case explicitly for concreteness and variety, we start with $A \in [\text{ob IDblCat}_f, \text{IDblCat}]$ defined by

$$A(c) = \begin{cases} 2_{0,1}^{2,0} \sqcup 2_{0,2}^{1,0} & \text{if } c = 1^H \sqcup_0 1^H \\ 2_{2,0}^{0,1} \sqcup 2_{1,0}^{0,2} & \text{if } c = 1^V \sqcup_0 1^V \\ 2_{0,1}^{0,0} \sqcup 2_{0,0}^{1,0} \sqcup 2_{0,0}^{0,1} \sqcup 2_{1,0}^{0,0} & \text{if } c = 0 \end{cases}$$

where we implicitly identify the representable objects in **DblCptd** with their images under the free functor in **IDblCat**. Then an $FA$-algebra is an implicit double category equipped with the 1-cell composition and identity creation 2-cell operations as specified above. We then describe another $B \in [\text{ob IDblCat}_f, \text{IDblCat}]$ with two maps $B \Rightarrow UFA$ and consider the coequalizer in $\text{Mnd}_f(\text{IDblCat})$ of the induced parallel pair $FB \Rightarrow FA$, to obtain a monad $T_4^\text{w}$ on **IDblCat** whose algebras are represented implicit double categories. Similarly, we get a monad $T_2^\text{w}$ on **I-2-Cat** whose algebras are represented implicit 2-categories.

We can also describe the free algebras of these monads more directly.

**Proposition 5.6.** *The free bicategory on an implicit 2-category $\mathbf{X}$ admits the following description.*

- *Its 0-cells are those of $\mathbf{X}$.*
- *Its 1-cells are freely generated from those of $\mathbf{X}$ by binary composition and identities.*
- *Its 2-cells with a given boundary are those in $\mathbf{X}$ with boundary given by erasing parentheses and identities, with composition as in $\mathbf{X}$.*

*Similarly, the free doubly weak double category on an implicit double category $\mathbf{X}$ admits the following description.*

- *Its 0-cells are those of $\mathbf{X}$.*
- *Its 1-cells of both sorts are freely generated from those of $\mathbf{X}$ by binary composition and identities.*
- *Its 2-cells with a given boundary are those in $\mathbf{X}$ with boundary given by erasing parentheses and identities, with composition as in $\mathbf{X}$.*

*Proof.* We describe the 2-category case; the double-category case is similar. First note that given a path $f_1, \dots, f_n$ from $A$ to $B$ in an implicit 2-category $\mathbf{X}$, the implicit 2-category obtained from $\mathbf{X}$ by freely adjoining a 1-cell $f: A \to B$ and an isomorphism $f_1, \dots, f_n \cong f$ is described as follows: its 0-cells and 1-cells are those of $\mathbf{X}$ plus the 1-cell $f$, and the 2-cells in $\mathbf{X}'$ with a given boundary are those in $\mathbf{X}$ with boundary obtained by replacing all occurrences of $f$ with $f_1, \dots, f_n$. It is easy to verify this implicit 2-category satisfies the claimed universal property. Similarly, we can adjoin any number of such 1-cells with isomorphisms.

Now the free represented implicit 2-category (equivalently, bicategory) on an implicit 2-category defined as in **Definition 5.4** is a sequential colimit of such steps of adjoining isomorphisms. Specifically, starting from $\mathbf{X}_0 = \mathbf{X}$, we adjoin a 1-cell as above for *every* path in $\mathbf{X}_0$ of length 2 or 0, obtaining a new implicit 2-category $\mathbf{X}_1$. We then repeat for every path of length 2 or 0 in $\mathbf{X}_1$, obtaining $\mathbf{X}_2$, and so on. This yields a chain of inclusions

$$\mathbf{X}_0 \to \mathbf{X}_1 \to \mathbf{X}_2 \to \dots .$$

Since the monad on 2-computads for implicit 2-categories is finitary, the colimit $\mathbf{X}_\infty$ of this chain in **I-2-Cat** is its colimit in **2-Cptd** equipped with the evident

28

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

composition structure. And since **2-Cptd** is a presheaf category and this chain consists of monomorphisms, its colimit in **2-Cptd** is its “union” in a straightforward sense, giving the explicit description as stated in the proposition. Finally, it is straightforward to check that $\mathbf{X}_{\infty}$ is represented, and that any map from $\mathbf{X}$ to a represented implicit 2-category factors uniquely through $\mathbf{X}_{\infty}$. $\square$

**Corollary 5.7.** *The free bicategory on a 2-computad $\mathbf{X}$ has 1-cells freely generated from those of $\mathbf{X}$ by binary composition and identities, and 2-cells as in the free strict 2-category with boundary given by erasing parentheses and identities. Similarly, the free doubly weak double category on a double computad $\mathbf{X}$ has 1-cells of both types freely generated from those of $\mathbf{X}$ by binary composition and identities, and 2-cells as in the free strict double category with boundary given by erasing parentheses and identities.*

*Proof.* Combine Proposition 5.6 and Remark 5.3. $\square$

Finally, in Sections 2 and 3 we also characterized strict 2-categories, pseudo double categories, and strict double categories by imposing associativity and unit laws. These axioms can be added to the monad presentations, so we have:

**Proposition 5.8.** *The category 2-Cat of 2-categories (and strict functors) is monadic over the category 2-Cptd of 2-computads.*

*Likewise, the categories $\mathbf{DblCat}$ and $\mathbf{PsDblCat}_{\mathrm{st}}$ of strict double categories and pseudo double categories (both with strict functors) are monadic over the category $\mathbf{DblCptd}$ of double computads.* $\square$

The situation is summarized by chains of forgetful functors

$$2\text{-}\mathbf{Cat} \rightarrow \mathbf{W}\text{-}2\text{-}\mathbf{Cat}_{\mathrm{st}} \rightarrow \mathbf{I}\text{-}2\text{-}\mathbf{Cat} \rightarrow 2\text{-}\mathbf{Cptd}$$

and

$$\mathbf{DblCat} \rightarrow \mathbf{PsDblCat}_{\mathrm{st}} \rightarrow \mathbf{WDblCat}_{\mathrm{st}} \rightarrow \mathbf{IDblCat} \rightarrow \mathbf{DblCptd}$$

all compositions of which are monadic, using Lemma 4.3.

*Remark 5.9.* The left adjoint $\mathbf{I}\text{-}2\text{-}\mathbf{Cat} \rightarrow 2\text{-}\mathbf{Cat}$ is in fact the obvious subcategory inclusion, sending implicit 2-categories to their path 2-categories. The left adjoint $\mathbf{IDblCat} \rightarrow \mathbf{DblCat}$ is similar.

The composite $\mathbf{W}\text{-}2\text{-}\mathbf{Cat}_{\mathrm{st}} \rightarrow \mathbf{I}\text{-}2\text{-}\mathbf{Cat} \rightarrow 2\text{-}\mathbf{Cat}$ (forget then free) is the usual strictification functor for bicategories, which we described explicitly in Proposition 2.5. Analogously, the composite $\mathbf{WDblCat}_{\mathrm{st}} \rightarrow \mathbf{IDblCat} \rightarrow \mathbf{DblCat}$ provides a strictification functor for doubly weak double categories; in the next section we will show that every doubly weak double category is equivalent to its strictification in a suitable sense.

## 6. ICONS AND 2-MONADS

In this section we will see that $\mathbf{I}\text{-}2\text{-}\mathbf{Cat}$ and $\mathbf{IDblCat}$ can be enhanced to 2-categories. (One furthermore expects the instances of a two-dimensional categorical structure to be objects in a *three*-dimensional categorical structure; transformations and modifications of implicit 2-categories are discussed in Appendix A.)

As is standard in the theory of bicategories, we cannot directly define a (weak or strict) 2-category of bicategories, pseudofunctors, and transformations: vertical

DOUBLY WEAK DOUBLE CATEGORIES

29

composition of transformations is not strictly associative. But there is an alternative notion of 2-cell will give us a 2-category after all, called an *icon* [Lac08].

When $F$ and $G$ are pseudofunctors of bicategories, an icon from $F$ to $G$ is equivalent to a *colax* transformation whose components are identity 1-cells. (A *lax* transformation from $F$ to $G$ whose components are identity 1-cells can be identified with an icon from $G$ to $F$; the reason one chooses the colax ones to be primary is that it is in that case that the 2-cell components point *from* the value of $F$ on a 1-cell *to* the value of $G$ on that 1-cell.)

We may define an icon of implicit 2-category functors to be simply an icon of the associated 2-functors between path 2-categories. Unpacking this, we get the following:

**Definition 6.1.** Let $\mathbf{C}$ and $\mathbf{D}$ be implicit 2-categories, and let $F, G: \mathbf{C} \rightarrow \mathbf{D}$ be functors *that agree on 0-cells*. An **icon** $\theta$ between $F$ and $G$ consists of, for each 1-cell $f: A \rightarrow B$ in $\mathbf{C}$, a 2-cell (bigon) $\theta_f$ in $\mathbf{D}$:

![img-35.jpeg](img-35.jpeg)

such that for each 2-cell $\alpha$ in $\mathbf{C}$, we have

![img-36.jpeg](img-36.jpeg)

We define **compositions** of icons componentwise. Likewise **identity** icons are identities componentwise. We can also **whisker** an icon with a functor (i.e. compose a functor $C' \rightarrow C$ with an icon of functors $C \rightarrow D$ to obtain an icon of functors $C' \rightarrow D$; or compose an icon of functors $C \rightarrow D$ with a functor $D \rightarrow D'$ to obtain an icon of functors $C \rightarrow D'$) by using the icon components at the image of the functor or by applying the functor to the icon components, as usual.

**Proposition 6.2.** *There is a strict 2-category $\mathcal{I}$-2-Cat of implicit 2-categories, functors, and icons.*

This is just the locally full sub-2-category of the 2-category of strict 2-categories, 2-functors, and icons in the ordinary sense.

The definition for implicit double categories is similar, but there is an added subtlety: we have to choose directions for both the horizontal and vertical component bigons, and these choices can be independent. Thus in principle we get four different notions of icon, and which one we regard as going “from” $F$ “to” $G$ depends on our beliefs about which direction the squares in a double category “point”. There are also four possibilities for this, which we may name cardinally as **northwest** $\searrow$, **northeast** $\nearrow$, **southeast** $\searrow$, and **southwest** $\nearrow$.

For the most part we will choose the *southeast* view, which has the advantage that squares point in the same direction as all the arrows on their boundaries:

30

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

This has the consequence that horizontal bigons point from top to bottom, while vertical bigons point from left to right. However, it should be noted that this is not compatible with the “quintets” construction of a double category from a 2-category, which requires picking either the northeast or southwest view. Fortunately, the four kinds of icon are interchanged by the symmetry operations of double categories, so all of them provide equivalent 2-categories of double categories in the end. Moreover, *invertible* icons are the same no matter which definition we pick.

**Definition 6.3.** Let $F, G: \mathbf{C} \rightarrow \mathbf{D}$ be functors of implicit double categories *that agree on 0-cells*. A **southeast icon** $\theta$ between $F$ and $G$ consists of

- for each horizontal $f: A \rightarrow B$ in $\mathbf{C}$, a 2-cell (horizontal bigon) $\theta_f$ in $\mathbf{D}$:

![img-37.jpeg](img-37.jpeg)

- for each vertical $g: A \rightarrow B$ in $\mathbf{C}$, a 2-cell (vertical bigon) $\theta_g$ in $\mathbf{D}$:

![img-38.jpeg](img-38.jpeg)

such that for each 2-cell $\alpha$ in $\mathbf{C}$, we have

![img-39.jpeg](img-39.jpeg)

**Proposition 6.4.** *There is a strict 2-category $\mathcal{IDblCat}$ of implicit double categories, functors, and (southeast) icons.*

Now since $\mathcal{I}$-2-Cat and $\mathcal{IDblCat}$ are 2-categories, we can hope to enhance the monads on these categories to 2-monads. This is not possible for our monads on 2-Cptd and DblCptd, as these are not 2-categories in any obvious way.

**Remark 6.5.** There is also another category between I-2-Cat and 2-Cptd that can be extended to a 2-category: its objects are 2-computads equipped with composition operations allowing arbitrary 2-cells to be composed only with bigons. (In other words, the bigons form categories which compatibly act on other 2-cells.) The

DOUBLY WEAK DOUBLE CATEGORIES

31

double-categorical case is similar. However, for reasons of space we will not treat these categories.

**Lemma 6.6.** *These 2-categories $\mathcal{I}$-2-$\mathcal{C}$at and $\mathcal{I}$DblCat are locally finitely presentable as 2-categories (that is, Cat-enriched categories).*

*Proof.* By [Kel82b, Proposition 7.5], a cocomplete 2-category $\mathcal{K}$ is locally finitely presentable if and only if its underlying ordinary category $\mathcal{K}_0$ is locally finitely presentable and whenever $X \in \mathcal{K}$ is finitely presentable in $\mathcal{K}_0$ (that is, $\mathcal{K}_0(X, -): \mathcal{K}_0 \to \mathbf{Set}$ preserves filtered colimits) then it is also **Cat**-finitely-presentable in $\mathcal{K}$ (that is, $\mathcal{K}(X, -): \mathcal{K} \to \mathbf{Cat}$ preserves filtered colimits). For this, in turn, it suffices to show that $\mathcal{K}_0$ has a strongly generating set of finitely presentable objects that are also finitely presentable in $\mathcal{K}$.

We consider $\mathcal{I}$DblCat; the case of $\mathcal{I}$-2-$\mathcal{C}$at is analogous. For cocompleteness, since the underlying 1-category **IDblCat** is cocomplete, it suffices by [Kel82a, §3.8] to show that $\mathcal{I}$DblCat has powers by small categories. As for other 2-categories of icons, these can be constructed “hom-wise”. The power $X^{\mathbb{J}}$ has the same objects as $X$, its vertical arrows from $x$ to $y$ are $\mathbb{J}$-shaped diagrams in the category of such vertical arrows of $X$, and similarly for horizontal arrows, while its 2-cells are families of 2-cells in $X$ indexed by the objects of $\mathbb{J}$ that are “natural” with respect to their boundaries.

Now an evident strongly generating set of objects in the 1-category **IDblCat** consists of the images of the representables $0$, $1^H$, $1^V$, and $2_{c,d}^{a,b}$, so it suffices to show that these are also finitely presentable in the 2-category, in other words that icons mapping out of them preserve filtered colimits. Now, there are no nontrivial icons with domain $0$, while icons with domain $1^H$ and $1^V$ are simply horizontally or vertically globular 2-cells, and icons with domain $2_{c,d}^{a,b}$ are commutative “cylinders” relating two 2-cells of shape $2_{c,d}^{a,b}$ by globular 2-cells on their boundaries. But all of these are finitary structures, and hence are preserved in filtered colimits. $\square$

Therefore, we can use the machinery sketched in Section 5 to present 2-monads on $\mathcal{I}$-2-$\mathcal{C}$at and $\mathcal{I}$DblCat. Moreover, since the finitary objects are the same whether we regard them as 1-categories or 2-categories, exactly the same presentation as before actually presents a 2-monad.

We immediately deduce that **W-2-Cat$_{st}$** and **WDblCat$_{st}$** can also be enhanced to 2-categories $\mathcal{W}$-2-$\mathcal{C}$at$_{st}$ and $\mathcal{W}$DblCat$_{st}$, namely the 2-categories of strict algebras and strict morphisms for these 2-monads. We also obtain immediately notions of pseudo, lax, and colax morphism between bicategories and doubly weak double categories. Moreover, the “endomorphism monad of a morphism” $\{f, f\}$ from [KL97, §2] (see also [Lac09, §5.1]) implies that the definitions of these more general morphisms can also be deduced algebraically from the presentation.

In general, suppose $FA$ is the free 2-monad on $A \in [\mathrm{ob}\mathcal{K}_f, \mathcal{K}]$, for some locally finitely presentable 2-category $\mathcal{K}$, so that an $FA$-algebra $X$ is determined by maps $\mathcal{K}(c, X) \to \mathcal{K}(Ac, X)$. Then a pseudo $FA$-morphism $f: X \to Y$ is determined by natural isomorphisms

$$\begin{array}{ccc} \mathcal{K}(c, X) & \longrightarrow & \mathcal{K}(Ac, X) \\ \downarrow & \cong & \downarrow \\ \mathcal{K}(c, Y) & \longrightarrow & \mathcal{K}(Ac, Y). \end{array}$$

32

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

Similarly, if $T$ is the coequalizer of the maps $FB \Rightarrow FA$, a pseudo $T$-morphism is a pseudo $FA$-morphism (as above) that restricts to the same pseudo $FB$-morphism along the two given maps. In our case, this specializes to the following:

**Lemma 6.7.** *Let $\mathbf{C}$ and $\mathbf{D}$ be doubly weak double categories. A pseudo $T^\mathbf{v}$-morphism $F: \mathbf{C} \rightarrow \mathbf{D}$ is a functor of implicit double categories together with*

- *For each pair of composable horizontal 1-cells $f: A \rightarrow B$ and $g: B \rightarrow C$ in $\mathbf{C}$, an invertible horizontal bigon in $\mathbf{D}$:*

![img-40.jpeg](img-40.jpeg)

*that commutes with the representability isomorphisms:*

![img-41.jpeg](img-41.jpeg)

- *For each pair of composable vertical 1-cells $f: A \rightarrow B$ and $g: B \rightarrow C$ in $\mathbf{C}$, an invertible vertical bigon in $\mathbf{D}$:*

![img-42.jpeg](img-42.jpeg)

*that commutes with the representability isomorphisms:*

![img-43.jpeg](img-43.jpeg)

- *For each object $A \in \mathbf{C}$, invertible horizontal and vertical bigons:*

![img-44.jpeg](img-44.jpeg)

DOUBLY WEAK DOUBLE CATEGORIES

33

that commute with the representability isomorphisms:

$$\begin{array}{c} F1_A \\ \phi_A^H \\ 1_{FA} \\ \cong \\ FA \end{array} = \begin{array}{c} F1_A \\ F(\cong) \\ FA \end{array} \quad F1_A \quad \phi_A^H 1_{FA} \cong FA = F1_A \quad F(\cong) \quad FA$$

However, since the representability cells are also isomorphisms, the conditions required above uniquely determine each invertible cell $\phi$ (as the composite of two representability cells). The case of bicategories is similar. Thus the pseudo-morphisms are simply functors of the underlying implicit structures, recovering the categories **W-2-Cat** and **WDblCat** from Section 2 and Section 3:

**Proposition 6.8.** *If $X$ and $Y$ are bicategories, then every functor $F: X \to Y$ of implicit 2-categories has a unique structure of pseudo $T_2^w$-morphism.*

*Similarly, if $X$ and $Y$ are doubly weak double categories, then every functor $F: X \to Y$ of implicit double categories has a unique structure of pseudo $T_d^w$-morphism.*

**Corollary 6.9.** *The 2-monads $T_2^w$ on $\mathcal{I}$-2-Cat, and $T_d^w$ on $\mathcal{IDblCat}$, are pseudo-idempotent. Therefore, an icon between bicategories or doubly weak double categories is nothing more than an icon between their underlying implicit 2-categories or implicit double categories.*

*Proof.* The first statement is by definition of “pseudo-idempotent”. The second follows from [KL97, Proposition 6.7].

*Remark 6.10.* In particular, every lax or colax $T_2^w$- or $T_d^w$-morphism is automatically pseudo. We could obtain nontrivial notions of lax and colax functors by using the alternative base 2-category suggested in Remark 6.5.

*Remark 6.11.* The same arguments apply for the 2-monads whose algebras are strict 2-categories, strict double categories, and pseudo double categories. In the fully strict case it is also sensible to consider *pseudo algebras*; these yield “unbiased” bicategories and a similar notion of “unbiased doubly weak double category”. General 2-monadic coherence techniques as in [Pow89, Lac02a, Shu12] can be adapted to show that every such unbiased structure is equivalent to a strict one.

We end this section by characterizing the relevant equivalences more explicitly, and proving a coherence theorem for (biased) doubly weak double categories.

**Lemma 6.12.** *A functor of implicit double categories $F: \mathbf{C} \to \mathbf{D}$ is an equivalence in the 2-category $\mathcal{IDblCat}$ if and only if it is*

- *byjective on 0-cells,*
- *locally essentially surjective on horizontal and vertical 1-cells, and*
- *byjective on 2-cells per boundary of 1-cells in $\mathbf{C}$.*

*Therefore, a functor of doubly weak double categories is an equivalence in the 2-category $\mathcal{WDblCat}$ if and only if it satisfies these same conditions.*

34

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

*Proof.* Suppose $F$ is an equivalence, so there exists $G: \mathbf{D} \rightarrow \mathbf{C}$ with invertible icons $1_{\mathbf{C}} \cong G \circ F$ and $1_{\mathbf{D}} \cong F \circ G$. For these icons to exist forces $F$ and $G$ to be inverse on 0-cells. We also have that $F$ is surjective on isomorphism classes of 1-cells, since $g \cong FGg$ for any 1-cell $g$ in $\mathbf{D}$. Finally, any 2-cell $\alpha$ is related to $FG\alpha$ by composing with invertible icon components, so $FG$ is bijective on 2-cells per boundary of 1-cells; likewise so is $GF$, and therefore so must be $F$ and $G$.

Conversely, suppose $F$ satisfies the conditions above. We nonconstructively define a functor $G: \mathbf{D} \rightarrow \mathbf{C}$. On 0-cells $G$ is inverse to $F$. For each 1-cell $g$ in $\mathbf{D}$, we pick a 1-cell $Gg$ in $\mathbf{C}$ with an isomorphism $g \cong FGg$. Now to define $G$ on a 2-cell in $\mathbf{D}$, we compose on all sides with these chosen isomorphisms or their inverses, then apply the inverse of the bijection on 2-cells given by $F$. Functoriality of $G$ so defined follows from functoriality of $F$, and we have an invertible icon $1_{\mathbf{D}} \cong F \circ G$ by construction. To define the icon $1_{\mathbf{C}} \cong G \circ F$ at a 1-cell $f$ in $\mathbf{C}$, we take the chosen isomorphism in $\mathbf{D}$ at $Ff$, then apply the inverse of the bijection on 2-cells given by $F$. Naturality of this icon also follows from functoriality of $F$. $\square$

# **Proposition 6.13.** *Every doubly weak double category is equivalent to a strict one.*

*Proof.* A doubly weak double category is defined as a representable implicit double category, and an implicit double category is in turn defined as a strict double category with free 1-cells. Hence every doubly weak double category has an associated strict double category (the path double category), its “strictification”. On the other hand, in *Corollary 3.14*, we saw that strict double categories in the usual sense are identified with doubly weak double categories that happen to be strict. Thus the strictification of a doubly weak double category $\mathbf{C}$ determines another doubly weak double category $\operatorname{st} \mathbf{C}$, which is strict. We will show that $\mathbf{C}$ and $\operatorname{st} \mathbf{C}$ are equivalent implicit double categories.

Under the correspondence of *Proposition 3.13*, we obtain the following description of $\operatorname{st} \mathbf{C}$: 0-cells in $\operatorname{st} \mathbf{C}$ are 0-cells in $\mathbf{C}$, horizontal or vertical 1-cells in $\operatorname{st} \mathbf{C}$ are *paths* of horizontal or vertical 1-cells in $\mathbf{C}$, and a 2-cell in $\operatorname{st} \mathbf{C}$ (bordered by paths of paths) is a 2-cell in $\mathbf{C}$ (bordered by the concatenations).

There is an evident functor $F: \mathbf{C} \rightarrow \operatorname{st} \mathbf{C}$ sending 1-cells to corresponding length 1 paths. This $F$ is clearly bijective on 0-cells and bijective on 2-cells per boundary of 1-cells in $\mathbf{C}$. Moreover, $F$ is surjective on isomorphism classes of 1-cells, since each 1-cell in $\operatorname{st} \mathbf{C}$ (a path in $\mathbf{C}$) is isomorphic to a 1-cell in the image of $F$ (a length 1 path, a composite of the path in $\mathbf{C}$). Hence $F$ is an equivalence by *Lemma 6.12*. (Moreover an equivalence in the other direction can be constructed explicitly by choosing a preferred way of associating compositions of paths.) $\square$

## 7. DOUBLE BICATEGORIES

Our last goal in this paper is to give finite axiomatizations of doubly weak double categories. There are actually many such definitions, and we struggled with choosing which ones to present in detail. In this section we give a definition that clarifies the relationship to Verity’s double bicategories (and *Proposition 7.22* reduces it to a definition only involving cells of *square* shape); in *Section 8* we give a definition that clarifies the relationship to Garner’s cubical bicategories; and finally in *Section 9* we give a monadic presentation using only finitely many of the shapes of a double computad.

DOUBLY WEAK DOUBLE CATEGORIES

35

A double graph with bigons is a double computed whose only 2-cells are squares, horizontal bigons, and vertical bigons:

![img-45.jpeg](img-45.jpeg)

and

![img-46.jpeg](img-46.jpeg)

and

![img-47.jpeg](img-47.jpeg)

The category BiDblGph of double graphs with bigons can be identified with a functor category whose domain is a suitable full subcategory of  \( C_{d} \) :

![img-48.jpeg](img-48.jpeg)

(composition laws as in \(\mathbb{C}_{\mathbf{d}}\)). Hence the forgetful functor \(\mathbf{DblCptd} \to \mathbf{DblGph}\) factors through \(\mathbf{BiDblGph}\).

We now recall the definition of double bicategory, writing out all the operations explicitly for reference.

Definition 7.1 ([Ver92]). A double bicategory consists of:

- A double graph with bigons. (That is, collections of 0-cells, horizontal and vertical 1-cells, and horizontal bigon 2-cells, vertical bigon 2-cells, and square 2-cells, related appropriately by various source and target maps.)
- The operations of a bicategory on the horizontal 1-cells and bigons. Likewise, the operations of a bicategory on the vertical 1-cells and bigons.
- A top bigon-on-square action operation sending compatible pairs of horizontal bigons and squares (where the bottom 1-cell of the bigon is the same as the top 1-cell of the square) to squares.

![img-49.jpeg](img-49.jpeg)

![img-50.jpeg](img-50.jpeg)

Likewise bottom, left, and right bigon-on-square action operations.

- A horizontal identity square operation sending vertical 1-cells to squares. Likewise, a vertical identity square operation sending horizontal 1-cells to squares.
- A horizontal composition operation sending compatible pairs of squares (where the right 1-cell of the first square is the same as the left 1-cell of the second square) to squares.

Likewise, a vertical composition operation for squares.

Furthermore, the following laws hold:

- Appropriate source and target laws for all ways of composing bigons and squares.
- The laws of a bicategory for horizontal 1-cells and bigons, and likewise for vertical 1-cells and bigons.

36

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

- Identity, associativity, and mutual commutativity laws making the left, right, top, and bottom bigon-on-square operations into four compatible actions.
- For any vertical bigon $\beta$, the identity square commutativity law

$$\beta 1 = 1\beta$$

(where the left hand side is the left action of $\beta$ on the identity square of its codomain, and the right hand side is the right action of $\beta$ on the identity square of its domain).

Likewise, the analogous identity square commutativity law for horizontal bigons.

- For any compatible horizontal string consisting of a vertical bigon $\beta$ sandwiched between two squares $\zeta, \xi$, the associativity law

$$(\zeta\beta)\xi = \zeta(\beta\xi).$$

Likewise, the analogous vertical sandwiching associativity law.

- For any compatible horizontal string consisting of a vertical bigon $\beta$ to the left of two squares $\zeta, \xi$, the associativity law

$$(\beta\zeta)\xi = \beta(\zeta\xi).$$

Likewise, the analogous horizontal associativity law on the right, and the analogous vertical associativity laws on the top and bottom.

- An interchange law that says the two possible ways of composing two horizontal bigons side by side atop two horizontally adjacent squares are equal.

![img-51.jpeg](img-51.jpeg)

![img-52.jpeg](img-52.jpeg)

Likewise, the analogous interchange laws for horizontal bigons below horizontally adjacent squares, and for vertical bigons to the left and to the right of vertically stacked squares.

- A horizontal left unitor naturality law for squares $\zeta$:

![img-53.jpeg](img-53.jpeg)

where $\cong$ denotes the appropriate left unitor isomorphism bigons.

Likewise, the analogous horizontal right unitor naturality law, and the analogous top and bottom (i.e. vertical left and right) unitor naturality laws.

DOUBLY WEAK DOUBLE CATEGORIES

37

- A horizontal associator naturality law for squares $\zeta, \xi, \psi$:

![img-54.jpeg](img-54.jpeg)

where $\cong$ denotes the appropriate associator isomorphism bigons.

Likewise, the analogous vertical associator naturality law.

- The interchange laws for squares as in a double category.
Specifically, the identity compatibility law states that vertical identity squares on horizontal identity 1-cells agree with horizontal identity squares on vertical 1-cells; the identity interchange laws state that horizontal compositions of vertical identity squares are vertical identity squares and vice versa; and the square composition interchange law states that the two possible ways of composing a two by two grid of compatible squares are equal.

We will show that doubly weak double categories are equivalent to double bicategories satisfying an extra “tidiness” condition.

**Definition 7.2.** A **tidy double bicategory** is a double bicategory in which the canonical map that sends *2-cells in the horizontal bicategory* to *squares whose vertical source and target are identities* is bijective

![img-55.jpeg](img-55.jpeg)

and analogously for 2-cells in the vertical bicategory and squares whose horizontal source and target are identities.

Explicitly, this means a tidy double bicategory has:

- A conversion operation sending squares whose top and bottom 1-cells are identities to vertical bigons.
Likewise, a conversion operation sending squares whose left and right 1-cells are identities to horizontal bigons.
and the following laws are satisfied:
- Appropriate source and target laws for the degenerate square to bigon conversion operations.
- The horizontally degenerate square to vertical bigon conversion operation is inverse to the map that sends each vertical bigon $\beta$ to the square

$$\beta 1 = 1\beta.$$

Likewise, the analogous correspondence holds between vertically degenerate squares and horizontal bigons.

**Remark 7.3.** Tidiness already appears, without a name, in [Ver92, Lemma 1.4.9]. In [RvdWAN25] it is called *saturation*.

38

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

*Remark 7.4.* Double bicategories are monadic over double graphs, essentially by construction. But *tidy* double bicategories are not, since the domains of the additional square-to-bigon conversion operations are not objects of **BiDblGph**: there is no double graph with bigons representing, say, a “square whose vertical source and target are identities”.

All of the operations and laws in a (tidy) double bicategory are readily derived from those in a doubly weak double category, and so there is a forgetful functor $U: \mathbf{WDblCat}_{\text{st}} \rightarrow \mathbf{DblBicat}_{\text{st}}$, where $\mathbf{DblBicat}_{\text{st}}$ denotes the category of double bicategories and strict functors, i.e. homomorphisms of the algebraic structure. In the other direction, we have a functor described as follows (similarly to Proposition 2.5), which will turn out to be left adjoint to this forgetful functor.

**Proposition 7.5.** *Given a double bicategory $\mathcal{C}$, the following data amount to a doubly weak double category $F\mathcal{C}$:*

- *The 0-cells and 1-cells (horizontal and vertical) are as in $\mathcal{C}$.*
- *A 2-cell with a given boundary is a family consisting of a choice of square in $\mathcal{C}$ for every possible bracketing of the boundary, such that these squares are related by composing with the appropriate rebracketing coherence isomorphism bigons.*
- *Composition (and identity) for 2-cells is induced by composition of squares in $\mathcal{C}$.*
- *The composition isomorphisms are given by identity squares.*

*Proof.* Due to the compatibilities of the bigon actions, the coherence theorem for bicategories guarantees that each square with bracketed paths along its boundary determines, by composing with coherence isomorphisms, a unique corresponding square for every rebracketing of the boundary. Thus composition of 2-cells is well-defined, since rebracketing then composing squares is the same as composing then rebracketing as appropriate.

Finally, composition of 2-cells is horizontally and vertically associative and unital by the naturality conditions relating associators and unitors with squares. It satisfies interchange laws because the square composition operations do. $\square$

*Remark 7.6.* The only use of bigons in this definition is to rebracket squares. Hence this construction discards the two bicategories of bigons; only when the double bicategory is tidy can these two bicategories be recovered from the bracketed squares and their composition. Surprisingly, however, although it forgets this information it is still left adjoint to the forgetful functor.

**Lemma 7.7.** *Any doubly weak double category $\mathcal{C}$ is isomorphic to $FUC$.*

*Proof.* By composing with chosen isomorphisms, the 2-cells with arbitrary boundary are in composition-respecting correspondence with bracketed squares. $\square$

**Lemma 7.8.** *In any double bicategory $\mathcal{C}$, the canonical map converting horizontal bigons to squares induces a strict functor from the horizontal bicategory of $\mathcal{C}$ to the horizontal bicategory of $F\mathcal{C}$. (Likewise for the vertical bicategory.) Hence in the case of a tidy double bicategory, this is a strict isomorphism of bicategories.*

*Moreover, this assignment preserves the action of bigons on squares.*

DOUBLY WEAK DOUBLE CATEGORIES

39

*Proof.* The canonical map from horizontal bigons to squares is by composing with a vertical identity square; the resulting square is bordered by vertical identities, and so corresponds to a bigon in $FC$.

The double bicategory laws of associativity, identity commutativity, and unitor naturality ensure this mapping preserves vertical bicategorical composition (i.e. that vertically composing bigons then converting to a square is the same as converting then vertically composing squares, up to rebracketing with unitors). The unit laws for bigon-on-square action ensure preservation of identities. The identity interchange and bigon-square interchange laws ensure preservation of horizontal composition. Coherence isomorphisms are preserved because in $FC$ they are defined (see Proposition 2.7) as compositions of morphisms related to identities by composing coherence isomorphisms.

Moreover, the action of bigons on squares is preserved by associativity and unitor naturality laws. $\square$

**Lemma 7.9.** *If $\mathcal{C}$ is a double bicategory, then $FC$ is the free doubly weak double category on $\mathcal{C}$.*

*Proof.* Let $\mathbf{D}$ be a doubly weak double category. A strict functor $\mathcal{C} \rightarrow U\mathbf{D}$ induces a strict functor $FC \rightarrow \mathbf{D} \cong FUD$, since, using Lemma 7.7, the latter amounts to functorially mapping families of bracketed squares in $\mathcal{C}$ to families of bracketed squares in $\mathbf{D}$. Conversely, by Lemma 7.8 such a map of squares $FC \rightarrow \mathbf{D}$ also induces action-respecting strict functors from the horizontal and vertical bicategories of $\mathcal{C}$ to those of $\mathbf{D}$, in total determining a strict functor $\mathcal{C} \rightarrow U\mathbf{D}$. Moreover, these processes of translation are inverse. $\square$

**Proposition 7.10.** *The adjunction*

$$\mathbf{DblBicat_{st}} \xrightleftharpoons[F]{U} \mathbf{WDblCat_{st}}$$

*restricts to an equivalence of categories between $\mathbf{WDblCat_{st}}$ and the full subcategory of $\mathbf{DblBicat_{st}}$ consisting of tidy double bicategories.*

*Proof.* The counit is an isomorphism, via Lemma 7.7. The unit is an isomorphism at tidy double bicategories, via Lemma 7.8 (additionally noting that squares and their composition in $FC$ are also as in $\mathcal{C}$). $\square$

**Corollary 7.11.** *The forgetful functor $\mathbf{WDblCat_{st}} \rightarrow \mathbf{DblBicat_{st}}$ is fully faithful.* $\square$

**Corollary 7.12.** *The forgetful functor $\mathbf{WDblCat_{st}} \rightarrow \mathbf{BiDblGph}$ is faithful and conservative.* $\square$

Thus, we can still regard a doubly weak double category as “structure” on an underlying double graph with bigons, though that structure is not monadic.

*Remark 7.13.* Conversely, a double bicategory is equivalently a doubly weak double category $\mathbf{C}$ together with two bicategories with strict functors into the horizontal and vertical bicategories of $\mathbf{C}$ that are the identity on 1-cells. Thus, we may alternatively identify doubly weak double categories with double bicategories in which the bicategories are freely generated by the 1-cells and their incoherent operations.

40

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

The equivalence of Proposition 7.10 can also be extended to pseudofunctors. For double bicategories, these are the morphisms in Verity's category $\underline{Horiz}_{SH}$, whose definition is obtained by combining [Ver92, Definition 1.4.7, the definition preceding Lemma 1.4.9, and the definition preceding Observation 1.4.10].

**Definition 7.14.** Let $\mathbf{C}$ and $\mathbf{D}$ be double bicategories. A **double pseudofunctor** $\mathbf{C} \rightarrow \mathbf{D}$ consists of:

- Two pseudofunctors from the vertical and horizontal bicategories of $\mathbf{C}$ to those of $\mathbf{D}$, which are the same on objects.
- A function from squares of $\mathbf{C}$ to squares of $\mathbf{D}$ that acts on boundaries as the 1-cell action of the horizontal and vertical pseudofunctors.
- The top, bottom, left, and right actions of bigons on squares are preserved.
- The horizontal and vertical square composition and identities are preserved, modulo the coherence cells for the horizontal and vertical pseudofunctors.

These are the morphisms of a category **DblBicat**.

**Lemma 7.15.** *Any pseudofunctor between doubly weak double categories induces a double pseudofunctor between their underlying double bicategories.*

*Proof.* Just like Proposition 2.8. $\square$

**Lemma 7.16.** *If $G : \mathbf{C} \rightarrow \mathbf{D}$ is a double pseudofunctor between double bicategories, the following defines a pseudofunctor of doubly weak double categories $FG : F\mathbf{C} \rightarrow F\mathbf{D}$, where $F$ is as in Proposition 7.5.*

- *The action on 0-cells and 1-cells is as for $G$.*
- *Given a 2-cell with some boundary, its component with a given bracketing of the boundary is sent to the image of that 2-cell under $G$, acted on all four sides by the coherence isomorphisms for that bracketing induced by the horizontal and vertical pseudofunctor parts of $G$.*

*Proof.* Coherence for pseudofunctors implies that the operation on 2-cells is well-defined, and preserves composition of 2-cells. $\square$

**Proposition 7.17.** *The equivalence of Proposition 7.10 extends to an equivalence between WDblCat and the full subcategory of DblBicat determined by the tidy double bicategories.* $\square$

*Remark 7.18.* If $\mathbf{C}$ and $\mathbf{D}$ are strict double categories regarded as double bicategories, then a double pseudofunctor as in Definition 7.14 specializes to the notion of double pseudofunctor from [Shu11, Definition 6.1].

Finally, we can further clarify the relationship between doubly weak double categories and "untidy" double bicategories as follows.

**Lemma 7.19.** *The algebras of the monad on BiDblGph induced by the forgetful functor WDblCat$_{\text{st}} \rightarrow \text{DblGph}$ are precisely double bicategories.*

*Proof.* First we observe that the free doubly weak double category on a double graph with bigons is such that the 1-cells are bracketed paths, and the 2-cells are grids of squares with sequences of vertical or horizontal bigons placed at the vertical and horizontal edges, matching along 1-cells, with boundaries bracketed arbitrarily.

DOUBLY WEAK DOUBLE CATEGORIES

41

Using Corollary 5.7, to see this it suffices to give a similar description of free strict double categories, where the 1-cells are instead simply paths. Such bigon-accessorized grids indeed form a strict double category (where 2-cells bordered by identities are given by zero-width or zero-height grids), and we may check its universal property. Namely, given a double graph with bigons $X$, a strict double category $\mathbf{C}$, and a map $X \rightarrow U\mathbf{C}$ (where $U\mathbf{C}$ is the underlying double graph with bigons of $\mathbf{C}$), there is a unique extension to a strict double functor from the free strict double category $FX \rightarrow \mathbf{C}$. Each 2-cell in $FX$ may be composed from the generators $X$, for example by horizontally composing the rows consisting of squares and vertical bigons; horizontally composing (whiskering) horizontal 1-cells and vertical compositions of horizontal bigons between the rows; and finally vertically composing all these horizontal composites. Hence we obtain a map $FX \rightarrow \mathbf{C}$ sending cells in $FX$ to the corresponding composites in $\mathbf{C}$. Functoriality is shown using the associativity and interchange laws.

Now by Proposition 7.10, in order to see that the two monads on **BiDblGph** agree, it is enough to see that the underlying bicategories of a free double bicategory and those of a free doubly weak double category both constitute the free bicategories on the underlying 2-graphs. For double bicategories this is clear because the only operations giving bigons are the bicategory operations; for doubly weak double categories this follows from the description in the previous paragraph (and the similar description of free bicategories on 2-graphs). $\square$

**Proposition 7.20.** *The forgetful functor $\mathbf{WDblCat}_{\mathbf{st}} \rightarrow \mathbf{BiDblGph}$ is not monadic. (That is to say, doubly weak double categories are distinct from double bicategories.)*

*Proof.* By Lemma 7.19, it suffices to exhibit a double bicategory that does not arise from any doubly weak double category. In a doubly weak double category, there is a bijection between 2-cells of shapes

![img-56.jpeg](img-56.jpeg)

obtained by composing on the top and bottom with the isomorphisms

![img-57.jpeg](img-57.jpeg)

We now construct a double bicategory without this property. Given any monoid $M$, let the double bicategory $\mathcal{C}_M$ have two 0-cells $A$ and $B$, one nonidentity vertical 1-cell $f: A \rightarrow B$, a vertical bigon

![img-58.jpeg](img-58.jpeg)

42

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

for each $m \in M$, no nonidentity horizontal arrows or bigons, and no nonidentity squares. The only square that the nontrivial vertical bigons can act on is the identity square

![img-59.jpeg](img-59.jpeg)

and we can simply say that it is fixed by this action. Thus, if $M$ is nontrivial, then in $\mathcal{C}_M$ there is no bijection between 2-cells of shapes

![img-60.jpeg](img-60.jpeg)

Hence $\mathcal{C}_M$ cannot arise from any doubly weak double category.

*Remark 7.21.* Given Lemma 7.19, the functor $\mathbf{WDblCat}_{\mathbf{st}} \rightarrow \mathbf{DblBicat}_{\mathbf{st}}$ is the canonical comparison functor to the category of algebras for the induced monad on $\mathbf{BiDblGph}$. When such a comparison functor is fully faithful (as it is in this case, by Corollary 7.11), the right adjoint forgetful functor (here $\mathbf{WDblCat}_{\mathbf{st}} \rightarrow \mathbf{BiDblGph}$) is said to be of *descent type* [BW05] or *premonadic* [Tho74]. There are many other equivalent characterizations of this property, which are summarized in [KP93, Theorem 2.4]; perhaps the most interesting is that *every doubly weak double category has a canonical presentation as a coequalizer of maps between doubly weak double categories that are freely generated by double graphs with bigons*.

The definition of tidy double bicategory is convenient because it is finite. However, it still contains redundancies that can be eliminated. If we pare it down to the bones, we obtain our most concise definition of doubly weak double category.

**Proposition 7.22.** *A doubly weak double category amounts to:*

- *a double graph,*
- *horizontal and vertical 1-cell composition and identity operations (as in a double category),*
- *horizontal and vertical square composition and identity operations (as in a double category), and*
- *horizontal and vertical associator and unitor squares (and their putative inverses) with identity 1-cells as their vertical and horizontal boundaries, respectively,*

*with appropriate sources and targets, such that*

- *the canonical map induced by composing with an identity square (in any of the four directions)*

![img-61.jpeg](img-61.jpeg)

DOUBLY WEAK DOUBLE CATEGORIES

43

is a bijection, per boundary, and

- if we define a vertical (resp. horizontal) bigon to be a square whose vertical (resp. horizontal) boundaries are identities:

$$\begin{array}{ccc} A & \xrightarrow{1_A^R} & A \\ f \downarrow & \alpha & \downarrow_g \\ B & \xrightarrow{1_B^R} & B \end{array} \qquad \begin{array}{ccc} A & \xrightarrow{f} & B \\ 1_A^V \downarrow & \beta & \downarrow_{1_B^V} \\ A & \xrightarrow{g} & B \end{array}$$

then these data with the derived bigon identity, composition, and action operations

$$\begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & 1 & \downarrow_1 \\ \cdot & \xrightarrow{f} & \cdot \end{array} \qquad \begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & \alpha & \downarrow_1 \\ \cdot & -x & \cdot \\ 1 \downarrow & \beta & \downarrow_1 \\ \cdot & \xrightarrow{g} & \cdot \end{array} \mapsto \begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & \alpha & \downarrow_1 \\ \cdot & -g & \cdot \\ \cdot & \xrightarrow{g} & \cdot \end{array} \mapsto \begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & \alpha & \downarrow_1 \\ \cdot & -g & \cdot \\ \cdot & \xrightarrow{g} & \cdot \end{array}$$

(and similarly in other directions) satisfy the laws of a double bicategory.

(Here one could use either of the two inverse bijections to define composition of bigons; it does not matter.)

*Proof.* The double bicategory so-defined is automatically tidy. Conversely, given any tidy double bicategory, we obtain an isomorphic one by replacing all the sets of bigons by the sets of squares to which they are in bijection by tidiness. After this replacement, the tidiness isomorphisms become identities, and all the composition operations on bigons become equal to the corresponding ones on squares; thus we have a structure as described in the statement. The two processes are evidently inverse up to isomorphism. □

This definition can be convenient when constructing examples that do not start with a given bicategory.

*Example 7.23.* As in Example 3.7, let $X$ be a topological space, let the 0-cells be points of $X$, the 1-cells be continuous paths $p : [0,1] \to X$, and the 2-cells be homotopy classes of continuous maps $[0,1] \times [0,1] \to X$ rel their boundaries. We take the composition operations on these data to be the usual ones, and the associator and unitor squares to be the usual reparametrizing homotopies. It is then straightforward to verify the axioms.

We will also see a worked example putting this definition to use in the next section.

44

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

### 8. CUBICAL BICATEGORIES

Next, we compare our definition of doubly weak double category with Garner's definition of cubical bicategory, which he described as follows [Gar10a]:

Definition. A cubical bicategory is given by sets of objects, of vertical arrows, of horizontal arrows and of squares, satisfying the obvious source and target criteria, together with operations of identity and binary composition for vertical and horizontal arrows, satisfying no laws at all; and finally, for every $n \times m$ grid of squares (where possibly $n$ or $m$ are zero), and every way of composing up the horizontal and vertical boundaries using the nullary and binary compositions, a composite square with those boundaries. The coherence axioms which this structure must satisfy say that any two ways of composing up a diagram of squares must give the same answer.

Just like Verity's definition, Garner's definition can be derived from ours by ignoring some of the structure of a double computad. But first, let us elaborate on the subtler points of this definition.

The condition that 'any two ways of composing up a diagram of squares must give the same answer' a priori constitutes infinitely many axioms involving grids of squares nested arbitrarily deeply. In particular, we have infinitely many axioms involving arbitrarily many $n \times 0$ and $0 \times m$ grids nested within other grids. For example, all of the following composites are made equal, since they represent the same formal $2 \times 2$ grid of squares:

![img-62.jpeg](img-62.jpeg)

DOUBLY WEAK DOUBLE CATEGORIES

45

![img-63.jpeg](img-63.jpeg)

To put it another way, equality between composite squares in the free cubical bicategory on a double graph is checked by comparing the boundaries and the induced grids of generating squares appearing in the composites. This leads to the following observation.

Recall that **DblGph** denotes the category of double graphs.

**Lemma 8.1.** *The algebras of the monad on DblGph induced by the forgetful functor $\mathbf{WDblCat}_{\mathbf{st}} \rightarrow \mathbf{DblGph}$ are precisely cubical bicategories.*

*Proof.* The above definition is obtained from the characterization in **Corollary 5.7** of the free doubly weak double category on a double computed, specialized to the case of double graphs. (The 2-cells in free *strict* double categories on double graphs are given by grids of squares; this is well-known and also follows as a special case of the description of free strict double categories in the proof of **Lemma 7.19**.) □

**Proposition 8.2.** *The forgetful functor $\mathbf{WDblCat}_{\mathbf{st}} \rightarrow \mathbf{DblGph}$ is not monadic. (That is to say, doubly weak double categories are distinct from cubical bicategories.)*

*Proof.* By **Lemma 8.1**, it suffices to exhibit a cubical bicategory that does not arise from any doubly weak double category. In a doubly weak double category, there is a bijection between 2-cells of shapes

![img-64.jpeg](img-64.jpeg)

obtained by composing on the top with the unitor isomorphism

![img-65.jpeg](img-65.jpeg)

46

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

We now construct a cubical bicategory without this property. Given any commutative monoid $M$ with identity $0_M$, let the cubical bicategory $\mathbf{C}_M$ have one 0-cell, and let the horizontal and vertical 1-cells both be freely generated, i.e. given by bracketed strings of 1. Let there be one 2-cell bordered on all sides by 1, which we label $0_M$

![img-66.jpeg](img-66.jpeg)

and let the 2-cells having any other particular boundary be identified with $M$. The composite of any grid of 2-cells will be given by simply adding up the elements of $M$ occurring in it.

Now if $M$ is nontrivial, then in $\mathbf{C}_M$ there is no bijection between 2-cells of shapes

![img-67.jpeg](img-67.jpeg)

Hence $\mathbf{C}_M$ cannot arise from any doubly weak double category. $\square$

However, Lemma 8.1 does also give us:

**Corollary 8.3.** *There is a canonical functor from doubly weak double categories to cubical bicategories.*

*Proof.* This is the standard comparison functor from the domain of any right adjoint to the category of algebras for the monad induced by the adjunction. $\square$

We now show that, as was the case for double bicategories, this comparison functor is fully faithful, and we characterize the image. (It is possible to quickly see that the comparison functor is fully faithful using Proposition 7.22, but it will take us some additional work to establish the following simple characterization of the image.)

**Definition 8.4.** A **tidy cubical bicategory** is a cubical bicategory such that the canonical map induced by composing with an identity square (in any of the four directions)

![img-68.jpeg](img-68.jpeg)

is a bijection, per boundary. In terms of operations and laws, this means a tidy cubical bicategory is additionally equipped with four conversion operations, defined

DOUBLY WEAK DOUBLE CATEGORIES

47

on squares of forms

![img-69.jpeg](img-69.jpeg)

satisfying laws that ensure these are sent to squares of the form

![img-70.jpeg](img-70.jpeg)

and that these operations are inverse to composing with identities.

**Proposition 8.5.** *The comparison functor of Corollary 8.3 is an equivalence onto the full subcategory of tidy cubical bicategories.*

*Proof.* Suppose given a tidy cubical bicategory. We will construct a tidy double bicategory using the squares-only definition from Proposition 7.22. That is, we require a double graph equipped with binary composition and identity operations, such that the canonical maps induced by composing with identities are bijections per boundary, and the squares and “bigons” (squares bordered appropriately by identities) with the induced operations have the structure of a double bicategory.

Any cubical bicategory has an underlying double graph with binary composition operations and identities (among other more general composition operations). In particular, an identity square for (say) vertical composition is obtained by composing a $0 \times 1$ grid using single identity 1-cells as the composites of the nullary left and right boundaries. A *tidy* cubical bicategory moreover by definition has the same identity square cancellation condition of Proposition 7.22.

As in Proposition 7.22, we define horizontal (vertical) bigons to be squares bordered by vertical (horizontal) identity 1-cells, and we define the bigon-on-square and bigon-on-bigon composition operations of a double bicategory by composing squares then applying the given identity square cancellation bijection. We display this again here for convenience:

![img-71.jpeg](img-71.jpeg)

Now we observe that the structure of a cubical bicategory does contain coherence 2-cells bounded by identities, as in the structure of a double bicategory. Any sequence of (say) horizontal 1-cells

$$\cdot \xrightarrow{f_1} \cdot \xrightarrow{f_2} \dots \xrightarrow{f_{n-1}} \cdot \xrightarrow{f_n} \cdot$$

can be regarded as a $0 \times n$ grid of composable squares. Therefore, given any two ways of bracketing a composite of these 1-cells (perhaps including insertion of identities), we can take those to be the top and bottom composites for this grid,

48

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

use single identity 1-cells as the composites of the nullary left and right boundaries, and obtain a coherence 2-cell. We will write all of these coherence 2-cells as “≅”, save for the identity squares written as “1” (which, observe, are a special case of coherence 2-cells), and we often write elongated = signs for identity 1-cells. For instance, here is horizontal associativity:

$$\begin{array}{c} \cdot \xrightarrow{f(gh)} \cdot \\ \Big\| \quad \cong \quad \Big\| \\ \cdot \quad \xrightarrow{(fg)h} \cdot \end{array}$$

Our discussion at the beginning of this section implies that two formal composites, i.e. squares in a free cubical bicategory, constructed from the same grid of squares are equal if and only if they have the same boundary. (By definition, the 2-cells in a free cubical bicategory on a double graph are compatible grids of squares with bracketed boundaries.) In particular, any formal composite featuring only coherence cells is itself a coherence cell, since there is at most one formal composite with any given boundary featuring *no* squares.

We next verify the double bicategory laws. The double-categorical interchange laws are automatic from the cubical bicategory structure. To show the remaining laws, note that in a *tidy* cubical bicategory, we have cancellation with respect to composing with identities. Therefore one strategy to show an equation between two squares is to compose both of them with identities and then to express the resulting two squares as formal composites derived from the same grid. (Then since we know these squares must be equal, by cancellation the original squares are equal.)

Let us start with the unitar naturality laws. We must show that the following compositions with coherence bigons are equal:

$$\begin{array}{c} \boxed{\cong} \\ \boxed{\zeta} \end{array} \mapsto \boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{(1\zeta)} \mapsto \boxed{\cong} \\ \boxed{(1\zeta)} \mapsto \boxed{(1\zeta)} \mapsto \boxed{(1\zeta)}$$

Observe

$$\begin{array}{c} \boxed{\cong} \\ \boxed{\zeta} \end{array} = \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{\zeta} \mapsto \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{\zeta} \mapsto \boxed{\begin{array}{c} 1 \\ \hline \end{array}} = \boxed{\begin{array}{c} \zeta \\ \hline 1 \end{array}}$$

since each is a formal composite constructed from the same $1 \times 1$ grid $\zeta$. Hence by definition of bigon composition we have

$$\begin{array}{c} \boxed{1} \\ \boxed{\cong} \\ \boxed{\zeta} \end{array} = \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{\zeta} \mapsto \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{1} \mapsto \boxed{\begin{array}{c} \zeta \\ \hline 1 \end{array}} = \boxed{\begin{array}{c} \zeta \\ \hline 1 \end{array}}$$

and therefore by cancelling identities

$$\boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{\zeta} \mapsto \boxed{(1\zeta)} \mapsto \boxed{\cong}$$

DOUBLY WEAK DOUBLE CATEGORIES

49

The other unitor naturality laws are analogous, as well as the associator naturality laws, where we use

$$\begin{array}{c} \boxed{f(gh)} \\ \boxed{\cong} \\ \boxed{(\zeta\xi)\psi} \\ \boxed{(fg)h} \end{array} = \boxed{f(gh)} \begin{array}{c} \boxed{f(gh)} \\ \boxed{1} \\ \boxed{\zeta\xi\psi} \\ \boxed{(fg)h} \end{array} \quad \text{and} \quad \boxed{f(gh)} \begin{array}{c} \boxed{f(gh)} \\ \boxed{\zeta(\xi\psi)} \\ \boxed{\cong} \\ \boxed{(fg)h} \end{array} = \boxed{f(gh)} \begin{array}{c} \boxed{f(gh)} \\ \boxed{\zeta\xi\psi} \\ \boxed{1} \\ \boxed{(fg)h} \end{array}$$

constructed from the same $1 \times 3$ grid (and similarly in the vertical case, with a $3 \times 1$ grid). We also have that the inverse pairs of coherence cells do behave as such:

$$\boxed{\begin{array}{c} \boxed{\cong} \\ \boxed{\cong} \end{array}} = \boxed{\begin{array}{c} 1 \\ \boxed{1} \end{array}}$$

Similarly the pentagon and triangle laws of a bicategory are satisfied because all formal compositions of coherence cells agree, as noted above.

The next law we show is the identity square commutativity law of a double bicategory. Observe for any square $\alpha$, we have the equations

$$\boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha & 1 \end{array}} = \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \end{array}} \quad \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \end{array}} = \boxed{\begin{array}{c|c|c} 1 & \alpha & 1 \\ \hline 1 & 1 & 1 \end{array}}$$

since both sides of each equation have the same boundary and are formal composites constructed from the $1 \times 1$ grid $\alpha$. (Of course, whenever we compose a grid, we must choose some bracketing of its boundary, but we will omit such annotations from our diagrams, trusting the reader to supply suitable choices.)

When $\alpha$ is moreover a *bigon* (bordered on either side by identities), we get

$$\boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha & 1 \end{array}} = \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \end{array}} = \boxed{\begin{array}{c|c|c} 1 & \alpha & 1 \\ \hline 1 & 1 & 1 \end{array}}$$

(The composite in the middle agrees the two from above since there is a unique coherence cell for any bracketed boundary of a $0 \times 0$ grid.) Hence by cancelling the identities on the left and right, we obtain

$$\boxed{\begin{array}{c} 1 \\ \hline \alpha \end{array}} = \boxed{\begin{array}{c} \alpha \\ \hline 1 \end{array}}$$

Horizontal identity square commutativity is similar.

The bigon identity laws are trivial. We also have the associativity laws for composing bigons (with squares or bigons):

$$\boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha\beta & \zeta \\ \hline 1 & 1 & 1 \end{array}} = \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \alpha\beta & \zeta \\ \hline \end{array}} = \boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline \alpha & \beta & \zeta \\ \hline 1 & 1 & 1 \end{array}} = \boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline \alpha & 1 & \beta\zeta \\ \hline 1 & 1 & 1 \end{array}} = \boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha & \beta\zeta \\ \hline 1 & 1 & 1 \end{array}}$$

and the action compatibility laws:

50

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

$$\begin{array}{l} \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{(\alpha\zeta)\beta} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{\alpha\zeta} \quad \boxed{\beta} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} = \begin{array}{r} \boxed{\cong} \quad \boxed{\phantom{\cong}} \\ \boxed{\alpha\zeta} \quad \boxed{\phantom{\beta}} \\ \boxed{\phantom{\cong}} \quad \boxed{\phantom{\cong}} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{\alpha} \quad \boxed{\phantom{\zeta}} \quad \boxed{\phantom{\beta}} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} \\ = \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{\alpha} \quad \boxed{\zeta\beta} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} = \begin{array}{r} \boxed{\cong} \quad \boxed{\phantom{\cong}} \\ \boxed{\alpha(\zeta\beta)} \quad \boxed{1} \\ \boxed{\phantom{\cong}} \quad \boxed{\phantom{\cong}} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{\alpha(\zeta\beta)} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} \\ \begin{array}{r} \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{\alpha(\zeta)} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \\ \boxed{\beta} \quad \boxed{\alpha} \\ \boxed{\phantom{\beta}} \quad \boxed{\phantom{\alpha}} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{\alpha} \\ \boxed{\beta} \quad \boxed{\phantom{\alpha}} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{\alpha} \\ \boxed{1} \quad \boxed{\phantom{\alpha}} \\ \boxed{\beta\zeta} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{\alpha(\beta\zeta)} \end{array} \end{array}$$

Last we have the bigon-square sandwiching laws, associativity laws, and interchange laws:

$$\begin{array}{l} \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \\ \boxed{\zeta\beta} \quad \boxed{\phantom{\zeta\beta}} \quad \boxed{\phantom{\xi}} \\ \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \end{array} = \begin{array}{r} \boxed{\cong} \quad \boxed{\phantom{\cong}} \\ \boxed{\phantom{\cong}} \\ \boxed{\zeta\beta} \quad \boxed{\phantom{\xi}} \\ \boxed{\phantom{\cong}} \\ \boxed{\phantom{\cong}} \end{array} = \begin{array}{r} \boxed{\boxed{\phantom{\cong}} \quad \boxed{\phantom{\cong}} \\ \boxed{\phantom{\cong}} \\ \boxed{\phantom{\zeta}} \quad \boxed{\phantom{\beta}} \quad \boxed{\phantom{\xi}} \\ \boxed{\phantom{\cong}} \end{array} = \begin{array}{r} \boxed{\boxed{\phantom{\cong}} \quad \boxed{\phantom{\cong}} \\ \boxed{\phantom{\cong}} \\ \boxed{\phantom{\zeta}} \quad \boxed{\phantom{\beta}\phantom{\xi}} \\ \boxed{\phantom{\cong}} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \\ \boxed{\zeta} \quad \boxed{\phantom{\beta}\phantom{\xi}} \\ \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{1} \end{array} \\ \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{1} \quad \boxed{\beta\zeta} \quad \boxed{\phantom{\beta}\phantom{\xi}} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} = \begin{array}{r} \boxed{\cong} \quad \boxed{\phantom{\cong}} \\ \boxed{\phantom{\cong}} \\ \boxed{\beta\zeta} \quad \boxed{\phantom{\xi}} \\ \boxed{\phantom{\cong}} \end{array} = \begin{array}{r} \boxed{\phantom{\cong}} \\ \boxed{\phantom{\beta}} \quad \boxed{\phantom{\zeta}} \quad \boxed{\phantom{\xi}} \end{array} = \begin{array}{r} \boxed{1} \quad \boxed{1} \quad \boxed{1} \\ \boxed{\beta} \quad \boxed{\phantom{\zeta}} \quad \boxed{\phantom{\xi}} \\ \boxed{1} \quad \boxed{1} \quad \boxed{1} \end{array} \\ \begin{array}{r} \boxed{1} \quad \boxed{\alpha\zeta} \\ \boxed{1} \quad \boxed{\phantom{\alpha}\phantom{\xi}} \\ \boxed{\phantom{\beta}\phantom{\xi}} \end{array} = \begin{array}{r} \boxed{\phantom{\alpha}} \quad \boxed{\phantom{\zeta}} \\ \boxed{\phantom{\beta}} \quad \boxed{\phantom{\xi}} \end{array} \end{array} = \begin{array}{r} \boxed{\phantom{\alpha}} \quad \boxed{\phantom{\zeta}} \\ \boxed{\phantom{\beta}} \quad \boxed{\phantom{\xi}} \end{array} \end{array}$$

The reader is warned that the above calculations are somewhat subtle, as the visual representations omit detail. Formally, each diagram is to be decomposed into particular nested parenthesized grids. For example, in the above proof of the bigon-square sandwiching law, we start with a $5 \times 2$ grid. Then we reinterpret this as a $1 \times 2$ grid nested within the middle of a $3 \times 1$ grid nested within the middle of a $3 \times 1$ grid (using that both this and the previous composite represent the same formal $1 \times 2$ grid). Then we reinterpret the middle $3 \times 1$ grid as a $1 \times 3$ grid, and the rest of the argument proceeds symmetrically. Also note that in certain cases, a correct choice of parenthesization along the boundary allows the shown steps to be performed, whereas an incorrect choice of parenthesization does not. For example, in the same proof, the bracketing $(1((1\rightarrow)1))1$ for the left and right boundaries works, whereas the bracketing $((11)\rightarrow)(11)$ does not.

Finally, we observe that the processes of translation between tidy double bicategories and tidy cubical bicategories are inverse. It is clear that a tidy double bicategory is recovered from the cubical bicategory structure of its underlying doubly weak double category, since all the data of Proposition 7.22 are included in the

DOUBLY WEAK DOUBLE CATEGORIES

51

structure. Conversely, all the structure of a tidy cubical bicategory is determined by the underlying tidy double category structure, since an arbitrary grid composition operation is obtained by binarily composing the grid and acting with coherence isomorphism bigons to rebracket the boundary as desired. □

**Corollary 8.6.** *The forgetful functor from doubly weak double categories to cubical bicategories is fully faithful.* □

**Corollary 8.7.** *The forgetful functor $\mathbf{WDblCat}_{\text{st}} \rightarrow \mathbf{DblGph}$ is faithful and conservative.* □

Thus we can still regard a doubly weak double category as “structure” on an underlying double graph, though that structure is not monadic.

*Remark 8.8.* Similarly to *Remark 7.21*, Corollary 8.6 says that the forgetful functor $\mathbf{WDblCat} \rightarrow \mathbf{DblGph}$ is of descent type or premonadic, and this implies that every doubly weak double category has a canonical presentation as a coequalizer of maps between doubly weak double categories that are freely generated by double graphs.

## 9. A FINITE AXIOMATIZATION

Tidy double bicategories do constitute a finite axiomatization of doubly weak double categories: they are essentially algebraic (presenting a finite limit theory) with finitely many types, finitely many operations, and finitely many equations.

However, they do not share the good property of the infinitary definition in Section 5 of being presented as monadic over a presheaf category in which *pseudofunctors* can also be represented as presheaf maps. (A tidy double bicategory requires operations whose domains involve identity 1-cells; however, identity 1-cells are not strictly preserved by pseudofunctors.)

We now present another finitary definition, exhibiting doubly weak double categories as monadic over a presheaf category with domain a finite subcategory of that of double computads. The practical use of this particular presentation is questionable, but the point is to illustrate that something like it can be done. There are many axioms, but most of them are adaptations of the axioms for double bicategories.

A **monogon** in a double computad is a 2-cell of shape $2_{0,0}^{1,0}$, $2_{0,0}^{0,1}$, $2_{1,0}^{0,0}$, or $2_{0,1}^{0,0}$. A **double graph with monogons** is a double computad in which all 2-cells are monogons or squares. Let $\mathbf{MoDblGph}$ denote the category of double graphs with monogons, a functor category whose domain is a suitable full subcategory of $\mathbb{C}_d$:

![img-72.jpeg](img-72.jpeg)

**Definition 9.1.** A **weak composition structure** on a double graph with monogons consists of the following operations.

52

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

- Horizontal and vertical binary composition and identity operations for 1-cells and squares, as in a double bicategory.
- Four 2-cell composition operations sending two compatible squares and two compatible monogons to a square:

![img-73.jpeg](img-73.jpeg)

- Four 2-cell composition operations sending a square and three compatible monogons to a monogon:

![img-74.jpeg](img-74.jpeg)

- A 2-cell composition operation sending four compatible monogons (one of each type) to a square:

![img-75.jpeg](img-75.jpeg)

- Operations sending horizontal 1-cells to left and right unitor squares and their inverses, and likewise for vertical 1-cells:

![img-76.jpeg](img-76.jpeg)

- Operations sending length three paths of horizontal 1-cells to associator squares and their inverses, and likewise for vertical 1-cells:

![img-77.jpeg](img-77.jpeg)

DOUBLY WEAK DOUBLE CATEGORIES

53

- Operations sending 0-cells to horizontal and vertical identity composition monogons and their inverses:

![img-78.jpeg](img-78.jpeg)

Moreover, these operations must satisfy the following laws.

- Source and target laws for horizontal and vertical identity and binary composition operations of 1-cells and squares, as in a double bicategory.
- Source and target laws for unitor and associator squares, 2-cell composition operations, and identity composition monogons, as appropriate.
- Identity laws:

![img-79.jpeg](img-79.jpeg)

- Associativity laws that say the three possible ways of composing each of the following diagram shapes are equal:

![img-80.jpeg](img-80.jpeg)

- Horizontal unitor and associator invertibility laws:

![img-81.jpeg](img-81.jpeg)

Likewise, analogous laws for vertical unitors and associators.

54

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

- Horizontal unitor and associator naturality laws:

![img-82.jpeg](img-82.jpeg)

Likewise, analogous laws for vertical unitors and associators.

- Horizontal bicategory triangle and pentagon laws:

![img-83.jpeg](img-83.jpeg)

(By the associativity laws above, we can use any of the three possible ways to compose the right hand side of the pentagon equation. Here and elsewhere we do not annotate how each diagram is built up from the basic composition operations, trusting the reader to compose the diagrams up in a suitable way.)

Likewise, analogous vertical bicategory pentagon and triangle laws.

- The square interchange laws as in a double category (the identity compatibility law, the identity interchange laws, and the square composition interchange law).
- Interchange laws involving monogons and horizontal composition of squares:

![img-84.jpeg](img-84.jpeg)

where

![img-85.jpeg](img-85.jpeg)

Likewise, the three other analogous (rotated) interchange laws.

DOUBLY WEAK DOUBLE CATEGORIES

55

- A law ensuring that identity composition monogons correspond to identities:

![img-86.jpeg](img-86.jpeg)

- Associativity laws that say the two possible ways of composing each of the following diagram shapes are equal:

![img-87.jpeg](img-87.jpeg)

- Identity commutativity laws:

![img-88.jpeg](img-88.jpeg)

(By the associativity laws above, we can use either of the two possible ways to compose the middle diagram.)

Likewise, analogous (rotated) laws for horizontal identities.

- Associativity laws for sandwiching monogons between squares:

![img-89.jpeg](img-89.jpeg)

Likewise, the other analogous (rotated) associativity law for vertical composition.

- Associativity laws for squares composed beside monogons:

![img-90.jpeg](img-90.jpeg)

56

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

Likewise, the three other analogous (rotated) associativity laws.

- Associativity laws that say the two possible ways of composing each of the following diagram shapes are equal:

![img-91.jpeg](img-91.jpeg)

- Laws ensuring that the canonical map from monogons to squares is undone by the canonical map from appropriately degenerate squares to monogons:

![img-92.jpeg](img-92.jpeg)

Likewise, three other analogous (rotated) laws.

Any doubly weak double category has an underlying double graph with monogons, equipped with weak composition structure. Conversely, we have the following.

**Proposition 9.2.** *Any double graph with monogons having a weak composition structure $\mathbf{X}$ has an underlying tidy double bicategory:*

- *The 0-cells, 1-cells, squares, 1-cell identities and composition, and square identities and composition are as in $\mathbf{X}$.*
- *The horizontal bigons are the squares in $\mathbf{X}$ bordered by vertical identities. The vertical bigons are the squares in $\mathbf{X}$ bordered by horizontal identities.*
- *Horizontal composition of horizontal bigons, horizontal unitors, and horizontal associators are as in $\mathbf{X}$. The top and bottom actions of horizontal bigons $\alpha$ on squares $\zeta$ are defined as*

![img-93.jpeg](img-93.jpeg)

*and vertical composition of bigons $\alpha$ and $\beta$ is defined as*

![img-94.jpeg](img-94.jpeg)

*Similarly for the vertical bicategory.*

DOUBLY WEAK DOUBLE CATEGORIES

57

*Proof.* Notice that the two ways of defining vertical composition of bigons do in fact agree, using identity laws, identity composition monogons, and identity commutativity:

![img-95.jpeg](img-95.jpeg)

The interchange laws for the bicategories and for the bigon-on-square actions come straightforwardly from the monogon interchange laws, identity composition monogon law, and identity laws.

All other laws of a double bicategory correspond directly to laws of weak composition structure. $\square$

**Proposition 9.3.** *The category of double graphs with monogons equipped with weak composition structure (and homomorphisms) is equivalent to the category of doubly weak double categories (and strict functors) **WDblCat$_{st}$.***

*Proof.* First, observe that the canonical maps between squares bordered by identities on three sides and monogons

![img-96.jpeg](img-96.jpeg)

are inverse:

![img-97.jpeg](img-97.jpeg)

(with the other direction stipulated as a law in the definition).

58

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

Now all of the operations are determined by the double bicategory structure. Indeed, we have

![img-98.jpeg](img-98.jpeg)

and

The right hand sides can be interpreted in the tidy double bicategory. It follows that so can

**Corollary 9.4.** *The forgetful functor* $\mathbf{WDblCat}_{\mathbf{st}} \rightarrow \mathbf{MoDblGph}$ *is monadic.*

*Remark 9.5.* Alternatively, the 4-ary monogon to square operation could be replaced without difficulty by two operations that send two monogons and a compatible 1-cell to a square:

![img-99.jpeg](img-99.jpeg)

DOUBLY WEAK DOUBLE CATEGORIES

59

We also note that two of the operations combining two squares and two monogons can be derived from the others, e.g.:

where

*Remark 9.6.* Less minimal than squares and monogons, but perhaps more natural, is the full subcategory $\mathbb{E} \hookrightarrow \mathbb{C}_{\mathbf{d}}$ including $0, 1^H, 1^V$, and $2_{c,d}^{a,b}$ for all $a, b, c, d \leq 1$, so that $[\mathbb{E}, \mathbf{Set}]$ gives the “subunary” double computads. An axiomatization for doubly weak double categories presenting a monad on $[\mathbb{E}, \mathbf{Set}]$ could presumably be given involving a large number of binary 2-cell composition operations, removing the need for the unusual 4-ary operations we have given. As a middle ground, one could also give a definition using monogons, bigons, and squares (involving both binary and ternary 2-cell composition operations).

It is tempting to conjecture that the forgetful functor $\mathbf{WDblCat}_{\mathbf{st}} \to [\mathbb{E}, \mathbf{Set}]$ will be monadic when $\mathbb{E}$ is any full subcategory of $\mathbb{C}_{\mathbf{d}}$ including the 0-cells, 1-cells, monogons, and squares. However, this appears not to be true: consider the case where $\mathbb{E}$ consists of only these and the 2-cell shape $2_{0,0}^{2,0}$.

#### APPENDIX A. TRANSFORMATIONS AND MODIFICATIONS

In this section we discuss transformations and modifications of implicit structures. We will see that when $\mathbf{C}$ and $\mathbf{D}$ are implicit 2-categories, we obtain an implicit 2-category $\operatorname{Hom}(\mathbf{C}, \mathbf{D})$; in the case $\mathbf{C}$ and $\mathbf{D}$ are representable, this is the usual bicategory of transformations and modifications of bicategories. More than this, we will see that the *lax* and *colax* transformations of implicit 2-categories (resp. bicategories) assemble into an *implicit double category* (resp. *doubly weak double category*) $\operatorname{Hom}_{\mathbf{co}/\mathbf{lax}}(\mathbf{C}, \mathbf{D})$, providing a natural source of examples of doubly weak double categories.

It is also true that when $\mathbf{C}$ and $\mathbf{D}$ are implicit double categories (resp. doubly weak double categories), we have an implicit double category (resp. doubly weak double category) $\operatorname{Hom}(\mathbf{C}, \mathbf{D})$. However, we will focus on the 2-categorical case. This is for reasons of space and also because we are unable to provide motivation for studying transformations and modifications of doubly weak double categories

60

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

(we have no examples). Still, all of the definitions in this section readily generalize to double-categorical analogues.

To figure out what the content of $\operatorname{Hom}(\mathbf{C}, \mathbf{D})$ ought to be, recall the defining property of an internal hom: it is universal such that $\mathbf{C} \otimes \operatorname{Hom}(\mathbf{C}, \mathbf{D})$ maps into $\mathbf{D}$. However, this leaves us to wonder what the monoidal product $\otimes$ ought to be. In ordinary 2-category theory, the relevant monoidal product is the *Gray tensor product* [Gra74], which composes 2-categories as if they were the homs in a semistrict tricategory (so that closure for $\otimes$ induces a semistrict tricategory of 2-categories).

This composition can be represented very cleanly using string diagrams, as described in [Mor22]. Namely, a string diagram for $\mathbf{C} \otimes \mathbf{D}$ consists of a string diagram for $\mathbf{C}$ superimposed over a string diagram for $\mathbf{D}$. For example, diagrams in $\mathbf{C} \cong \operatorname{Hom}(\mathbf{1}, \mathbf{C})$ can be composed with diagrams in $\operatorname{Hom}(\mathbf{C}, \mathbf{D})$ to yield diagrams in $\mathbf{D} \cong \operatorname{Hom}(\mathbf{1}, \mathbf{D})$:

![img-100.jpeg](img-100.jpeg)

The Gray tensor product is easy to express in terms of implicit structures. Recall that a **shuffle** of linearly ordered sets is a compatible linear order on their disjoint union.

**Definition A.1.** Let $\mathbf{C}$ and $\mathbf{D}$ be implicit 2-categories. The **Gray tensor product** of $\mathbf{C}$ and $\mathbf{D}$, denoted $\mathbf{C} \otimes \mathbf{D}$, is an implicit 2-category defined as follows.

- A 0-cell in $\mathbf{C} \otimes \mathbf{D}$ is a pair $(c, d)$ of a 0-cell $c$ in $\mathbf{C}$ and a 0-cell $d$ in $\mathbf{D}$.
- A 1-cell in $\mathbf{C} \otimes \mathbf{D}$ is *either*
  - a pair $(f, d): (c, d) \rightarrow (c', d)$ of a 1-cell $f: c \rightarrow c'$ in $\mathbf{C}$ and a 1-cell $d$ in $\mathbf{D}$, *or*
  - a pair $(c, g): (c, d) \rightarrow (c, d')$ of a 0-cell $c$ in $\mathbf{C}$ and a 1-cell $g: d \rightarrow d'$ in $\mathbf{D}$.
  Equivalently, a path of 1-cells in $\mathbf{C} \otimes \mathbf{D}$ is a *shuffle* of a path of 1-cells in $\mathbf{C}$ and a path of 1-cells in $\mathbf{D}$.
- A 2-cell in $\mathbf{C} \otimes \mathbf{D}$, with source and target each a shuffle of a path in $\mathbf{C}$ and a path in $\mathbf{D}$, is a pair $(\alpha, \beta)$ of a 2-cell $\alpha$ with the source and target paths in $\mathbf{C}$ and a 2-cell $\beta$ with the source and target paths in $\mathbf{D}$.
- Composition of 2-cells is by composition in $\mathbf{C}$ and $\mathbf{D}$.

DOUBLY WEAK DOUBLE CATEGORIES

61

We also define \(\otimes\) on functors in the obvious way: if \(F\colon \mathbf{C}\to \mathbf{D}\) and \(G\colon \mathbf{C}'\to \mathbf{D}'\) are functors of implicit 2-categories, then \(F\otimes G\) sends each cell called \((x,y)\) to the cell called \((F(x),G(y))\) with appropriate boundary.

Remark A.2. This is the usual Gray tensor product of strict 2-categories, specialized to implicit 2-categories (i.e. the path 2-category of the Gray tensor product of implicit 2-categories is the usual Gray tensor product of their path 2-categories). The description of the 2-cells given here follows from the equivalence (see e.g. [Gur13, Corollary 3.22]) between the Gray tensor product of 2-categories \(\mathbf{C} \otimes \mathbf{D}\) and the cartesian product of 2-categories \(\mathbf{C} \times \mathbf{D}\).

Remark A.3. The above definition easily generalizes from a binary product to an n-ary product, by replacing pairs and binary shuffles with n-tuples and n-ary shuffles. In particular, observe that the empty Gray tensor product defined in this way is an implicit 2-category with one 0-cell denoted () and no other non-identity cells.

Proposition A.4. I-2-Cat is symmetric monoidal with respect to \(\otimes\).

Sketch of proof. Functoriality of  \( \otimes \)  is immediate from the definition. Moreover,  \( \otimes \)  is associative, unital (Remark A.3), and symmetric up to coherent natural isomorphism, by reparenthesizing and reordering the names of tuples. ☐

In Section 2 we defined an implicit 2-category as a strict 2-category whose 1-cells are free, and we defined a functor of implicit 2-categories as a 2-functor sending the generating 1-cells to generating 1-cells. Now we define a (lax or colax) transformation of implicit 2-category functors as a (lax or colax) natural transformation of 2-functors whose components are generating 1-cells, and we define a modification of implicit 2-category transformations as a modification of (compositions of) these 2-category natural transformations. We spell out the details below.

These definitions are appropriate in that they provide closure for the Gray tensor product (to be shown in Proposition A.10), and they exactly give the usual notions of transformations and modifications in bicategories, under the correspondence between representable implicit 2-categories and bicategories (to be shown in Proposition A.15).

Definition A.5. Let \(F\) and \(G\) be functors between implicit 2-categories \(\mathbf{C}\) and \(\mathbf{D}\). A colax transformation \(\sigma: F \to G\) consists of

- for each 0-cell \(A\) in \(\mathbf{C}\), a 1-cell \(\sigma_A\) in \(\mathbf{D}\):

\[
F A \xrightarrow {\sigma_ {A}} G A
\]

![img-101.jpeg](img-101.jpeg)

- for each 1-cell \( f \colon A \to B \) in \( \mathbf{C} \), a 2-cell \( \sigma_f \) in \( \mathbf{D} \):

![img-102.jpeg](img-102.jpeg)

![img-103.jpeg](img-103.jpeg)

62

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

such that for each 2-cell $\alpha$ in $\mathbf{C}$, we have

![img-104.jpeg](img-104.jpeg)

A **lax transformation** is defined dually, with transformation component 1-cells at the northwest and southeast corners of diagrams (diagrams mirrored).

When the $\sigma_f$ 2-cells are all invertible, we call $\sigma$ simply a **transformation**.

![img-105.jpeg](img-105.jpeg)

*Remark A.6.* A transformation is both a colax transformation and a lax transformation: given a colax transformation where the $\sigma_f$ 2-cells are all invertible, the inverse 2-cells $\sigma_f^{-1}$ are components of a lax transformation, and vice versa.

![img-106.jpeg](img-106.jpeg)

Just as a transformation is a morphism of functors, a modification is a morphism of transformations. The most commonly seen definition of modification goes between two (lax or colax) transformations. However, there is a more general definition of modification that involves both *lax* and *colax* transformations. We actually get a (implicit) *double category* $\text{Hom}_{\text{co/lax}}(\mathbf{C}, \mathbf{D})$ where the horizontal arrows are lax transformations and the vertical arrows are colax transformations.

DOUBLY WEAK DOUBLE CATEGORIES

63

# Definition A.7. A modification

![img-107.jpeg](img-107.jpeg)

![img-108.jpeg](img-108.jpeg)

where $\pi_i$ and $\tau_i$ are lax transformations and $\rho_i$ and $\sigma_i$ are colax transformations of functors $\mathbf{C} \rightarrow \mathbf{D}$ consists of for each 0-cell $A$ in $\mathbf{C}$ a 2-cell $\Gamma_A$ in $\mathbf{D}$:

![img-109.jpeg](img-109.jpeg)

![img-110.jpeg](img-110.jpeg)

such that for any 1-cell $f: A \rightarrow B$ in $\mathbf{C}$, we have

![img-111.jpeg](img-111.jpeg)

64

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

![img-112.jpeg](img-112.jpeg)

We define **horizontal compositions** and **vertical compositions** of modifications componentwise. Likewise **horizontal (lax) identity** and **vertical (colax) identity** modifications are identities componentwise.

**Proposition A.8.** *Functors, lax and colax transformations, and modifications between* $\mathbf{C}$ *and* $\mathbf{D}$ *form an implicit double category* $\mathrm{Hom}_{\mathbf{co}/\mathbf{lax}}(\mathbf{C}, \mathbf{D})$ *(via composition of modifications).*

*Proof.* The associativity, unit, and interchange laws are inherited from the 2-cells in $\mathbf{D}$. $\square$

We denote by $\mathrm{Hom}(\mathbf{C}, \mathbf{D})$ the implicit 2-category whose 0-cells are functors $\mathbf{C} \to \mathbf{D}$, 1-cells are *transformations*, and 2-cells are modifications between these.

*Remark A.9.* Given a colax transformation of implicit 2-category functors, if every component 1-cell is a left adjoint, we obtain (upon choosing adjunctions) a lax transformation in the other direction (where the new component 2-cells are the *mates* of the old ones). A *conjoint pair* in $\mathrm{Hom}_{\mathbf{co}/\mathbf{lax}}(\mathbf{C}, \mathbf{D})$ is such a pair of colax and lax transformations, with component 1-cells in left and right adjoint pairs.

On the other hand, as noted in **Remark A.6**, given a colax transformation, if every component 2-cell is invertible, we obtain a lax transformation in the same direction; this is the content of a (non lax or colax) transformation. A *companion pair* in $\mathrm{Hom}_{\mathbf{co}/\mathbf{lax}}(\mathbf{C}, \mathbf{D})$ is (up to isomorphism) such a transformation.

In general, implicit 2-categories may be identified with implicit double categories having horizontal and vertical 1-cells in assigned companion pairs. (It is the same as in the strict case; the translation from (implicit) 2-categories to such (implicit) double categories is the “squares” or “quintets” construction of **Example 3.6**.) The implicit 2-category $\mathrm{Hom}(\mathbf{C}, \mathbf{D})$ is then embedded in $\mathrm{Hom}_{\mathbf{co}/\mathbf{lax}}(\mathbf{C}, \mathbf{D})$ as the 1-cells with companions. (The former is recovered up to equivalence from the latter through the right adjoint to the quintets construction.)

It still remains to verify that $\mathrm{Hom}(\mathbf{C}, \mathbf{D})$ in fact provides an internal hom for the Gray tensor product. In other words, $\mathbf{C} \otimes \mathbf{D}$ is universal with a map $\mathbf{C} \to \mathrm{Hom}(\mathbf{D}, \mathbf{C} \otimes \mathbf{D})$:

**Proposition A.10.** **I-2-Cat** *is closed with respect to* $\otimes$.

*In particular, the Gray tensor product* $\mathbf{C} \otimes \mathbf{D}$ *is the free implicit 2-category on the following data and laws:*

- *For every 0-cell $c$ of* $\mathbf{C}$, *there is a functor* $(c, -): \mathbf{D} \to \mathbf{C} \otimes \mathbf{D}$.
- *For every 1-cell $f: c \to d$ of* $\mathbf{C}$, *there is a transformation* $(f, 1): (c, -) \to (d, -)$.

DOUBLY WEAK DOUBLE CATEGORIES

65

![img-113.jpeg](img-113.jpeg)

FIGURE 2. A generic 2-cell $(\alpha, \beta)$ in $\mathbf{C} \otimes \mathbf{D}$.

- For every 2-cell $\alpha$ of $\mathbf{C}$, there is a modification $(\alpha, 1)$ between the associated transformations.
- Such modifications compose as in $\mathbf{C}$, with identities as in $\mathbf{C}$.

Proof. Note first that the construction $\operatorname{Hom}(\mathbf{D}, \mathbf{X})$ is functorial in $\mathbf{X}$ (since functors, transformations, modifications, and their compositions are shapes consisting of cells and equations in $\mathbf{X}$), and a map from $\mathbf{C}$ into $\operatorname{Hom}(\mathbf{D}, \mathbf{X})$ is precisely the data in $\mathbf{X}$ as described above.

It is easy to see that $\mathbf{C} \otimes \mathbf{D}$ contains such data. Now suppose $\mathbf{X}$ also contains such data. We must check that the induced map on the putative generating cells extends to a unique functor $\mathbf{C} \otimes \mathbf{D} \to \mathbf{X}$.

All cells in $\mathbf{C} \otimes \mathbf{D}$ are indeed compositions of these generating cells: see Figure 2. Here each 2-cell written $(1, 1)$, or “shuffle”, may be composed in a canonical way (up to associativity) from the transformation component 2-cells $(f, d), (c', g) \to (c, g), (f, d')$ or their inverses, by constructing the induced permutation out of transpositions. We accordingly extend the map $\mathbf{C} \otimes \mathbf{D} \to \mathbf{X}$ to arbitrary cells, sending each 2-cell written as a composite of the generating 2-cells to the corresponding composite in $\mathbf{X}$.

To show functoriality, consider 2-cells in the image of this extended map $\mathbf{C} \otimes \mathbf{D} \to \mathbf{X}$, i.e. those built as in Figure 2. Vertical composites reduce to the desired form by transformation component 2-cells cancelling with their inverses; horizontal composites are put into the desired form using the naturality and modification laws.

It is then easy to see that the left adjoint acts as $-\otimes \mathbf{D}$ on morphisms as well.

Alternatively, we could skip this argument by appealing to existing knowledge about the Gray tensor product of 2-categories, of which the Gray tensor product of implicit 2-categories may be viewed as a special case; the Gray tensor product of strict 2-categories has a presentation like the above since its internal homs are given by 2-functors, pseudonatural transformations, and modifications of strict 2-categories. □

Remark A.11. Replacing the transformations in Proposition A.10 with (co)lax transformations, we obtain the (co)lax Gray tensor product [Gra74] as the presented structure. (The lax Gray tensor product is then the reverse of the colax Gray tensor product.) However, it is perhaps less obvious that this definition gives a (non-symmetric) monoidal product.

66

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

*Remark A.12.* In contrast, **I-2-Cat** is not cartesian closed. For example, let **C**, **D**₁, **D**₂ and **I** be respectively free on

![img-114.jpeg](img-114.jpeg)

Now the pushout of the unique functors **C** → **D**₁ and **C** → **D**₂ is not preserved by - × **I**. (Cartesian products in **I-2-Cat** are calculated using the essentially algebraic definition of implicit 2-categories in Section 5; note this does not agree with the cartesian product in **2-Cat**.) Indeed, this pushout has nontrivial composite 2-cells α with nullary source and target, so its product with **I** likewise has nontrivial 2-cells (α, 1). On the other hand **D**₁ and **D**₂ have no nontrivial 2-cells with nullary source and target, so the products with **I** are simply **I**, as is the pushout of these.

The next proposition implies in particular that if **C** and **D** are bicategories, then Hom$_{\text{co/lax}}$(**C**,**D**) is a doubly weak double category.

**Proposition A.13.** *If **C** and **D** are implicit 2-categories and **D** is represented, then Hom$_{\text{co/lax}}$(**C**,**D**) (and hence in particular Hom(**C**,**D**)) is represented.*

*Proof.* We define binary composites of colax transformations σ: F → G and ρ: G → H and identity transformations (nullary composites) componentwise on 1-cells, and with 2-cell components:

![img-115.jpeg](img-115.jpeg)

These are easily checked to be horizontal transformations. Moreover, the composition 2-cells in **D** are components of invertible modifications. Lax transformations are similar. □

*Remark A.14.* The Gray tensor product of two representable implicit 2-categories is usually *not* representable: if f: c → c' is an arrow in **C** and g: d → d' is an arrow in **D**, there is no composite 1-cell of the compatible (f, d) and (c', g) in **C** ⊗ **D**.

Next we observe that our notions of transformation, modification, and icon correspond to the usual notions for bicategories.

**Proposition A.15.** *Identifying represented implicit 2-categories and functors with bicategories and pseudofunctors (Proposition 2.9) respects (co)lax transformations, modifications, and icons, as well as their composition.*

DOUBLY WEAK DOUBLE CATEGORIES

67

Proof. Suppose \(\sigma: F \to G\) is a colax transformation of implicit 2-category functors. We define a colax natural transformation of the underlying pseudofunctors as follows.

- The component 1-cell at 0-cell \(A\) is \(\sigma_A\).
- The component 2-cell at 1-cell \( f \colon A \to B \) is \( \sigma_f \) converted to a bigon:

![img-116.jpeg](img-116.jpeg)

![img-117.jpeg](img-117.jpeg)

The axioms of a colax natural transformation then follow from composition isomorphisms cancelling with their inverses and applications of the colax transformation naturality axiom.

Conversely, suppose  \( \sigma \)  is a colax natural transformation of pseudofunctors. We define a colax transformation of the underlying implicit 2-category functors as follows.

- The component 1-cell at 0-cell \(A\) is \(\sigma_A\).
- The component 2-cell is \(\sigma_f\) converted to a (2,2)-ary 2-cell:

![img-118.jpeg](img-118.jpeg)

![img-119.jpeg](img-119.jpeg)

When translated into a statement about corresponding cells in the underlying implicit 2-category, the naturality axiom yields

\[
\begin{array}{c} F f \xrightarrow {} F B \\ F a \xrightarrow {} F g \\ \sigma_ {A} \xrightarrow {} G a \end{array} = \begin{array}{c} F f \xrightarrow {} F B \\ F A \xrightarrow {} G f \\ \sigma_ {A} \xrightarrow {} G a \end{array}
\]

![img-120.jpeg](img-120.jpeg)

68

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

![img-121.jpeg](img-121.jpeg)

![img-122.jpeg](img-122.jpeg)

FIGURE 3. The colax transformation naturality axiom

for all bigons $\alpha$, and the coherence axioms yield

![img-123.jpeg](img-123.jpeg)

![img-124.jpeg](img-124.jpeg)

![img-125.jpeg](img-125.jpeg)

![img-126.jpeg](img-126.jpeg)

for all chosen composition isomorphisms. We obtain the implicit 2-category colax transformation naturality axiom for an arbitrary 2-cell $\alpha$ by bracketing up its 1-cells and moving $\sigma$ across the resulting bigon, as shown in Figure 3. These translation

DOUBLY WEAK DOUBLE CATEGORIES

69

processes are clearly inverse. Moreover, it is easy to see that identities, compositions, and whiskerings are sent to identities, compositions, and whiskerings, as defined in e.g. [JY21].

Our general notion of modification between lax and colax transformations of implicit 2-categories corresponds to a notion for bicategories defined in the same way, and it is easy to see that the specialization to modifications between only lax or only colax transformations (and their composition) coincides with the usual definition, as in e.g. [JY21].

Finally, icons in a represented implicit 2-category are in one-to-one correspondence with colax transformations whose components are identities, by composing the naturality 2-cells with nullary composition isomorphisms:

![img-127.jpeg](img-127.jpeg)

Composition and whiskering for icons are also as in [Lac08].

*Remark A.16.* It is easy to generalize most of the results of this section to double-categorical versions, with a few caveats. We refer the reader to [Böh19] for definitions of horizontal and vertical pseudonatural transformations, modifications, and Gray tensor products of strict double categories; see also [Mor23] for definitions of horizontal and vertical lax and colax transformations.

A maximally general definition of modification between both lax and colax horizontal and vertical transformations of (implicit) double categories can be formulated by placing transformation component 1-cells at all possible corners of the diagram:

![img-128.jpeg](img-128.jpeg)

One then expects to assemble some two-dimensional categorical structure, analogous to $\text{Hom}_{\text{co/lax}}(\mathbf{C}, \mathbf{D})$, in which 0-cells are functors, 1-cells are lax and colax transformations, and 2-cells are these generalized modifications. But here there are four different sorts of 1-cells, apparently requiring an analogue of a (implicit) double category with octagon-shaped rather than square 2-cells.

*Remark A.17.* There is a relationship between double categories and (co)lax transformations of 2-categories. Let $H\mathbf{C}$ denote the vertically trivial (implicit) double category with horizontal (implicit) 2-category $\mathbf{C}$, let $V\mathbf{D}$ denote the horizontally trivial (implicit) double category with vertical (implicit) 2-category $\mathbf{D}$, and let $Q\mathbf{X}$ denote the (implicit) double category of “quintets” of (implicit) 2-category $\mathbf{X}$.

By comparing presentations, we can see that a (implicit) 2-category functor from the *lax* Gray tensor product (Remark A.11) of $\mathbf{C}$ and $\mathbf{D}$ into $\mathbf{X}$ is the same as a (implicit) double category functor $H\mathbf{C} \otimes V\mathbf{D} \rightarrow Q\mathbf{X}$. (Here the double-categorical Gray tensor product $H\mathbf{C} \otimes V\mathbf{D}$ simply agrees with the cartesian product of strict double categories, due to lack of nontrivial 1-cells of each type in some factor. This

70

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

is (the transpose of) the “external product” of 2-categories from [FPP07, Definition 2.6].) In other words, the lax Gray tensor product of (implicit) 2-categories is given by $F(H(-) \otimes V(-))$, where $F$ is the left adjoint to $Q$.

In particular, as can also be seen directly, lax and colax transformations valued in a (implicit) 2-category can be described as horizontal and vertical transformations valued in its associated (implicit) double category.

# REFERENCES

[Bar06] Toby Bartels. Higher gauge theory I: 2-Bundles. PhD thesis, University of California, Riverside, 2006. arXiv:math/0410328. 2
[Bat98] M.A. Batanin. Computads for finitary monads on globular sets. In Higher category theory (Evanston, IL, 1997), volume 230 of Contemp. Math., pages 37–57, USA, 1998. American Mathematical Society. 5
[Bat02] M.A. Batanin. Computads and slices of operads. arXiv:math/0209035, 2002. 5
[BG13] John Bourke and Richard Garner. On semiflexible, flexible and pie algebras. Journal of Pure and Applied Algebra, 217(2):293–321, 2013. 12
[BG16] John Bourke and Richard Garner. Algebraic weak factorisation systems II: categories of weak maps. Journal of Pure and Applied Algebra, 220(1):148–174, 2016. 12, 17
[BHKP02] Ronald Brown, Keith A. Hardie, Klaus Heisner Kamps, and Timothy Porter. A homotopy double groupoid of a Hausdorff space. Theory and Applications of Categories, 10(2):71–93, 2002. 2, 14
[Böh19] Gabriella Böhm. The Gray monoidal product of double categories. Applied Categorical Structures, 28:477 – 515, 2019. 69
[Bou92] Dominique Bourn. Low dimensional geometry of the notion of choice. In Category Theory 1991: Proceedings of an International Summer Category Theory Meeting, Held June 23–30, 1991, pages 55–73. American Mathematical Society, USA, 1992. 19
[Bur93] Albert Burroni. Higher-dimensional word problems with applications to equational logic. Theoretical Computer Science, 115(1):43–62, 1993. 5
[BW05] Michael Barr and Charles Wells. Toposes, triples and theories. Repr. Theory Appl. Categ., pages x+288 pp. (electronic), 2005. Corrected reprint of the 1985 original. 42
[CJ95] Aurelio Carboni and Peter T. Johnstone. Connected limits, familial representability and Artin glueing. Math. Structures Comput. Sci., 5(4):441–459, 1995. Fifth Biennial Meeting on Category Theory and Computer Science (Amsterdam, 1993). 18
[CS10] G.S.H. Cruttwell and Michael Shulman. A unified framework for generalized multicategories. Theory and Applications of Categories, 24(21):580–655, 2010. 6
[Daw95] Robert Dawson. A forbidden-suborder characterization of binarily-composable diagrams in double categories. Theory Appl. Categ., 1(7):146–155, 1995. 7
[DP93] Robert Dawson and Robert Paré. General associativity and general composition for double categories. Cahiers Topologie Géom. Différentielle Catég., 34(1):57–79, 1993. 7
[Fer06] Nelson Martins Ferreira. Pseudo-categories. Journal of Homotopy and Related Structures, 1(1):47 – 78, 2006. arXiv:math/0604549. 2
[FPP07] Thomas M. Fiore, Simona Paoli, and Dorette Pronk. Model structures on the category of small double categories. Algebraic & Geometric Topology, 8:1855–1959, 2007. 70
[Gar10a] Richard Garner. Email to the categories list “re: Composing modifications”. https://github.com/punkdit/categories/blob/master/gmane/science/mathematics/categories/5612, March 2010. 4, 44
[Gar10b] Richard Garner. Homomorphisms of higher categories. Advances in Mathematics, 224(6):2269–2311, 2010. 12, 17
[GP99] Marco Grandis and Robert Pare. Limits in double categories. Cahiers Topologie Géom. Différentielle Catég., XL(3):162–220, 1999. 2, 14, 17

DOUBLY WEAK DOUBLE CATEGORIES

71

[GP04] Marco Grandis and Robert Paré. Adjoints for double categories. *Cah. Topol. Géom. Différ. Catég.*, 45(3):193–240, 2004. 3[Gra74] John Gray. *Formal category theory: adjointness for 2-categories*, volume 391 of *Lecture Notes in Mathematics*. Springer, Berlin, 1974. 60, 65[Gur13] Nick Gurski. *Coherence in Three-Dimensional Category Theory*. Cambridge Tracts in Mathematics. Cambridge University Press, Cambridge, 2013. 9, 61[Had19] Amar Hadzihasanovic. Weak units, universal cells, and coherence via universality for bicategories. *Theory and Applications of Categories*, 34(29):883–960, 2019. 12[Had21] Amar Hadzihasanovic. The smash product of monoidal theories. In *Proceedings of the 36th Annual ACM/IEEE Symposium on Logic in Computer Science*, LICS '21, New York, NY, USA, 2021. Association for Computing Machinery. arXiv:2101.10361. 12[Her00] Claudio Hermida. Representable multicategories. *Advances in Mathematics*, 151(2):164–225, 2000. 6[HMZ08] Victor Harnik, Michael Makkai, and Marek Zawadowski. Computads and multitopic sets. arXiv:0811.3215, 2008. 5[JY21] Niles Johnson and Donald Yau. *2-Dimensional Categories*. Oxford University Press, Oxford, 2021. 69[Kel80] G. M. Kelly. A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on. *Bull. Austral. Math. Soc.*, 22(1):1–83, 1980. 23[Kel82a] G. M. Kelly. *Basic concepts of enriched category theory*, volume 64 of *London Mathematical Society Lecture Note Series*. Cambridge University Press, Cambridge, 1982. Also available online in Reprints in Theory and Applications of Categories, No. 10 (2005) pp. 1–136. 31[Kel82b] G. M. Kelly. Structures defined by finite limits in the enriched context. I. *Cahiers Topologie Géom. Différentielle Catégoriques*, 23(1):3–42, 1982. Third Colloquium on Categories, Part VI (Amiens, 1980). 23, 31[KG13] Joachim Kock and Nicola Gambino. Polynomial functors and polynomial monads. *Math. Proc. Cambridge Phil. Soc.*, 154:153–192, 2013. arXiv:0906.4931. 2[KL97] G. M. Kelly and Stephen Lack. On property-like structures. *Theory Appl. Categ.*, 3(9):213–250, 1997. 31, 33[Kou20] Seerp Roald Koudenburg. Augmented virtual double categories. *Theory and Applications of Categories*, 35(10):261–325, 2020. 7[KP93] G. M. Kelly and A. J. Power. Adjunctions whose counits are coequalizers, and presentations of finitary enriched monads. *J. Pure Appl. Algebra*, 89(1-2):163–179, 1993. 42[KS74] G. M. Kelly and Ross Street. Review of the elements of 2-categories. In *Category Seminar (Proc. Sem., Sydney, 1972/1973)*, volume 420 of *Lecture Notes in Math.*, pages 75–103, Berlin, 1974. Springer. 3, 15[Lac99] Stephen Lack. On the monadicity of finitary monads. *J. Pure Appl. Algebra*, 140(1):65–73, 1999. 23[Lac02a] Stephen Lack. Codescent objects and coherence. *J. Pure Appl. Algebra*, 175(1-3):223–241, 2002. Special volume celebrating the 70th birthday of Professor Max Kelly. 33[Lac02b] Stephen Lack. A Quillen model structure for 2-categories. *K-Theory*, 26(2):171–205, 2002. 12[Lac04] Stephen Lack. A Quillen model structure for bicategories. *K-Theory*, 33(3):185–197, 2004. 12[Lac08] Stephen Lack. Icons. *Applied Categorical Structures*, 18:289–307, 2008. 29, 69[Lac09] Stephen Lack. A 2-categories companion. In John C. Baez and J. Peter May, editors, *Towards Higher Categories*, volume 152 of *The IMA Volumes in Mathematics and its Applications*, pages 105–192, Berlin, 2009. Springer. arXiv:math.CT/0702535. 23, 31[LR25] Elena Di Lavoro and Mario Román. Timing via pinwheel double categories. arXiv:2504.12846, 2025. 7[Mor22] Edward Morehouse. 2-categories from a Gray perspective, 2022. arXiv:2203.08783. 60

72

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

[Mor23] Edward Morehouse. Cartesian Gray-monoidal double categories, 2023. arXiv:2302.07810. 69
[Mye16] David Jaz Myers. String diagrams for double categories and equipments, 2016. arXiv:1612.02762. 6
[nLa25] nLab authors. coherence and strictification for monoidal categories. https://ncatlab.org/nlab/show/coherence+and+strictification+for+monoidal+categories, May 2025. Revision 23. 9
[Pow89] A. J. Power. A general coherence result. J. Pure Appl. Algebra, 57(2):165–173, 1989. 33
[Rob12] David M. Roberts. Internal categories, anafunctors and localisations. Theory and Applications of Categories, 26(29):788–829, 2012. arXiv:1101.2363. 2
[RvdWAN25] Nima Rasekh, Niels van der Weide, Benedikt Ahrens, and Paige Randall North. Insights from univalent foundations: A case study using double categories. In Jörg Endrullis and Sylvain Schmitz, editors, 33rd EACSL Annual Conference on Computer Science Logic (CSL 2025), volume 326 of Leibniz International Proceedings in Informatics (LIPIcs), pages 45:1–45:18, Dagstuhl, Germany, 2025. Schloss Dagstuhl – Leibniz-Zentrum für Informatik. 4, 8, 37
[Shu08] Michael Shulman. Framed bicategories and monoidal fibrations. Theory and Applications of Categories, 20(18):650–738 (electronic), 2008. arXiv:0706.1286. 2, 15
[Shu11] Michael Shulman. Comparing composites of left and right derived functors. New York Journal of Mathematics, 17:75–125, 2011. arXiv:0706.2868. 40
[Shu12] Michael Shulman. Not every pseudoalgebra is equivalent to a strict one. Adv. Math., 229(3):2024–2041, 2012. arXiv:1005.1520. 33
[Str76] Ross Street. Limits indexed by category-valued 2-functors. J. Pure Appl. Algebra, 8(2):149–181, 1976. 5, 19
[Tho74] Walter Tholen. Relative Bildzerlegungen und algebraische Kategorien. Inaugural-dissertation, Universität Münster, 1974. 42
[Ver92] Dominic Verity. Enriched categories, internal categories, and change of base. PhD thesis, University of Cambridge, April 1992. Macquarie Mathematics Report No. 93-123. 2, 4, 8, 15, 35, 37, 40
[Web15] Mark Weber. Polynomials in categories with pullbacks. Theory and Applications of Categories, 30(16):533–598, 2015. 2
[Woo82] Richard J. Wood. Abstract proarrows I. Cahiers de Topologie et Géométrie Différentielle Catégoriques, 23(3):279–290, 1982. 2, 15
[Woo85] Richard J. Wood. Proarrows II. Cahiers de Topologie et Géométrie Différentielle Catégoriques, 26(2):135–168, 1985. 15