arXiv:2106.02706v2 [math.CT] 15 Jun 2021

# Higher Theories and Monads

Simon Henry and Nicholas J. Meadows

June 17, 2021

## Abstract

We extend Bourke and Garner's idempotent adjunction between monads and pretheories to the framework of $\infty$-categories and we use this to prove many classical results about monads in the $\infty$-categorical framework. Amongst other things, we show that the category of algebras for an accessible monads on a locally presentable $\infty$-category $\mathcal{E}$ is again locally presentable, and that a diagram of accessible monads on a locally presentable $\infty$-category admits a colimit. Our results also provide a new and simpler way to construct and describe monads in terms of theories.

## Contents

|  1 | Introduction | 2  |
| --- | --- | --- |
|  2 | Notation and preliminaries | 6  |
|  3 | Monads on $\infty$-Categories | 11  |
|  4 | Partial adjoints and functoriality of the Kleisli category | 26  |
|  5 | The Monad-Theory Correspondence | 32  |
|  6 | General consequences of the Monad-Theories adjunction | 37  |
|  7 | Monads as Kleisli categories | 42  |
|  8 | $E_1$, $E_2$ and $E_\infty$-algebras | 45  |

1

9 Relation to algebraic patterns

51

# 1 Introduction

At the present time, monads on $\infty$-categories are arguably difficult to work with. In [16], Jacob Lurie developed a relatively nice theory of monads on $\infty$-categories as a byproduct of his theory of $\infty$-operads and proved the Barr-Beck monadicity theorem for $\infty$-categories. Essentially, a monad is defined there as a monoid object in the monoidal $\infty$-category of endofunctors. However, this theory remains relatively difficult to use in practice due to the fact that unpacking all the definitions involved in the previous sentence takes a lot work (we review this in Section 3). Also many classical theorems about monads have not yet been proven in this context. For example, it does not seem possible to deduce from [16]$^1$ that the category of algebras for an accessible monad on a cocomplete category has all colimits.

Riehl and Verity proposed an alternative, simpler, definition of monads in [18] for which they also proved the Barr-Beck monadicity criterion. But it is also more model dependent than Lurie's definition as it relies on a strict action of a simplicial monoid on a quasi-category.

This paper is meant to be a toolbox filling some of these gaps and offering a new way to work with (most) monads on $\infty$-categories using only basic $\infty$-category theory instead of Lurie's theory of operads and in an essentially model independent way. This is mostly based on an $\infty$-categorical adaptation of the work on Bourke and Garner in [4] for 1-categorical monads.

Versions of the monad-theory adjunction have appeared in the category theory literature since the 1960s, beginning with Linton's result ([14]). In [4], Bourke and Garner developed a very general monad-theory adjunction, which encompassed many, if not all, of the previously known constructions. Disregarding the enriched category theoretic aspect for simplicity, if $\mathcal{A} \subset \mathcal{E}$ is a small dense full subcategory, an $\mathcal{A}$-pretheory is just a bijective on objects (or essentially surjective) functors $\mathcal{A} \to \mathcal{K}$, with $\mathcal{K}$ a small $\infty$-category. Any monad $M$ on $\mathcal{E}$ has an attached pretheory, called its theory, which is the full subcategory of the Kleisli category of $M$ of objects that are in $\mathcal{A}$.

$^1$Lurie's work contains some results about colimits in category of algebras, but as far as we know, in the case of monads they only applies when the monad preserves colimits and hence colimits of algebras are just colimits in the underlying category.

2

Given an $\mathcal{A}$-pretheory $\mathcal{A} \rightarrow \mathcal{K}$ one defines the category of $\mathcal{K}$-models in $\mathcal{E}$ as objects $X \in \mathcal{E}$ whose restricted Yoneda embeddings in $\Pr(\mathcal{A})$ have an extension to a presheaf on $\mathcal{K}$. That is, it can be expressed as a pullback square:

$$\begin{array}{ccc} \text{Mod}_{\mathcal{E}}(\mathcal{K}) & \longrightarrow & \Pr(\mathcal{K}) \\ \downarrow & \downarrow & \downarrow \\ \mathcal{E} & \longrightarrow & \Pr(\mathcal{A}) \end{array}$$

Now, Bourke and Garner show that under the assumption that $\mathcal{E}$ is locally presentable, the functor $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \mathcal{E}$ is a monadic right adjoint. In particular, it gives a monad $\mu^{\mathcal{K}}$ associated to $\mathcal{K}$ which is characterized by the property that $\mu^{\mathcal{K}}$-algebras are the same as $\mathcal{K}$-models.

Finally, they show that these two constructions (from monads to pretheory and pretheory to monads) are adjoint to each other and form an idempotent adjunction, i.e. induces an equivalence of categories between their essential images. The object in the images are respectively called $\mathcal{A}$-theories, and $\mathcal{A}$-Nervous monads, as they are exactly the monads that satisfy the conclusion of the nerve theorem.

In the present paper, we will generalize these results to the $\infty$-categorical context. While Bourke and Garner generalize all this to an enriched setting (where $\mathcal{E}$, $\mathcal{A}$ and $\mathcal{K}$ are all $V$-enriched categories and $M$ is a $V$-enriched monad for $V$ a nice enough monoidal category), we will restrict to the unenriched setting (as presented above) as we feel the theory of enriched $\infty$-categories is not yet developed enough for this.

In Section 7 we also show that the category of monads on an $\infty$-category $\mathcal{C}$ is equivalent (though the construction of the Kleisli category) with the $\infty$-category of essentially surjective left adjoint functors $\mathcal{C} \rightarrow \mathcal{K}$. This result is not directly related to the main goals of the paper, but it follows from the methods developed in the paper and is fairly similar to the construction of the Monad-theory adjunction. This result produce a much simpler description of the $\infty$-category of monads, which is why we decided to include it.

The main kind of application of our results is to deduce several structural theorems about monads, such as the existence of colimits of monads and colimits in the $\infty$-category of algebras for a monad, by looking instead at colimits of theories and colimits in the category of models of a theory. In

3

order to do this, one needs to show that most monads are actually $\mathcal{A}$-nervous monads for $\mathcal{A}$ a large enough dense subcategory. This is achieved using an $\infty$-categorical generalization of the work of Berger, Mellies and Weber in [2] where they showed that a large class of monads, that they call “monads with arities”, satisfy a nerve theorem (that is are nervous monads). In particular, their results show that any $\lambda$-accessible monad on a locally $\lambda$-presentable category is $\mathcal{A}$-nervous for $\mathcal{A}$ the full subcategory of $\lambda$-presentable objects. We generalize this to accessible monads on $\infty$-categories in Section 6. Using this, we show that:

- For any accessible monad on a locally presentable $\infty$-category the category of $M$-algebras is locally presentable, in particular it has all colimits. Indeed, the category of models of an $\mathcal{A}$-pretheory is easily seen to be locally presentable. See Corollary 6.8.
- Any small diagram $I \rightarrow \mathbf{Mnd}_{\mathcal{E}}$ of accessible monads on a locally presentable $\infty$-category $\mathcal{E}$ has a colimits in the $\infty$-category $\mathbf{Mnd}_{\mathcal{E}}$ of monads on $\mathcal{E}$. Moreover an algebra for the colimit monad $\operatorname{Colim}_i M_i$ is an object of $\mathcal{E}$ equipped with compatible structure of $M_i$ algebra for all $i$. More concretely, we have:

$$\mathcal{E}^{\operatorname{Colim}_{i \in I} M_i} \simeq \lim_{i \in I} \mathcal{E}^{M_i},$$

where $\mathcal{E}^M$ denotes the category of $M$-algebras for a monad $M$ and the limit on the right uses the forgetful functors induced by the morphisms of monads between the $M_i$. This is proven using the fact that colimits of $\mathcal{A}$-pretheories are easy to understand (they are just colimits in the $\infty$-category $\mathbf{Cat}_{\infty}$ of $\infty$-categories) and the monad-theory adjunction preserves colimits. See Corollary 6.9.

A second type of application of our result is to construct examples of monads on $\infty$-categories from (pre)theories. Pretheories are much easier to work with directly, since they are just essentially surjective functors of $\infty$-categories. We treat in detail the case of the monads for $E_1, E_2$ and $E_{\infty}$ algebras in Section 8, and many other more involved examples are in Section 9. In many of these examples $\mathcal{A}$ and $\mathcal{K}$ can be taken to be (nerve of) 1-categories.

4

This can be thought more generally as a procedure to extend a classical monad $M_0$ on a 1-category to an “$\infty$-monad” $M$ on an $\infty$-category by viewing the theory of $M_0$ as an $\infty$-categorical theory, and applying the monad-theory adjunction. To be more precise, assume we have $\mathcal{E}$ a locally presentable $\infty$-category, with $\mathcal{E}_0 \subset \mathcal{E}$ a subcategory that is (equivalent to the nerve of) a locally presentable 1-category. For example, $\mathcal{E}$ could be a category of presheaves of spaces on a 1-category and $\mathcal{E}_0$ is the full subcategory of presheaves that are levelwise discrete (i.e. equivalent to presheaves of sets). If now $M$ is an ordinary monad on the 1-category $\mathcal{E}_0$ which is $\mathcal{A}$-nervous for $\mathcal{A} \subset \mathcal{E}_0$ then, assuming $\mathcal{A}$ is also dense in $\mathcal{E}$, one can consider the monad on $\mathcal{E}$ associated by the monad-theory adjunction to the $\mathcal{A}$-theory of $M$. We will not develop this point of view much further, but many examples we mention in this paper can be thought as special case of this. The $E_1$ monad is obtained from the free monoid monad on Sets (as a subcategories of spaces). All the examples mentioned at the end of Section 9 can also be thought of as being obtained this way. The examples the monads for $E_2$ and $E_\infty$-algebras treated in Section 8 can also be thought in this way, but with $\mathcal{E}_0$ and $\mathcal{A}$ being 2-categories instead of 1-categories.

We conclude this introduction by mentioning some closely related work:

Another approach to the monad-theory correspondence in $\infty$-categorical context has been developed very recently and independently from ours by R. Kositsyn in [13]. Compared to our approach, Kositsyn uses more abstract methods, relying on the theory of $(\infty, 2)$-categories. He also uses the description of monads as lax functors from the terminal category, while we take a more elementary approach following more closely Lurie’s theory of monads from [16]. Also, Kositsyn’s work focuses on generalizing the notion of “monads with arities” from [2] (which we discuss in section Section 6) while we consider the slightly more general notion of “nervous monads” from [4]. While the gain in generality from using nervous monads instead of monads with arities is not essential by itself, it allows one to see the monad-theory equivalence as a special case of a more general monad-pretheory adjunction. The notion of pretheory is much simpler and has better category-theoretic properties than the various notion of theories considered. This makes pretheories much easier to handle when dealing with examples and is key in our construction in Section 6 of colimits of nervous monads and accessible monads on locally presentable categories, using colimits of pretheories.

In [11], R. Haugseng has developed a more general theory of monads in

5

an $(\infty, 2)$-category and proves it is equivalent to both Lurie's and Riehl-Verity's approach to monads (hence clarifying the equivalence between the two). We expect a large part of our preliminary results could be deduced from [11]. However, Haugseng's work relies on the some (as of yet unproven) assumptions about the Gray tensor products of $\infty$-categories, so we have decided to give independent and more elementary proof of these results.

Finally, our work is closely related to Chu and Haugseng's work on algebraic patterns from [5] and the precise relation is discussed in Section 9. Essentially, algebraic patterns correspond to the special case of '(pre)theories' as above that represent parametric right adjoint cartesian monads (or polynomial monads in the terminology of [5]) on presheaf $\infty$-categories. Of course, it is not true that the results in [5] are all special cases of our results: parametric right adjoint cartesian monads have more structure than general monads and this translates into a better behaved theory in this special case.

## 2 Notation and preliminaries

While we will try to give model independent argument whenever possible, we generally work within the framework of Jacob Lurie's books [15] and [16]. An $\infty$-category is by definition a quasicategory, i.e. a simplicial set satisfying the appropriate lifting property. We refer to [15] for the basic theory of $\infty$-categories. We often will write objects (or 0-simplices) in an $\infty$-category by lower case letters, such as $x, y$. We call the 1-simplices of an $\infty$-category *edges* or *1-morphisms*. An edge is said to be an equivalence if and only if it represents an equivalence in the *homotopy category* of an $\infty$-category (see [15, Section 1.2.3] for the definition of the homotopy category).

Given two objects $x, y$ in an $\infty$-category $\mathcal{C}$, we will write $\text{Map}_{\mathcal{C}}(x, y)$ for the space of maps between $x$ and $y$. We will be working in a relatively model-independent manner, so it does not matter which of the (equivalent) models of mapping spaces from [15, Section 1.2.2] we use. An *equivalence of $\infty$-categories* is just an equivalence in Joyal's model structure for $\infty$-categories. That is, it induces an equivalence of homotopy categories, as well as induces weak equivalences of mapping spaces. We will refer to fibrations in Joyal's model structure as *quasi-fibrations*. Quasi-fibrations between quasicategories have a nice characterization as *isofibrations* (see [15, Corollary 2.4.6.5]).

We will write $X^K$ for the internal hom in simplicial sets. If $X$ is an $\infty$-

6

category, then $X^K$ is also an $\infty$-category and we write often write $\text{Fun}(K, X)$, to emphasize that this is the $\infty$-category of functors from $K$ to $X$.

By a *simplicial category*, we mean a simplicially enriched category. Given a simplicial category $\mathcal{C}$, we will write $N(\mathcal{C})$ for its homotopy coherent nerve (see [15, Definition 1.1.5]). It should be noted that in the case we regard an ordinary category as an enriched category with discrete mapping spaces, this recovers the ordinary nerve construction.

Recall that a *natural transformation* of maps of $\infty$-categories $f, g : \mathcal{C} \rightarrow \mathcal{D}$ is just a map $T : \mathcal{C} \times \Delta^1 \rightarrow \mathcal{D}$ so that $T|_{\mathcal{C} \times \{0\}} = f, T|_{\mathcal{C} \times \{1\}} = g$. This is the same as a morphism in the functor $\infty$-category $\text{Fun}(\mathcal{C}, \mathcal{D})$. A natural transformation $T$ is called a *natural isomorphism* if corresponds to an invertible morphism in $\text{Fun}(\mathcal{C}, \mathcal{D})$. We often write $T_x = T|_{\{x\} \times \Delta^1}$ which is an arrow in $f(x) \rightarrow g(x)$ in $\mathcal{D}$, and is called the *component of $T$ at $x$*. We recall that:

**Lemma 2.1.** *Suppose that $T : \mathcal{C} \times \Delta^1 \rightarrow \mathcal{D}$ is a natural transformation. The following are equivalent:*

1. $T$ is a natural isomorphism.
2. For each $x \in \mathcal{C}$, $T_x$ is an equivalence.

*In other words, a natural transformation is a natural isomorphism iff each component is an equivalence.*

*Proof.* This follows from [15, Corollary 5.1.2.3] as an object $y$ is equivalent to an object $x$ in an $\infty$-category $\mathcal{C}$ iff $y$ is a (co)limit of $x : \Delta^0 \rightarrow \mathcal{C}$. $\square$

We denote by $\mathcal{S}$ the $\infty$-category of spaces and by $\text{Pr}(\mathcal{C})$ the $\infty$-category of presheaves of spaces on an $\infty$-category $\mathcal{C}$, that is $\text{Pr}(\mathcal{C}) = \text{Fun}(\mathcal{C}^{op}, \mathcal{S})$. We will write $y_{\mathcal{C}} : \mathcal{C} \rightarrow \text{Pr}(\mathcal{C})$ for the Yoneda embedding.

We refer the reader to [15, Section 5.2.2] for the theory of adjoint functors, as well as related concepts such as counit transformations. In classical category theory, one can verify that functors form an adjoint pair by specifying the unit and counit of the adjunction, and verifying that they satisfy the triangle identities. The $\infty$-categorical counterpart of this statement, which follows, will be used several times throughout the paper:

7

**Lemma 2.2.** *Let $F : \mathcal{C} \rightarrow \mathcal{D}$, $G : \mathcal{D} \rightarrow \mathcal{C}$ be functors of $\infty$-categories. Let $\eta : id \rightarrow GF$ and $\epsilon : FG \rightarrow id$ be natural transformations. If for each object $X \in \mathcal{C}$ and $Y \in \mathcal{D}$ the two composites:*

$$F(X) \stackrel{F(\eta_X)}{\rightarrow} FGF(X) \stackrel{\epsilon_{F(X)}}{\rightarrow} F(X) \quad \text{and} \quad G(Y) \stackrel{\eta_{G(Y)}}{\rightarrow} GFG(Y) \stackrel{G(\epsilon_Y)}{\rightarrow} G(Y)$$

*are equivalences, then $\eta$ is the unit of an adjunction $F \dashv G$.*

By duality it is also the case that $\epsilon$ is the counit of an adjunction, but without additional assumption (for example the fact that the two composite above are equivalent to the identity) these two claims might not be compatible ($\eta$ and $\epsilon$ might not be the unit and counit of the same adjunction, typically, one of the adjunctions can be twisted by an automorphism of $F$ or $G$.)

*Proof.* By the definition of unit of an adjunction [15, Proposition 5.2.2.7], we want to show that for each $x \in \mathcal{C}, y \in \mathcal{D}$ the map

$$U_{x,y} : \text{Map}_{\mathcal{D}}(Fx, y) \rightarrow \text{Map}_{\mathcal{C}}(GFx, Gy) \xrightarrow{(-)\circ\eta_x} \text{Map}_{\mathcal{C}}(x, Gy) \quad (1)$$

is an equivalence. We introduce the dual transformation

$$V_{x,y} : \text{Map}_{\mathcal{C}}(x, Gy) \rightarrow \text{Map}_{\mathcal{D}}(Fx, FGy) \xrightarrow{\epsilon_y \circ(-)} \text{Map}_{\mathcal{D}}(Fx, y)$$

Since the natural transformation $\epsilon$ and $\eta$ induces a natural tranformation on the level of enriched homotopy categories$^2$, we get a commutative square in the homotopy category of spaces:

$$\begin{array}{ccc} \text{Map}_{\mathcal{C}}(x, G(y)) & \xrightarrow[GF(-)]{} & \text{Map}_{\mathcal{C}}(GF(x), GFG(y)) \\ \scriptstyle{id} \downarrow & & \scriptstyle{\eta_x} \downarrow \\ \text{Map}_{\mathcal{C}}(x, G(y)) & \xrightarrow{\eta_{Gy} \circ(-)} & \text{Map}_{\mathcal{C}}(x, GFG(y)) \end{array}$$

In other words $GF(-) \circ \eta_x \simeq \eta_{G(y)} \circ (-)$. We have

$$U_{x,y} \circ V_{x,y} = G(\epsilon_y \circ F(-)) \circ \eta_x = G(\epsilon_y) \circ GF(-) \circ \eta_x \simeq G(\epsilon_y) \circ \eta_{Gy} \circ (-)$$

$^2$Here we see the homotopy category as enriched in the homotopy category of spaces as in [15, Definition 1.1.5.14].

8

so $U_{x,y} \circ V_{x,y}$ is the composition by an equivalence by our assumptions, hence $U_{x,y} \circ V_{x,y}$ is an equivalence. Similarly, we have that $V_{x,y} \circ U_{x,y} \simeq \epsilon_y \circ F(G(-) \circ \eta_x) = \epsilon_y \circ FG(-) \circ F(\eta_x) \simeq (-) \circ \epsilon_{Gx} \circ F(\eta_x)$, so $V_{x,y} \circ U_{x,y}$ is also an equivalence. It hence follows that $U_{x,y}$ and $V_{x,y}$ are both equivalences. $\square$

In Section 5, we show that the monad-theory correspondence is an *idempotent adjunction*. We will exploit the idempotence of the adjunction throughout the paper, especially in Section 8. Thus, we will review the definition and basic properties of idempotent adjunctions below:

**Lemma 2.3.** *Suppose that $L \dashv R$ is an adjunction with counit $\epsilon$ and unit $\eta$. Then one of the following natural transformations $(\epsilon)L, R(\epsilon), \eta(R), L(\eta)$ is an equivalence if and only if each of them are equivalences. If any (and hence all) of the above natural transformations are equivalences, we say that the adjunction is idempotent.*

*Proof.* The classical, or 1-categorical, analogue of this fact is [17, Proposition 2.8]. The proof given there carries forward to the $\infty$-categorical case, either because it is essentially an excercise in manipulating the counit-unit identities, or be applying the 1-categorical result to the homotopy category and the adjunction between the derived functors of $L$ and $R$. $\square$

*Remark 2.4.* A useful fact about idempotent adjunctions is that the restrict to an equivalence $im(R) \simeq im(L)$ between the essential images of $R$ and $L$, essentially by definition. It is also important to note that if $X \in im(L), Y \in im(R)$, then also by definition $LRX \simeq X, Y \simeq RLY$.

*Remark 2.5.* Given an adjunction $L \dashv R$, written $L : \mathcal{C} \leftrightarrows \mathcal{D} : R$, post-composition with $L$ and $R$ induces an adjunction:

$$(L \circ -) : \text{Fun}(\mathcal{T}, \mathcal{C}) \leftrightarrows \text{Fun}(\mathcal{T}, \mathcal{C}) : (R \circ -)$$

for any $\infty$-category $\mathcal{T}$. A natural transformation $LX \rightarrow Y$ corresponds to a natural transformation $X \rightarrow RY$ simply by functoriality of the correspondence between arrows $L(a) \rightarrow b$ and arrows $a \rightarrow R(b)$.

But on the other hand, pre-composition with $L$ and $R$ induces an adjunction in the other direction:

$$(- \circ R) : \text{Fun}(\mathcal{D}, \mathcal{T}) \leftrightarrows \text{Fun}(\mathcal{T}, \mathcal{C}) : (- \circ L)$$

9

That is there is a correspondence between natural transformation $X \circ R \rightarrow Y$ and $X \rightarrow Y \circ L$. Indeed, given a natural transformation $v: X \rightarrow Y \circ L$, one obtain a natural transformation

$$XR \xrightarrow{vR} YLR \xrightarrow{Y(\eta)} Y$$

where $\eta: LR \rightarrow Id$ is the counit of adjunction. The inverse construction is obtained from the counit and the unit-counit relation shows that these are inverses of each other.

We refer to section 2.4 of [15] for the general theory of Cartesian and coCartesian fibrations. The following construction allows us to describe how the coCartesian fibration classified by $F: \mathcal{C} \rightarrow \mathbf{Cat}_{\infty}$ relates to the coCartesian fibration classified by $\text{Fun}(K, F(-)): \mathcal{C} \rightarrow \mathbf{Cat}_{\infty}$ for a fixed $\infty$-category $K$:

**Definition 2.6.** Let $\mathcal{E} \rightarrow \mathcal{B}$ be a map of simplicial sets and $K$ any simplicial set. We denote by $F_K(\mathcal{E})$ the simplicial set obtained as the pullback:

$$\begin{array}{ccc} F_K(\mathcal{E}) & \longrightarrow & \mathcal{E}^K \\ \downarrow & \downarrow & \downarrow \\ \mathcal{B} & \longrightarrow & \mathcal{B}^K, \end{array}$$

where the bottom map is the diagonal map.

**Proposition 2.7.** 1. If $\mathcal{E} \rightarrow \mathcal{B}$ is a Cartesian or coCartesian fibration, then $F_K\mathcal{E} \rightarrow \mathcal{B}$ is as well.

2. The construction $\mathcal{E} \mapsto F_K\mathcal{E}$ is right adjoint to $\mathcal{E} \mapsto \mathcal{E} \times K$ in the $\infty$-categories of Cartesian fibrations over $\mathcal{B}$ and of coCartesian fibrations over $\mathcal{B}$.
3. If $\mathcal{E} \rightarrow \mathcal{B}$ is a coCartesian fibration, then the functor $\mathcal{B} \rightarrow \mathbf{Cat}_{\infty}$ classifying $F_K(\mathcal{E})$ is equivalent to the composite of the functor $\mathcal{B} \rightarrow \mathbf{Cat}_{\infty}$ classifying $\mathcal{E} \rightarrow \mathcal{B}$ with $\text{Fun}(\mathcal{K}, -): \mathbf{Cat}_{\infty} \rightarrow \mathbf{Cat}_{\infty}$.

*Proof.* The first point for Cartesian fibrations follows immediately from Proposition 3.1.2.1 of [15], which claims that $\mathcal{E}^K \rightarrow \mathcal{B}^K$ is a cartesian fibration when $\mathcal{E} \rightarrow \mathcal{B}$ is, and the fact that a pullback of a cartesian fibration is a cartesian

10

fibration. The case of coCartesian fibrations immediately follows by duality. In order to prove the second point we will need to recall some element of the proof of Proposition 3.1.2.1 in [15].

The idea is that it is immediate to check that the construction $\mathcal{E} \mapsto F_K \mathcal{E}$ and $\mathcal{E} \mapsto K \times \mathcal{E}$ are a simplicially enriched pair of adjoint functors on the category (in the notation of [15]) $\mathrm{Set}_{\Delta}^{+}/\mathcal{B}^{\sharp}$ of marked simplicial sets over $\mathcal{B}^{\sharp}$ (which is $\mathcal{B}$ with all edges marked). The core result of section 3.1.2 of [15] is Proposition 3.1.2.3 which implies that product by $K$ preserves the “marked anodyne maps”. This implies that the right adjoint $F_k(-)$ preserves the objects with the right lifting property against these maps, i.e. exactly the Cartesian fibrations. However as taking the product with $K$ preserves the cofibrations, this pair of adjoint functors actually is a Quillen adjunction on the “cartesian model structure” (constructed in Proposition 3.1.3.7 of [15]) on $\mathrm{Set}_{\Delta}^{+}/\mathcal{B}^{\sharp}$. This implies that these functors induce an adjunction on the corresponding $\infty$-categories, which proves the second point for cartesian fibrations. The result for coCartesian fibrations follows by duality.

For the third point, while it is a bit difficult to keep track of what classifies the functor $F_K(\mathcal{E})$, it is relatively easy to observe that $K \times \mathcal{E} \to \mathcal{B}$ is classified by $K \times F(-)$ where $F : \mathcal{B} \to \mathbf{Cat}_{\infty}$ is the functor classifying $\mathcal{E} \to \mathcal{B}$. Indeed, by functoriality of the straightening/unstraightening construction in $\mathcal{B}$ one deduces that $\mathcal{B} \times K \to \mathcal{B}$ classifies the constant functor with value $K$, and one then uses that the straightening/unstraightening equivalence preserves products.

It follows that the right adjoint of these two constructions are also equivalent under the straightening/unstraightening equivalence. In the category of functors $\mathcal{B} \to \mathbf{Cat}_{\infty}$, the right adjoint to $F \mapsto K \times F$ is indeed $F \mapsto \mathrm{Fun}(K, F(-))$ and the second point above show that $F_k(-)$ is the right adjoint of $\mathcal{E} \to K \times \mathcal{E}$. This concludes the proof.

□

## 3 Monads on $\infty$-Categories

In the present paper, we follow Jacob Lurie’s definition of monads on $\infty$-categories, from Chapter 4.7 of [16]. In this section, we briefly recall some important points of Lurie’s theory of monads and we complete the proof of Theorem 3.22 which claims that the category $\mathbf{Mnd}_{\mathcal{C}}$ of monads in $\mathcal{C}$ is equivalent to the opposite of the full subcategory $\mathbf{RMd}_{\mathcal{C}}$ of $(\mathbf{Cat}_{\infty})/\mathcal{C}$ of

11

monadic right adjoint functors to $\mathcal{C}$. This result is mentioned without proof by Lurie in Remark 4.7.3.8 of [16].

Lurie's definition works as follows: given an $\infty$-category $\mathcal{C}$, he constructs a monoidal $\infty$-category of endofunctor $\text{End}(\mathcal{C})$ that acts on $\mathcal{C}$. The category $\mathbf{Mnd}_{\mathcal{C}}$ of monads on $\mathcal{C}$ is then defined as the category of monoids in $\text{End}(\mathcal{C})$. As $\text{End}(\mathcal{C})$ acts on $\mathcal{C}$, given a monad $T$ on $\mathcal{C}$ we can look at the category $\mathcal{C}^T$ of objects of $\mathcal{C}$ endowed with an action of $T$ (the left $T$-modules) and this is what we call the $\infty$-category of $T$-algebras, or the Eilenberg-Moore category of $T$.

In [16] Lurie make sense of these notions of monoids and algebras (or rather modules in the general terminology) using his formalism of $\infty$-operads. In fact, [16] developed two formalisms that allow one to do this: one can use the formalism of (symmetric) $\infty$-operads, or the formalism of planar (non-symmetric) $\infty$-operads. They are shown to be equivalent in [16, Proposition 4.1.2.11] and [16, Theorem 2.3.3.23], but lead to different combinatorics for the concrete description of monads. Here we will recall all of the relevant definitions in the formalism of planar operads, in a way as unpacked as possible.

**Definition 3.1.** A *monoid object* $M$ in an $\infty$-category $\mathcal{C}$ with finite products is a functor $M : N(\Delta^{op}) \to \mathcal{C}$ which satisfies the Segal conditions:

- $M([0])$ is a terminal object of $\mathcal{C}$.
- For each $n$, the map $M([n]) \to M([1])^n$, induced by the maps $[1] \simeq \{i, i+1\} \subset [n]$ for $i = 0 \dots, n-1$ is an equivalence.

The category $\mathbf{Mon}(\mathcal{C})$ of monoids in $\mathcal{C}$ is the full subcategory of $\mathcal{C}^{\Delta^{op}}$ on monoids. $M([1])$ is called the underlying object of $M$.

For example, if $M = M([1])$ is the underlying object of a monoid, the multiplication map $M^2 \to M$ is obtained as the map $M^2 \simeq M([2]) \to M([1])$ induced by $[1] \simeq \{0, 2\} \subset \{0, 1, 2\}$. The associativity and higher coherence conditions are obtained by looking at the maps between the $M([k])$ for $k \geqslant 3$.

Note that this is the definition of monoid *with respect to the cartesian product*. We will later give a definition of monoids with respect to a monoidal structure, which is different (they are equivalent when the monoidal structure is cartesian by (3) of [16, Corollary 2.4.1.8] and [16, Proposition 2.4.2.5]). The same remarks apply to the next definition as well:

12

**Definition 3.2.** A module object in an $\infty$-category $\mathcal{C}$ with finite products, is a functor $X : N(\Delta^{op}) \times \Delta^1 \to \mathcal{C}$ such that:

- The restriction of $X$ to $N(\Delta^{op}) \times \{1\} \simeq N(\Delta^{op})$ is a monoid object in the sense of Definition 3.1.
- The maps $X([n], 0) \to X([n], 1) \times X([0], 0)$ induced by the maps $[0] \simeq \{n\} \subset [n]$ and obvious map $(0, [n]) \to (1, [n])$ are equivalences.

The $\infty$-category $\mathbf{LMod}(\mathcal{C})$ of modules is the full subcategory of functors $\mathcal{C}^{N(\Delta^{op}) \times \Delta^1}$ on module objects.

The category $\mathbf{LMod}(\mathcal{C})$ should be thought of as a category of pairs of a monoid $M$ with an $M$-module $X$. The module $M$ is the restriction of $X$ to $N(\Delta^{op}) \times \{1\}$ which is a monoid by the first assumption. The “underlying” object $X$ is obtained as $X = X(0, [0])$, and the action map $M \times X \to X$ is induced by $X([1], 0) \simeq X([1], 1) \times X([0], 0) = M \times X \to X([0], 0)$ induced by the unique edge $[0] \to [1]$ in $N(\Delta)$.

This intuition that $\mathbf{LMod}(\mathcal{C})$ is a “category of pairs” is made formal by the following:

**Proposition 3.3.** *The forgetful functor from $\mathbf{LMod}(\mathcal{C}) \to \mathbf{Mon}(\mathcal{C})$ that restricts to $N(\Delta^{op}) \times \{1\}$ is a Cartesian fibration. Its fiber over a monoid $T \in \mathbf{Mon}(\mathcal{C})$ is called the category of $T$-modules and is denoted $\mathbf{LMod}^T(\mathcal{C})$.*

Henceforth, when we say that $X$ is an $M$-module we mean that $X$ is an object of $\mathbf{LMod}(\mathcal{C})$ over $M$. We call an action of $M$ on an object $X \in \mathcal{C}$ the data of a $M$-module whose underlying object is $X$.

This allows to define a *monoidal $\infty$-category* $\mathcal{M}$ to be a monoid in $\mathbf{Cat}_{\infty}$. A *monoidal action* of such a monoidal $\infty$-category $\mathcal{M}$ on an $\infty$-category $\mathcal{C}$ is an action in $\mathbf{Cat}_{\infty}$ in the sense above.

We will generally work with monoidal $\infty$-categories and monoidal action from “the other side” of the straightening/unstraightening equivalences. Instead of defining a monoidal $\infty$-category as a functor $N(\Delta^{op}) \to \mathbf{Cat}_{\infty}$, we define a monoidal $\infty$-category $\mathcal{M}$ to be a coCartesian fibration $\mathcal{M}^* \to N(\Delta^{op})$ which is classified by a functor satisfying the Segal conditions as in Definition 3.1. Similarly, an action of $\mathcal{M}$ on an $\infty$-category $\mathcal{C}$ is defined as a coCartesian fibration $\mathcal{C}^* \to N(\Delta^{op}) \times \Delta^1$ classified by a functor to $\mathbf{Cat}_{\infty}$ satisfying the conditions of Definition 3.2.

13

The symbol $\otimes$ is only here to distinguish the underlying $\infty$-categories $\mathcal{M}$ and $\mathcal{X}$, which are the fiber over respectively [1] and ([0], 0), from the domain of these coCartesian fibrations.

*Remark 3.4.* If an $\infty$-category $\mathcal{M}$ has a monoid structure as a simplicial set, then it has a monoidal $\infty$-category. We call this a strict monoidal $\infty$-category. Indeed, one easily sees that such a “strict monoidal” $\infty$-category corresponds exactly to the functor $N(\Delta^{op}) \rightarrow \mathbf{Cat}_{\infty}$, which comes from the 1-categorical functor $\Delta^{op} \rightarrow \operatorname{Set}_{\Delta}$ that takes values in $\infty$-categories and satisfies the Segal condition up to isomorphism instead of just up to equivalence. Morphisms of simplicial monoids also induces monoidal functors.

Of course, the same can be said of a monoidal action. If $\mathcal{M}$ and $\mathcal{X}$ are two $\infty$-categories and $\mathcal{M}$ is a simplicial monoid acting on the simplicial set $\mathcal{X}$, then this produces a monoidal structure on $\mathcal{M}$ and a monoidal action of $\mathcal{M}$ on $\mathcal{X}$ in the sense above. The monoidal action can be encoded as functor $\Delta^{op} \times \Delta^1 \rightarrow \operatorname{Set}_{\Delta}$ that takes values in quasi-categories and satisfies the Segal conditions up to isomorphism.

Next we move to the definition of monoids and monoidal actions in monoidal $\infty$-categories. We first need to introduce the following terminology:

**Definition 3.5.** • An edge in $N(\Delta^{op})$ is said to be *inert* if the corresponding arrow in $\Delta$ is an interval inclusion, i.e. of the form $[k] \simeq \{i, i+1, \dots, i+k\} \subset [n]$ for $i+k \leqslant n$.
- • An inert edge in $N(\Delta^{op}) \times \Delta^1$ is a pair $(v, f)$ of an *inert* edge $v$ (in the above sense) in $N(\Delta^{op})$ and an arbitrary edge $f$ in $\Delta^1$, such that if $f$ is the identity edge of 0 then the map $v : [n] \rightarrow [m]$ satisfies $v(n) = m$.
- • If $X^{\otimes} \rightarrow N(\Delta^{op})$ is a monoidal $\infty$-category or a monoidal action, an arrow in $X^{\otimes}$ is said to be *inert* if it is coCartesian and its image in $N(\Delta^{op})$ is inert.
- • If $X^{\otimes} \rightarrow N(\Delta^{op}) \times \Delta^1$ is a monoidal action, an arrow in $X^{\otimes}$ is said to be *inert* if it is coCartesian and its image in $N(\Delta^{op}) \times \Delta^1$ is inert.

Intuitively, the inert edges are the arrows in $N(\Delta^{op})$ or $N(\Delta^{op}) \times \Delta^1$ such that, given a monoid object $N(\Delta^{op}) \rightarrow \mathcal{C}$ or a module object $N(\Delta^{op}) \times \Delta^1 \rightarrow \mathcal{C}$ corresponds to product projection. A general arrow encodes some operations from the monoid or module structure.

We can now give the definition of monoids, monoid actions and module objects in a general monoidal $\infty$-category.

14

**Definition 3.6.** • If $\mathcal{C}^* \to N(\Delta^{op})$ is a monoidal $\infty$-category, a *monoid object* in $\mathcal{C}$ is a section of this map that send inert edges to inert edges. The $\infty$-category $\mathbf{Mon}(\mathcal{C})$ is defined as the full subcategory of the $\infty$-category of sections on monoid objects.

• If $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ is a monoidal action, a *module object* in $\mathcal{X}$ is a section of this map that sends inert edges to inert edges. The $\infty$-category $\mathbf{LMod}(\mathcal{X})$ is defined as the full subcategory of the $\infty$-category of sections on module objects.

Obviously, the notion of monoid in $\mathcal{C}$ depends on the whole monoidal structure $\mathcal{C}^* \to N(\Delta^{op})$ and not just on the underlying $\infty$-category $\mathcal{C}$, and the notation $\mathbf{Mon}(\mathcal{C})$ is an abuse. The same applies to module objects.

Here again, the monoidal action $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ is a pair of a monoidal $\infty$-category $\mathcal{M}$ that acts on an $\infty$-category $\mathcal{X}$. The category $\mathbf{LMod}(\mathcal{X})$ is a category of pairs of a monoid object $M$ in $\mathcal{M}$, together with an object $X$ of $\mathcal{X}$ and an action of $M$ on $X$.

We sometime write $\mathbf{LMod}(\mathcal{X}, \mathcal{M})$ when we want to emphasize the monoidal part of the action $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$.

Similar to the case of $\infty$-categories with finite limits, if $\mathcal{X}$ is an $\infty$-category with an action of a monoidal $\infty$-category $\mathcal{M}$, then there is a forgetful functor $\mathbf{LMod}(\mathcal{X}) \to \mathbf{Mon}(\mathcal{M})$ and Lurie showed that this is a cartesian fibration. If $A$ is a monoid object in $\mathcal{M}$ we denote by $\mathbf{LMod}^A(\mathcal{X})$ the fibre over $A$ of this fibration. We call it the category of $A$-modules in $\mathcal{X}$. The full subcategory whose objects are actions of $A$ on $B \in \mathcal{X}$ is denoted by $\mathbf{LMod}_B^A(\mathcal{X})$.

Before moving further, we quickly look at how these notions interact with the functions $F_K$ of Definition 2.6. Let $\mathcal{M}^* \to N(\Delta^{op})$ be a monoidal $\infty$-category and $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ a monoidal action of $\mathcal{M}$ on an $\infty$-category $\mathcal{X}$. For $K$ an $\infty$-category, we can apply the construction $F_K$ of Definition 2.6 to these functors to get new functors $F_K\mathcal{M}^* \to N(\Delta^{op})$ and $F_K\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$. We have:

**Lemma 3.7.** $F_K\mathcal{M}^* \to N(\Delta^{op})$ and $F_K\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ are a monoidal $\infty$-category and a monoidal action. They correspond, respectively, to a monoidal structure on $\operatorname{Fun}(K, \mathcal{M})$ and a monoidal action of $\operatorname{Fun}(K, \mathcal{M})$ on $\operatorname{Fun}(K, \mathcal{X})$.

*Proof.* By Proposition 2.7 these are coCartesian fibration classified by the postcomposition of the functor classifying $\mathcal{M}^*$ and $\mathcal{X}^*$ with $\operatorname{Fun}(K, -)$. As

15

$\text{Fun}(K, -)$ preserves products, it is immediate that the corresponding functors to $\mathbf{Cat}_{\infty}$ satisfies the “Segal conditions” of Definition 3.1 and Definition 3.2. This immediately proves the result. $\square$

**Lemma 3.8.** *We have natural equivalences (in fact isomorphisms) of $\infty$-categories:*

$$\begin{array}{ccc} \mathbf{LMod}(F_K \mathcal{X}^*) & \simeq & \text{Fun}(K, \mathbf{LMod}(\mathcal{X})) \\ \downarrow & & \downarrow \\ \mathbf{Mon}(F_K \mathcal{M}^*) & \simeq & \text{Fun}(K, \mathbf{Mon}(\mathcal{M})) \end{array}$$

*compatible to the forgetful functor as represented in the diagram above.*

*Proof.* By construction of $F_K$, or rather by the second point of Proposition 2.7, the simplicial set of sections of $F_K \mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ is equivalent to the simplicial set of maps $K \times N(\Delta^{op}) \times \Delta^1 \to \mathcal{X}^*$. This, in turn, is isomorphic to the simplicial set of maps from $K$ to the simplicial set of sections of $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$. The same can be said for $\mathcal{M}^* \to N(\Delta^{op})$, and these identification are compatible with the “forgetful functors”, i.e. the restriction along $N(\Delta^{op}) \times \{1\} \to N(\Delta^{op}) \times \Delta^1$.

The $\infty$-categories mentioned in the lemma are full subcategories of these simplicial sets. To conclude the proof we just need to show that they are preserved by these isomorphisms. The proofs for monoids and module objects are exactly the same. On the side of $\mathbf{LMod}(F_K \mathcal{X}^*)$ we are looking at the full subcategory of sections that send any inert arrow to a coCartesian lift. Though the series of isomorphisms mentioned at the beginning, these corresponds to the dotted section in

$$\begin{array}{ccc} & & \text{Fun}(K, \mathcal{X}^*) \\ & \downarrow & \\ N(\Delta^{op}) \times \Delta^1 & \longrightarrow & \text{Fun}(K, N(\Delta^{op}) \times \Delta^1) \end{array}$$

that sends inert edges to coCartesian edges. The coCartesian edges with respect to the coCartesian fibration $\text{Fun}(K, \mathcal{X}^*) \to \text{Fun}(K, N(\Delta^{op}) \times \Delta^1)$ are exactly the natural transformations that are coCartesian when evaluated at each object $k \in K$ (see [15, Proposition 3.1.2.1]). Thus, it follows that through the series of isomorphisms above, a section of $F_K \mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$

16

corresponds to a module object if and only the corresponding functor from $K$ to the simplicial set of section of $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ sends each object of $k \in K$ to a module object. This concludes the proof.

**Lemma 3.9.** *If $\mathcal{M}$ is a monoidal $\infty$-category and $K$ any $\infty$-category, then the diagonal functor $\mathcal{M} \to \operatorname{Fun}(K, \mathcal{M})$ admits a structure of monoidal functor.*

*Proof.* This follows immediately from the fact that $\mathcal{M} \to \operatorname{Fun}(K, \mathcal{M})$ is natural in $\mathcal{M}$ and that the monoidal structure on $\operatorname{Fun}(K, \mathcal{M})$ is obtained by postcomposing the functor $N(\Delta^{op}) \to \mathbf{Cat}_{\infty}$ classifying the monoidal structure of $\mathcal{M}$ with $\operatorname{Fun}(K, -)$. $\square$

*Remark 3.10.* We fix $\mathcal{M}$ a monoidal $\infty$-category with an action on an $\infty$-category $\mathcal{X}$, and $K$ any $\infty$-category. For $M$ any monoid object in $\mathcal{M}$, one can use the monoidal functor of Lemma 3.9 to see $M$ as a “constant” monoid object in $\operatorname{Fun}(K, \mathcal{M})$. Through the monoidal action of $\operatorname{Fun}(K, \mathcal{M})$ on $\operatorname{Fun}(K, \mathcal{X})$ introduced by Lemma 3.7, we can look at the $\infty$-category

$$\mathbf{LMod}^M(\operatorname{Fun}(K, \mathcal{X}))$$

of $M$-modules in $\operatorname{Fun}(K, \mathcal{X})$. We then have, as a special case of Lemma 3.8 an equivalence (in fact an isomorphism)

$$\mathbf{LMod}^M(\operatorname{Fun}(K, \mathcal{X})) \simeq \operatorname{Fun}(K, \mathbf{LMod}^M(\mathcal{X})).$$

Indeed, the left hand side corresponds to the fiber of $\mathbf{LMod}(\operatorname{Fun}(K, \mathcal{X})) \simeq \operatorname{Fun}(K, \mathbf{LMod}(\mathcal{X}))$ over $M \in \operatorname{Fun}(K, \mathbf{Mon}(\mathcal{M}))$. However, given that $M$ is in $\mathbf{Mon}(\mathcal{M})$ this actually is a fiber of $F_K(\mathbf{LMod}(\mathcal{X}))$, and hence can be identified with the simplicial set of functors from $K$ to the fiber of $\mathbf{LMod}(\mathcal{X})$ as explained in Proposition 2.7. This also shows that these equivalences are natural in $M$.

We will write $\operatorname{End}(\mathcal{C})$ for the simplicial monoid of endomorphisms of an $\infty$-category $C$. By 3.4, it has the structure of a monoidal $\infty$-category. In [16] Lurie defines the *category of monads on $\mathcal{C}$*, which we denote by $\mathbf{Mnd}_{\mathcal{C}}$, to be the category of monoid objects in $\operatorname{End}(\mathcal{C})$. Given a monad $M \in \mathbf{Mnd}_{\mathcal{C}}$ acting on a category $\mathcal{E}$, and a monad $T$ on $\mathcal{C}$, we write $\mathcal{E}^T$ for the category of $T$-modules.

17

**Construction 3.11.** Let $\mathcal{C}$ and $\mathcal{D}$ be two $\infty$-categories. In [16], Lurie construct an action of $\operatorname{End}(\mathcal{C})$ on $\operatorname{Fun}(\mathcal{D}, \mathcal{C})$ by looking at the strict action of the simplicial monoid $\operatorname{End}(\mathcal{C})$ on the simplicial set $\operatorname{Fun}(\mathcal{D}, \mathcal{C})$.

This is however equivalent to the construction we discussed above by combining the action of $\operatorname{Fun}(\mathcal{D}, \operatorname{End}(\mathcal{C}))$ on $\operatorname{Fun}(\mathcal{D}, \mathcal{D})$ obtained from Lemma 3.7 and the monoidal functor $\operatorname{End}(\mathcal{C}) \rightarrow \operatorname{Fun}(\mathcal{D}, \operatorname{End}(\mathcal{C}))$ from Lemma 3.9.

Indeed, we start from the strict action of $\operatorname{End}(\mathcal{C})$ on $\mathcal{C}$, which can be encoded by a functor $\Delta^{op} \times \Delta^1 \rightarrow \operatorname{Set}_{\Delta}$ as discussed in Remark 3.4, and our construction in Lemma 3.7 using $F_K$ is known (by Proposition 2.7) to be equivalent to post-composing this functor by $\operatorname{Fun}(K, -)$. But this is precisely the strict action considered in the first paragraph.

From the discussion of 3.10 and 3.8 above we obtain

**Lemma 3.12.** *The natural functor*

$$\operatorname{Fun}(K, \mathcal{C})^T \rightarrow \operatorname{Fun}(K, \mathcal{C}^T)$$

*is an equivalence of $\infty$-categories, compatible to the forgetful functor to $\operatorname{Fun}(K, \mathcal{C})$.*

The final ingredient to Lurie's theory of monads is the notion of *endomorphism object*. Given a monoidal $\infty$-category $\mathcal{C}$ acting on an $\infty$-category $\mathcal{X}$ and $X \in \mathcal{X}$ any object, Lurie considers the $\infty$-category $\mathcal{C}[X]$ which can informally be described as the $\infty$-category of object $Y \in \mathcal{C}$ endowed with a map $Y \otimes X \rightarrow X$ in $\mathcal{X}$ (see Definition 4.7.1.1 in [16] for a more formal statement).

**Definition 3.13.** Let $\mathcal{C}$ be a monoidal $\infty$-category and $\mathcal{X}$ an $\infty$-category with an action of $\mathcal{C}$. An *endomorphism object* for an object $X \in \mathcal{X}$ is (if it exists) a terminal object in the category $\mathcal{C}[X]$.

As usual, we will, in an abuse of language, say that an object $\operatorname{End}(X) \in \mathcal{C}$ is an endomorphisms object of $X$ if it is the image of a terminal object in $\mathcal{C}[X]$ by the forgetful functor $\mathcal{C}[X] \rightarrow \mathcal{C}$. Lurie also shows in [16, Remark 4.7.1.33 and Proposition 4.7.1.34] that:

**Proposition 3.14.** *In the situation above, the $\infty$-category $\mathcal{C}[X]$ admits a monoidal structure for which the forgetful functor $\mathcal{C}[X] \rightarrow \mathcal{C}$ is monoidal.*

18

**Proposition 3.15.** *Given $\mathcal{C}$ a monoidal $\infty$-category and $\mathcal{X}$ an $\infty$-category with an action of $\mathcal{C}$, if $X \in \mathcal{X}$ admits an endomorphisms object $\underline{\mathrm{End}}(X) \in \mathcal{C}$, then $\underline{\mathrm{End}}(X)$ is a monoid object, it acts on $X$, and we have equivalences $\mathrm{Map}_{\mathbf{Mon}(\mathcal{C})}(B, \underline{\mathrm{End}}(X)) \simeq \mathbf{LMod}_B^X(\mathcal{X})$, natural in $B \in \mathbf{Mon}(\mathcal{C})$.*

Note that the identity arrow $\underline{\mathrm{End}}(X) \rightarrow \underline{\mathrm{End}}(X)$ in particular corresponds to an action of the monoid $\underline{\mathrm{End}}(X)$ on $X$ which we call the canonical action of $\underline{\mathrm{End}}(X)$ on $X$.

*Proof.* The equivalence is essentially that of [16, Corollary 4.7.1.41], which is deduced from [16, Corollary 4.7.1.40]. However, we should note that [16, Corollary 4.7.1.41] do not explicitly claims that this equivalence is natural in $B$ (only that it is “canonical”). It seems that the naturality of the equivalence is implicit, and is later implicitly used in the rest of Section 4.7 of [16]. For this reason, we decided to explain some key points of the proof from section 4.7.1 of [16] and especially clarify how the naturality follows.

A first remark is that Lurie introduces an alternative model for $\mathcal{C}[X]$, more precisely he constructs a monoidal $\infty$-category $\mathcal{C}^+[X]$ for each $X \in \mathcal{X}$, such that there is a trivial fibration $\mathcal{C}^+[X] \rightarrow \mathcal{C}[X]$ and which has slightly better properties than $\mathcal{C}[X]$. By examining the proof of [16, Corollary 4.7.1.40], the equivalence comes from a string of equivalences

$$\mathbf{Mon}(\mathcal{C})_{/\underline{\mathrm{End}}(X)} \leftarrow \mathbf{Mon}(\mathcal{C}^+[X])_{/T_X} \rightarrow \mathbf{Mon}(\mathcal{C}^+[X]) \rightarrow \mathbf{LMod}^X(\mathcal{X}), \quad (2)$$

where $T_X$ is a terminal object of $\mathcal{C}^+[X]$ whose image in $\mathcal{C}$ is $\underline{\mathrm{End}}(X)$. The fact that such an object exists exactly translates to the assumption that $X$ admits an endomorphism object $\underline{\mathrm{End}}(X)$. As a terminal object of the monoidal $\infty$-category $\mathcal{C}^+[X]$, it follows from Corollary 3.2.2.5 and Proposition 4.1.3.19 of [16] that $T_X$ has a monoid structure that makes it a terminal object of $\mathbf{Mon}(\mathcal{C}^+[X])$. The monoid structure on $\underline{\mathrm{End}}(X)$ is obtained from the one on $T_X$ as the functor $\mathcal{C}^+[X] \rightarrow \mathcal{C}$ is monoidal.

The theorem is deduced from these equivalences and the fact that all the categories involved admits right fibrations to $\mathbf{Mon}(\mathcal{C})$ and all functors in (2) are compatible (up to equality) to these fibrations. Hence taking the fibers over a monoid $B \in \mathbf{Mon}(\mathcal{C})$ in the zig-zag of equivalence (2) gives a series of equivalences:

$$\mathrm{Map}_{\mathbf{Mon}(\mathcal{C})}(B, \underline{\mathrm{End}}(X)) \leftarrow (\mathbf{Mon}(\mathcal{C}^+[X])_B)_{/T_X} \rightarrow \mathbf{Mon}(\mathcal{C}^+[X])_B \rightarrow \mathbf{LMod}_B^X(\mathcal{X}) \quad (3)$$

19

where the $B$ index denotes fiber over $B$. The (contravariant) functoriality in $B$ of these all these constructions and the naturality of these equivalence hence follows immediately from the straightening construction.

The functor $\mathbf{Mon}(\mathcal{C})_{/\mathrm{End}(X)} \rightarrow \mathbf{Mon}(\mathcal{C})$ is the obvious forgetful functor and is hence a right fibration (by the dual of [15, Corollary 2.1.2.2]). The functor $\theta : \mathcal{C}^{+}[X] \rightarrow \mathcal{C}$ constructed in [16, Proposition 4.7.1.39] induces a right fibration $\mathbf{Mon}(\mathcal{C}^{+}[X]) \rightarrow \mathbf{Mon}(\mathcal{C})$ (also by [16, Proposition 4.7.1.39]). As $T_X$ is sent to $\mathrm{End}(X)$ by this functor, this induces a right fibration $\mathbf{Mon}(\mathcal{C}^{+}[X])_{/T_X} \rightarrow \mathbf{Mon}(\mathcal{C})_{/\mathrm{End}(X)}$. This clearly equips the first three categories with right fibrations to $\mathbf{Mon}(\mathcal{C})$ with the first two functor being compatible to these (by functoriality of the slice construction).

The functor $\mathbf{LMod}^X(\mathcal{X}) \rightarrow \mathbf{Mon}(\mathcal{C})$ is simply the composite of the functor $\mathbf{LMod}^X(\mathcal{X}) \rightarrow \mathbf{LMod}(\mathcal{X})$ with the forgetful functor $\mathbf{LMod}(\mathcal{X}) \rightarrow \mathbf{Mon}(\mathcal{C})$, it can be seen as the top of arrow in the pullback:

$$\begin{array}{ccc} \mathbf{LMod}^X(\mathcal{X}) & \longrightarrow & \{X\} \times \mathbf{Mon}(\mathcal{C}) \\ \downarrow & \downarrow & \downarrow \\ \mathbf{LMod}(\mathcal{X}) & \longrightarrow & \mathcal{X} \times \mathbf{Mon}(\mathcal{C}) \end{array}$$

Given that the bottom map is an iso-fibration, it follows that $\mathbf{LMod}^X(\mathcal{X}) \rightarrow \mathbf{Mon}(\mathcal{C})$ is a quasi-fibration. The fact that it is a right fibration will be deduced later from the equivalence with the right fibration $\mathbf{Mon}(\mathcal{C}^{+}[X]) \rightarrow \mathbf{Mon}(\mathcal{C})$ (see [16, Corollary 4.7.1.42]).

So, if we consider the diagram:

$$\begin{array}{ccc} \mathbf{Mon}(\mathcal{C}^{+}[X]) & \longrightarrow & \mathbf{LMod}^X(\mathcal{X}) \\ & \searrow & \downarrow \\ & \mathbf{Mon}(\mathcal{C}) & \end{array}$$

where the diagonal map is the map $\theta'$ mentioned above (whose fibre over $B$ is $\mathbf{Mon}(\mathcal{C}^{+}[X])_B$), the horizontal map is the equivalence of [16, Theorem 4.7.1.34], and the vertical map is the forgetful functor, which is a cartesian fibration. One can then check from the explicit construction of the horizontal map given in [16] that the above diagram commutes, since all functors involved are induced by 'forgetful functors' between various full subcategories of functor categories from (nerve of) 1-categories. Hence producing the last compatibility we needed. $\square$

20

*Remark 3.16.* Consider the $\infty$-category $\mathbf{Cat}_{\infty}$ of all $\infty$-categories with the usual cartesian monoidal structure. Then for any $\infty$-category $\mathcal{C} \in \mathbf{Cat}_{\infty}$, its endomorphism object $\underline{\mathrm{End}}(\mathcal{C})$ is just the $\infty$-category of endofunctors of $\mathcal{C}$, and Proposition 3.15 makes it into a monoidal $\infty$-category acting on $\mathcal{C}$. Though in this case given that $\mathrm{End}(\mathcal{C})$ can simply be concretely defined as the simplicial monoid of maps $\mathcal{C} \to \mathcal{C}$ one can also obtain this monoidal structure in much more explicit way from its strictly associative monoid structure. It is fairly easy to check that the two descriptions are equivalent.

Using the action of $\mathrm{End}(\mathcal{C})$ on $\mathrm{Fun}(\mathcal{D}, \mathcal{C})$ mentioned in Construction 3.11, we can specialize the notion of endomorphism object to the notion of endomorphisms monads. Following Definition 4.7.3.2 of [16] we have:

**Definition 3.17.** An *endomorphism monad* $T$ for a functor $U : \mathcal{D} \to \mathcal{C}$ is a monad $T \in \mathbf{Mnd}(\mathcal{C}) = \mathbf{Mon}(\mathrm{End}\mathcal{C})$ with an action of $T$ on $F$ such that the action map $TU \to U$ identify $T$ as an endomorphism object for $U$.

*Remark 3.18.* Let $U : \mathcal{D} \to \mathcal{C}$ be a functor that admits an endomorphism object $\underline{\mathrm{End}}(U) \in \mathrm{End}(\mathcal{C})$, for the action of $\mathrm{End}(\mathcal{C})$ on $\mathrm{Fun}(\mathcal{D}, \mathcal{C})$ from Construction 3.11. By Proposition 3.15, $\underline{\mathrm{End}}(U)$ gets a monoid (i.e. monad) structure, and a canonical action of $\underline{\mathrm{End}}(U)$ on $U$, obtained from the identity map of $\underline{\mathrm{End}}(U)$ through the equivalence of Proposition 3.15. This monad $\underline{\mathrm{End}}(U)$, with its action on $U$, is then an endomorphisms monad for $U$ in the sense of Definition 3.17, and any endomorphism monad is of this form (in an essentially unique way).

Indeed, saying that $T$ is a monad acting on $U$, means, by [16, Theorem 4.7.1.34], that when we use the action map $TU \to T$ to identify $T$ with an object of $\mathrm{End}(\mathcal{C})[U]$ it has a monoid structure. Now, as Definition 3.17 asks for $T$, endowed with this map $TU \to U$, be a terminal object in $\mathrm{End}(\mathcal{C})[U]$ (by Definition 3.13), this monoid structure is essentially unique, and makes $T$ into the terminal monoid in $\mathrm{End}(\mathcal{C})[U]$.

Now, the action of $\underline{\mathrm{End}}(U)$ on $U$ we mentioned is obtained from the identity of $\underline{\mathrm{End}}(U)$ through the equivalence of categories $\mathbf{Mon}(\mathrm{End}(\mathcal{C}))_{\mathrm{End}(U)} \simeq \mathbf{Mon}(\mathrm{End}(\mathcal{C})[U])$. Since the identity is terminal in the slice category, it corresponds to a terminal object of $\mathbf{Mon}(\mathrm{End}(\mathcal{C})[U])$, so that both description boils down to “terminal objects in $\mathbf{Mon}(\mathrm{End}(\mathcal{C})[U])$”.

Given this, we will denote $\underline{\mathrm{End}}(U)$ the endomorphism monad of $U$ if it exists.

Lemma 4.7.3.1 of [16] describes the endomorphism monads of right adjoint functor in the usual way:

21

**Proposition 3.19.** *If $U : \mathcal{D} \to \mathcal{C}$ is a functor with a left adjoint $F$, then $U \circ F : \mathcal{C} \to \mathcal{C}$ endowed with the map $U \circ F \circ U \to U$ given by applying $U$ to the unit of adjunction is an endomorphisms monad for $U$.*

We can construct a functor $\mathbf{Mnd}_{\mathcal{C}}^{op} \to \mathbf{Cat}_{\infty}$ that sends $T$ to $\mathcal{C}^T$ by applying straightening to the Cartesian fibration $\mathbf{LMod}(\mathrm{End}(\mathcal{C})) \to \mathbf{Mon}(\mathrm{End}(\mathcal{C}))$ associated to the action in Construction 3.11.

**Proposition 3.20.** *The functor*

$$\begin{array}{ccc} (\mathbf{Mnd}_{\mathcal{C}})^{op} & \to & (\mathbf{Cat}_{\infty})_{/\mathcal{C}} \\ T & \mapsto & \mathcal{C}^T \end{array}$$

*Corestricted to the full subcategory of right adjoint functors admit a left adjoint that sends a right adjoint functor $U : \mathcal{D} \to \mathcal{C}$ to its endomorphism monad.*

*Proof.* To show the existence of the adjoint, it suffices to show that the functor $T \mapsto \mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^T)$ is representable by $\underline{\mathrm{End}}(U)$. By applying 3.15 to the action of $\mathrm{End}(\mathcal{C})$ on $(\mathbf{Cat}_{\infty})_{/\mathcal{C}}$ given by 3.11, and applying 3.12, we get equivalences (natural in $T$)

$$\mathrm{Map}_{\mathbf{Mnd}_{\mathcal{C}}}(T, \underline{\mathrm{End}}(U)) \simeq \mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C})^T \simeq \mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C}^T)$$

where $\mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C})^T$ and $\mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C}^T)$ are the (homotopy) fibers of $\mathrm{Map}_{\mathbf{Cat}_{\infty}}(\mathcal{D}, \mathcal{C})^T$ and $\mathrm{Map}_{\mathbf{Cat}_{\infty}}(\mathcal{D}, \mathcal{C}^T)$ over $U \in \mathrm{Map}_{\mathbf{Cat}_{\infty}}(\mathcal{D}, \mathcal{C})$. By the description of mapping spaces in a slice $\infty$-category from [15, Proposition 5.5.5.12], one has an equivalence $\mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C}^T) \simeq \mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^T)$, which in total gives an equivalence natural in $T$:

$$\mathrm{Map}_{\mathbf{Mnd}_{\mathcal{C}}}(T, \underline{\mathrm{End}}(U)) \simeq \mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^T)$$

$\square$

**Lemma 3.21.** *Let $U : \mathcal{D} \to \mathcal{C}$ be a functor of $\infty$-categories. The unit of the adjunction of Proposition 3.20 can be identified with the canonical map $\mathcal{D} \to \mathcal{C}^{\underline{\mathrm{End}}(U)}$ determined by the action of $\underline{\mathrm{End}}(U)$ on $U$, through the equivalence $\mathrm{Fun}(\mathcal{D}, \mathcal{C}^{\underline{\mathrm{End}}(U)}) \simeq \mathrm{Fun}(\mathcal{D}, \mathcal{C})^{\underline{\mathrm{End}}(U)}$ of Lemma 3.12.*

22

Proof. We need to chase through the series of equivalences in the proof of Proposition 3.20 the image of $id: \underline{\mathrm{End}}(U) \to \underline{\mathrm{End}}(U)$ in $\mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^{\underline{\mathrm{End}}(U)})$.

The first step of this series of equivalences

$$\mathrm{Map}_{\mathbf{Mnd}_{\mathcal{C}}}(T, \underline{\mathrm{End}}(U)) \simeq \mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C})^{T}$$

sends the identity of $\underline{\mathrm{End}}(U)$ to the canonical action of $\underline{\mathrm{End}}(U)$ on $U$ (see Remark 3.18), essentially by definition of this action. The map to $\mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^{T})$ is then essentially just the isomorphism $\mathrm{Fun}(\mathcal{D}, \mathcal{C}^{\underline{\mathrm{End}}(U)}) \simeq \mathrm{Fun}(\mathcal{D}, \mathcal{C})^{\underline{\mathrm{End}}(U)}$, hence the result.

$\square$

A right adjoint functor $U: \mathcal{E} \to \mathcal{C}$ is said to be monadic if the unit of adjunction $\mathcal{E} \to \mathcal{C}^{\underline{\mathrm{End}}(U)}$ is an equivalence.

Theorem 4.7.3.5 of [16] is an $\infty$-categorical version of the Barr-Beck theorem. It states that a right adjoint functor $U: \mathcal{E} \to \mathcal{C}$ is monadic if and only it is conservative and for every simplicial object in $\mathcal{E}$ whose image by $U$ is split has a colimit which is preserved by $U$.

Given that forgetful functors of the form $\mathcal{C}^{T} \to \mathcal{C}$ themselves satisfy all these conditions, this shows that the adjunction of Proposition 3.20 is an idempotent, and identifies the category $\mathbf{Mnd}_{\mathcal{C}}$ of monads on a category $\mathcal{C}$ with the opposite of the category of monadic right adjoint functor $\mathcal{E} \to \mathcal{C}$, seen as a full subcategory of $(\mathbf{Cat}_{\infty})_{/\mathcal{C}}$. In particular, one deduces:

**Theorem 3.22.** For any $\infty$-category $\mathcal{C}$, the functor

$$\begin{array}{c c c} (\mathbf{Mnd}_{\mathcal{C}})^{op} & \to & (\mathbf{Cat}_{\infty})_{/\mathcal{C}} \\ T & \mapsto & \mathcal{C}^{T} \end{array}$$

is fully faithful and identifies $(\mathbf{Mnd}_{\mathcal{C}})^{op}$ with $\mathbf{RMd}_{\mathcal{C}}$ the reflective full subcategory of $(\mathbf{Cat}_{\infty})_{/\mathcal{C}}$ of monadic right adjoint functors.

This result was alluded to in Remark 4.7.3.8 of [16], but wasn't proven.

We finish with a consequence of Lurie's Barr-Beck theorem that will be useful in a few places:

**Proposition 3.23.** Given a (homotopy) pullback square of $\infty$-categories:

23

$$\begin{array}{c} \mathcal{D}' \xrightarrow{G} \mathcal{D} \\ \downarrow V^{-1} \quad \downarrow U \\ \mathcal{C}' \xrightarrow{F} \mathcal{C} \end{array}$$

*if $U$ is a monadic right adjoint functor and $V$ is a right adjoint functor then $V$ is monadic.*

*Proof.* We show that if $U$ satisfies the conditions of Lurie's Barr-Beck monadicity theorem (i.e. Theorem 4.7.3.5 of [15]), then so does $V$.

An arrow $f \in \mathcal{D}'$ is invertible if and only if both its image and $\mathcal{C}'$ and $\mathcal{D}$ are invertible. But if its image in $\mathcal{C}'$ is invertible, then its image in $\mathcal{C}$ is as well. Hence, as $U$ is conservative, its image in $\mathcal{D}$ is also invertible. Thus, $V$ is conservative.

Let $X : \Delta \to \mathcal{D}'$ be a $V$-split simplicial diagram. Its image in $\mathcal{D}$ is a $U$-split simplicial diagram, hence it admit a colimit which is preserved by $U$. The colimit of $X$ in $\mathcal{C}'$ is split, and is thus preserved by $F$, since split colimits are preserved by all functors ([15, Lemma 6.1.3.16]). It follows that $X$ has a colimit both in $\mathcal{D}$ and $\mathcal{C}'$ which is preserved by $U$ and $F$. Hence, it has a colimit in $\mathcal{D}'$ which is preserved by both projections by the lemma below. $\square$

**Lemma 3.24.** *Suppose that we have a diagram*

$$\begin{array}{c} N(I)^{\phi} \xrightarrow{\phi} \mathcal{D} \longrightarrow \mathcal{X} \\ \downarrow \quad \downarrow \quad \downarrow \quad g \downarrow \\ \mathcal{Y} \xrightarrow{f} \mathcal{Z} \end{array}$$

*where the square is a homotopy pullback square of $\infty$-categories and $I$ is any category. Suppose that $\phi$ determines a colimit diagram in $\mathcal{X}, \mathcal{Y}, \mathcal{Z}$. Then $\phi$ is a colimit diagram in $\mathcal{D}$.*

*Proof.* Because of the Quillen equivalence between Bergner's model structure on simplicial categories and Joyal's structure, we can replace the above diagram with the nerve of a diagram of (fibrant) simplicial categories. By [15, 4.2.4.1], we thus reduce to the corresponding statement about simplicial categories, where the homotopy pullback is taken with respect to Bergner's

24

model structure. For each pair of objects $x, y \in \mathcal{Y}, x', y' \in \mathcal{X}$ such that $f(x) = g(x'), f(y) = g(y')$, we have a homotopy pullback:

$$\begin{array}{ccc} \text{Map}_{\mathcal{D}}((x, x'), (y, y')) & \longrightarrow & \text{Map}_{\mathcal{X}}(x, y) \\ \downarrow & & \downarrow \\ \text{Map}_{\mathcal{Y}}(x, y) & \longrightarrow & \text{Map}_{\mathcal{Z}}(f(x), f(y)) \end{array}$$

This follows from the construction of homotopy pullbacks in Bergner's model structure. The result now follows from the description of homotopy colimits internal to a fibrant simplicial category ([15, Remark A.3.3.13]) and the fact that homotopy pullbacks and homotopy colimits of simplicial sets commute (see [15, 6.1.3.14]).

Finally, we will need the following lemma that is essentially a consequence of Theorem 3.22:

**Lemma 3.25.** *Let $U_1 : \mathcal{D}_1 \to \mathcal{C}$ and $U_2 : \mathcal{D}_2 \to \mathcal{C}$ be two monadic right adjoint functors, with left adjoints $L_1$ and $L_2$ and $t : \mathcal{D}_1 \to \mathcal{D}_2$ be a functor such that $U_1 \simeq U_2 t$. Then $t$ is an equivalence of $\infty$-categories if and only if the natural transformation $L_2 \to t L_1$ obtained from the isomorphism $U_1 \to U_2 t$ through the adjunction is an equivalence.*

*Proof.* Under the equivalence Theorem 3.22, $t$ corresponds to a morphisms of monads $\text{End}(U_2) \to \text{End}(U_1)$, and $t$ is an equivalence if and only if this morphism of monads is an equivalence. At the level of underlying endofunctors, the morphism of monads identifies with a natural transformation $U_2 L_2 \to U_1 L_1$ induced by the action of $U_2 L_2$ on $U_1 \simeq U_2 \circ t$. Thus, it can be described as the natural transformation $U_2 L_2 \to U_1 L_1 \simeq U_2 t L_1$ obtained under the adjunction $L_1 \dashv U_1$ from the map $U_2 L_2 U_2 t \to U_2 t$ induced by the counit $L_2 U_2 \to Id$.

Unfolding this, we see that up canonical isomorphism, this map $U_2 L_2 \to U_1 L_1$ is exactly the image under $U_2$ of the natural transformation $L_2 \to t L_1$. As $U_2$ is conservative it indeed follows that the morphism of monads is an equivalence if and only if $L_2 \to t L_1$ is an equivalence.

*Remark 3.26.* In the rest of the paper, we will never use explicitly use the notion of monads, but always work with monads through the equivalence of

25

Theorem 3.22. The only exception to this is Lemma 3.25 that will be used in the proof of Theorem 6.3.

In particular, any theory of monads for which Theorem 3.22 and Lemma 3.25 are valid can be used instead of Lurie's theory of monads. We suspect this should apply for example to Riehl-Verity theory of monads on $\infty$-categories from [18].

## 4 Partial adjoints and functoriality of the Kleisli category

**Definition 4.1.** If $T$ is a monad on an $\infty$-category $\mathcal{C}$, we denote by $\mathcal{C}_T$ the full subcategory of the $\infty$-category $\mathcal{C}^T$ of $T$-algebras on free $T$-algebras. That is, those $T$-algebras in the essential image of the free $T$-algebra functor $\mathcal{C} \rightarrow \mathcal{C}^T$. $\mathcal{C}_T$ is called the *Kleisli category* of $\mathcal{C}$.

As the title suggests, the goal of this section is to study the functoriality properties of the construction $T \mapsto \mathcal{C}_T$. While $T \mapsto \mathcal{C}^T$ has a contravariant functoriality, the Kleisli category has a covariant functoriality essentially given by taking the left adjoint $f_!$ to $f^*$ for $f: T \rightarrow M$ a morphism of monads. However (even in ordinary category theory) the existence of a left adjoint $f_! \dashv f^*$ is in general not guaranteed, and when it exists its construction generally requires a complicated transfinite construction or an application of the special adjoint functor theorem. In particular, given that we have not proven at this point that the $\infty$-category of algebras $\mathcal{C}^T$ has colimits or is a presentable category it would not be reasonable to assume that such a left adjoint exists. Instead we need to consider $f_!$ as a 'partial left adjoint' in the following sense:

**Definition 4.2.** Let $R: \mathcal{C} \rightarrow \mathcal{D}$ be a functor between $\infty$-categories. Let $\mathcal{D}' \subset \mathcal{D}$ be a full subcategory. One says that $R$ has a *partial left adjoint* on $\mathcal{D}'$ if for all $X \in \mathcal{D}'$, the functor:

$$\begin{aligned} \mathcal{C} &\rightarrow \mathcal{S} \\ Y &\mapsto \text{Map}_{\mathcal{D}}(X, R(Y)) \end{aligned}$$

is representable. If $\mathcal{C}' \subset \mathcal{C}$ is a full subcategory of $\mathcal{C}$, one says that $R$ has a partial left adjoint from $\mathcal{D}' \rightarrow \mathcal{C}'$ if for all $X \in \mathcal{D}'$ the object $Y$ as above is in $\mathcal{C}'$. We define *partial right adjoint* in the dual way.

26

By the $\infty$-categorical Yoneda lemma, it follows that when $R$ has a partial left adjoint $\mathcal{D}' \rightarrow \mathcal{C}'$ then there is an essentially unique functor $F : \mathcal{D}' \rightarrow \mathcal{C}$, called the partial left adjoint of $R$, endowed with an adjunction isomorphism:

$$\operatorname{Map}_{\mathcal{D}}(X, R(Y)) \simeq \operatorname{Map}_{\mathcal{C}}(F(X), Y)$$

natural in $X \in \mathcal{D}'$ and $Y \in \mathcal{C}$.

As mentioned above, our main example of partial left adjoints comes from morphisms of monads:

**Proposition 4.3.** *Let $f : T \rightarrow M$ be a morphism of monads on a category $\mathcal{C}$. Then the forgetful functor between their categories of algebras $f^* : \mathcal{C}^M \rightarrow \mathcal{C}^T$ has a partial left adjoint $f_! : \mathcal{C}_T \rightarrow \mathcal{C}_M$ between the full subcategories $\mathcal{C}_T \subset \mathcal{C}^T$ and $\mathcal{C}_M \subset \mathcal{C}^M$ of free algebras.*

*Proof.* Let $U : \mathcal{C}^T \rightarrow \mathcal{C}$ and $V : \mathcal{C}^M \rightarrow \mathcal{C}$ be the two forgetful functors.

For any free algebra $X = T(A) \in \mathcal{C}_T$ and $Y$ an $M$-algebra, we have a series of isomorphisms all natural in $Y \in \mathcal{C}^M$:

$$\operatorname{Map}_{\mathcal{C}^T}(X, f^*Y) \simeq \operatorname{Map}_{\mathcal{C}}(A, U(f^*Y)) \simeq \operatorname{Map}_{\mathcal{C}}(A, V(Y)) \simeq \operatorname{Map}_{\mathcal{C}^M}(MA, Y).$$

Thus, the functor $\operatorname{Map}_{\mathcal{C}^T}(X, f^*\text{-})$ is representable by $MA$, which concludes the proof. $\square$

In order to study the functoriality properties of the Kleisli category construction, we will consider more generally the question of how partial left adjoints assemble into a $\mathbf{Cat}_{\infty}$-valued functor. This occurs in exactly the same way as left adjoints assemble into a $\mathbf{Cat}_{\infty}$-valued functor (as show for example for adjointable functors between locally presentable $\infty$-categories in [15, Corollary 5.5.3.4]). To remind ourselves of the main case of interest, i.e. the category of monads, we will use similar notation for the general case:

**Assumption 4.4.** Consider a functor $\mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$, denoted $d \mapsto X^d$. For $f : d \rightarrow d'$ an arrow in $\mathcal{D}$, we denote the induced functor by $f^* : X^{d'} \rightarrow X^d$.

We also assume that for each object $d \in \mathcal{D}$, we have a full subcategory $X_d \subset X^d$ such that for each edge $f : d \rightarrow d'$, $f^* : X^{d'} \rightarrow X^d$ has a partial left adjoint $f_! : X_d \rightarrow X_{d'}$.

It should be noted that this automatically implies that if $d$ and $d'$ are isomorphic in $\mathcal{D}$, then the subcategory $X_d$ and $X_d'$ are identified by the equivalence between $X^d$ and $X^{d'}$.

27

**Proposition 4.5.** *Let $X^{\bullet} : \mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$ be a functor as in Assumption 4.4 above. Then there is a functor $\mathcal{D} \rightarrow \mathbf{Cat}_{\infty}$ that sends each object of $d$ to $X_d$ and each arrow $f$ to $f_!$.*

A precise construction of the functor is given in the proof and will be important on a few occasions in the rest of the paper.

*Proof.* Let $\pi : \mathcal{X} \rightarrow \mathcal{D}$ be the cartesian fibration classified by $X$. Up to equivalence of $\infty$-categories one can freely assume that objects of $\mathcal{X}$ are pairs $(d, x)$ where $d$ is an object of $\mathcal{D}$ and $x$ is an object of $\mathcal{X}^d$.

We write $\mathcal{X}'$ for the full subcategory of $\mathcal{X}$ of objects of the form $(d, x)$ for $x \in \mathcal{X}_d$, and we claim that $\mathcal{X}' \rightarrow \mathcal{D}$ is a cocartesian fibration classifying a functor as described in the proposition.

Indeed, for each arrow $f : d' \rightarrow d$ and $x \in X_{d'}$, we have a unit arrow $x \rightarrow f^* f_! x$ in $X^{d'}$ constructed from the adjunction isomorphism in the usual way. It corresponds to an arrow $(d', x) \rightarrow (d, f_! x)$ in $\mathcal{X}$. Exactly as in the case of actual adjunction (see the proof of “(2) $\Rightarrow$ (1)” of Proposition 5.2.2.8 of [15]), the adjunction isomorphism shows that this arrow is a locally $\pi$-cocartesian arrow in $\mathcal{X}$.

And Corollary 5.2.2.4 of [15] shows that, as $\pi$ is a Cartesian fibration, any locally $\pi$-coCartesian arrow is actually coCartesian, so this construction provide us with coCartesian lifts of any arrow $d' \rightarrow d$ for any object in $\mathcal{X}'$ over $d'$.

By the definition of $\mathcal{X}'$ its fiber over an object $d \in \mathcal{D}$ is indeed equivalent to $X_d$, and the way we constructed the cocartesian lift shows the functoriality is exactly the $f_!$ functor.

It immediately follows from Proposition 4.3 and Proposition 4.5 that:

**Corollary 4.6.** *The Kleisli category construction $T \mapsto \mathcal{C}_T$ defines a functor $\mathbf{Mnd}_{\mathcal{C}} \rightarrow \mathbf{Cat}_{\infty}$. Each morphism of monads $f : T \rightarrow M$ is sent to the partial left adjoint $f_! : \mathcal{C}_T \rightarrow \mathcal{C}_M$ to $f^*$.*

*Remark 4.7.* Because the initial object of $\mathbf{Mnd}_{\mathcal{C}}$ is the identity monad $I$ and the Kleisli category $\mathcal{C}_I$ of $I$ is equivalent to $\mathcal{C}$, it immediately follows that the Kleisli category construction can actually be seen as a functor from $\mathbf{Mnd}_{\mathcal{C}}$ to the coslice category $(\mathbf{Cat}_{\infty})_{\setminus \mathcal{C}}$, sending each monad $T$ to the free algebra functor $\mathcal{C} \rightarrow \mathcal{C}_T$.

28

**Proposition 4.8.** *Let $X^{\bullet}$ and $Y^{\bullet}$ be two functors $\mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$ as in Assumption 4.4. Let $\lambda : X^{\bullet} \rightarrow Y^{\bullet}$ be a natural transformation between them such that:*

1. *For each object $d \in \mathcal{D}$, the functor $\lambda(d) : X^d \rightarrow Y^d$ sends $X_d$ to $Y_d$.*
2. *For each morphism $f : d' \rightarrow d$ in $\mathcal{D}$, the natural transformation $\lambda(d)f_! \rightarrow f_!\lambda(d')$ obtained from the naturality square $\lambda(d')f^* \xrightarrow{\sim} f^*\lambda(d)$ through the partial adjunction between $f_!$ and $f^*$, is an isomorphism.*

*Then, there is a natural transformation $\lambda' : X_{\bullet} \rightarrow Y_{\bullet}$ between the functors $\mathcal{D} \rightarrow \mathbf{Cat}_{\infty}$ constructed in Proposition 4.5, which on objects is the restriction of $\lambda$ and whose naturality isomorphism is the natural isomorphism $\lambda(d)f_! \rightarrow f_!\lambda(d')$ mentioned above.*

*Proof.* Let $\mathcal{X}, \mathcal{Y} \rightarrow \mathcal{D}$ be the cartesian fibrations corresponding to $X, Y : \mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$. And let $\mathcal{X}', \mathcal{Y}' \rightarrow \mathcal{D}$ be the cocartesian fibration constructed in the proof of Proposition 4.5.

By functoriality of the Grothendieck (or unstraightening) construction, the natural transformation $\lambda$ induces a functor $V : \mathcal{X} \rightarrow \mathcal{Y}$ in $(\mathbf{Cat}_{\infty})_{/\mathcal{D}}$ that preserves cartesian arrows. Assumption 1, immediately shows that $V$ restricts to a functor $\mathcal{X}' \rightarrow \mathcal{Y}'$ (also in $(\mathbf{Cat}_{\infty})_{/\mathcal{D}}$). Assumption 2 translates to the fact that this functor sends cocartesian arrows to cocartesian arrows. Indeed, by uniqueness of cocartesian lifts, any cocartesian arrow in $\mathcal{X}$ is up to equivalence an arrow $(d, x) \rightarrow (d', f_!x)$ over $f : d \rightarrow d' \in \mathcal{D}$ corresponding to the unit of adjunction $x \rightarrow f^*f_!x$ as in the proof of Proposition 4.5, for $x \in X_d$. The functor $V$ sends such an arrow to the arrow $(d, \lambda^d(x)) \rightarrow (d, \lambda^{d'}f_!x)$. This in turn corresponds to $\lambda^d x \rightarrow f^*\lambda^{d'}f_!x$ which is the image of the co-unit $x \rightarrow f^*f_!x$ under $\lambda^d$ up to the isomorphism $\lambda^d f^* \simeq f^*\lambda^{d'}$. Under assumption (2), this maps identifies with the counit $\lambda^d(x) \rightarrow f^*f_!\lambda^d(x)$ and hence corresponds to a cocartesian arrow of $\mathcal{Y}'$.

As $V$ preserves cocartesian arrows from $\mathcal{X}'$ to $\mathcal{Y}'$, it corresponds to a natural transformation between the functors constructed in Proposition 4.5 with the properties claimed in the proposition. $\square$

**Proposition 4.9.** *Let $X^{\bullet} : \mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$ be a functor with subcategories $X_{\bullet}$ as in Proposition 4.5. Then there are natural transformation:*

$$(\mathcal{X}_d)^{op} \rightarrow \operatorname{Fun}(\mathcal{X}^d, \mathcal{S})$$

29

$$\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})$$

*which are levelwise the restriction of the Yoneda embeddings. Here, $X_d$ has its covariant functoriality from Proposition 4.5, $X^d$ has its original contravariant functoriality and we use the contravariant functoriality of $\text{Fun}(-,\mathcal{S})$ given by restriction of presheaves to make the right hand side into functors with the appropriate variance.*

*Proof.* $\text{Fun}(-,\mathcal{S})$ has two different functorialities. Firstly, it has the natural contravariant functoriality used in the statement of the proposition, where each induced map $f^*: \text{Fun}(\mathcal{X}^d, \mathcal{S}) \rightarrow \text{Fun}(\mathcal{X}^{d'}, \mathcal{S})$ induced by $f: X^{d'} \rightarrow X^d$ has a right adjoint. The second functoriality is then given by applying Proposition 4.5 to obtain a covariant functoriality $\mathcal{C} \mapsto \text{Fun}(\mathcal{C}, \mathcal{S})$, where morphisms acts as the left adjoint to the reindexing functors given by the contravariant functoriality. It was shown in section 6 of [12] that the Yoneda embeddings $\mathcal{C} \rightarrow \text{Pr}(\mathcal{C})$ can be made into a natural transformation when $\text{Pr}(\mathcal{C}) = \text{Fun}(\mathcal{C}^{op}, \mathcal{S})$ is endowed with this second functoriality.

In particular, we have a natural transformation $(\mathcal{X}^d)^{op} \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})$, or equivalently $\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})^{op}$ where on the right hand side $\text{Fun}(-,\mathcal{S})$ has its covariant (i.e. left adjoint) functoriality.

One can then apply Proposition 4.5 to $\mathcal{X}_d \subset (\mathcal{X}^d)$ to recover the covariant functoriality of $\mathcal{X}_d$ (given by the $(f_!)^{op}$) and to $d \mapsto \text{Fun}(\mathcal{X}^d, \mathcal{S})^{op}$ to recover its usual “precomposition” functoriality as in the proposition. Hence, Proposition 4.8 shows that the Yoneda embedding can be assembled into a natural transformation

$$(\mathcal{X}_d) \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})^{op}.$$

The first condition 1 is vacuous in this case given that the subcategories used on the right hand side are the whole category, and the second condition is easy to check. Indeed, the natural transformation between the left adjoint coming from the naturality square along a map $f: d \rightarrow d' \in \mathcal{D}$ is, for each $X \in \mathcal{X}_d$, the map in $(\text{Fun}(\mathcal{X}^{d'}, \mathcal{S}))^{op}$, which, when evaluated on a $Y \in \mathcal{X}^{d'}$ is the map

$$\text{Map}(f_!(X), Y) \rightarrow \text{Map}(X, f^*(Y))$$

obtained by applying the $f^*$ functoriality and precomposing with the unit $X \rightarrow f^* f_! X$. But essentially by definition, this map is an equivalence.

30

Taking opposite categories on both sides gives us the first natural transformation mentioned in the proposition:

$$\mathcal{X}_d^{op} \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S}),$$

which is levelwise given by the restriction of the Yoneda embedding. The second one can be obtained formally from the first ones: informally, a natural transformation $(\mathcal{X}_d)^{op} \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})$ can be seen as a dinatural transformation $(\mathcal{X}_d)^{op} \times \mathcal{X}^d \rightarrow \mathcal{S}$. This, in turn, can be seen as a natural transformation $\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})$ which is the second one. To avoid the use of dinatural transformations in this argument (which to the authors' knowledge have not been formalized in the $\infty$-categorical framework), one can use Proposition 5.1 of [8] or Proposition 2.3 of [10]. These assert that for any pairs of functors $F, G : \mathcal{C} \rightarrow \mathcal{D}$ the space of natural transformation from $F$ to $G$ can be described as the end$^{3}$:

$$\text{Map}(F, G) \simeq \int_{c \in \mathcal{C}} \text{Map}(F(c), G(c)).$$

In both cases a natural transformation $\lambda : F \rightarrow G$ corresponds to an element of the end whose component in $\text{Map}(F(c), G(c))$ is simply $\lambda_c : F(c) \rightarrow G(c)$.

Using this (and the functoriality of ends) we have isomorphisms:

$$\begin{aligned} \int_{d \in \mathcal{D}} \text{Fun}(\mathcal{X}_d^{op}, \text{Fun}(\mathcal{X}^d, \mathcal{S})) &\simeq \int_{d \in \mathcal{D}} \text{Fun}(\mathcal{X}_d^{op} \times \mathcal{X}^d, \mathcal{S}) \\ &\simeq \int_{d \in \mathcal{D}} \text{Fun}(\mathcal{X}^d, \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})). \end{aligned}$$

Through these isomorphisms, we hence obtain a natural transformation $\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})$ that for each $d$ is given by the restricted Yoneda embedding.

Applying this to the $\infty$-category of monads, we obtain:

**Corollary 4.10.** *The restricted Yoneda embeddings $\mathcal{C}^T \rightarrow \text{Pr}(\mathcal{C}_T)$ can be equipped with the structure of a natural transformation between functors $(\text{Mnd}_\mathcal{C})^{op} \rightarrow \text{Cat}_\infty$.*

$^{3}$The end of a functor $\mathcal{C} \times \mathcal{C}^{op} \rightarrow \mathcal{D}$ is the limit indexed by the twisted arrow category $\text{Tw}(\mathcal{C}) \rightarrow \mathcal{C} \times \mathcal{C}^{op}$. See [8] or [10]

31

## 5 The Monad-Theory Correspondence

Throughout this section, we fix a locally presentable $\infty$-category $\mathcal{E}$, as well as a *dense, small, full subcategory* $\mathcal{A} \subset \mathcal{E}$.

We write $\mathbf{PreTh}_{\mathcal{A}}$ for the full subcategory of $(\mathbf{Cat}_{\infty})_{\mathcal{A}/}$ of essentially surjective functors $\mathcal{A} \rightarrow \mathcal{K}$ (with $\mathcal{K}$ also being small). Objects of $\mathbf{PreTh}_{\mathcal{A}}$ are called $\mathcal{A}$-pretheories.

**Definition 5.1.** For a $\mathcal{A}$-pretheory $\mathcal{K}$, we define the category of $\mathcal{K}$-models as the pullback:

$$\begin{array}{ccc} \text{Mod}_{\mathcal{E}}(\mathcal{K}) & \longrightarrow & \text{Pr}(\mathcal{K}) \\ \downarrow & \downarrow & \downarrow \\ \mathcal{E} & \longrightarrow & \text{Pr}(\mathcal{A}), \end{array}$$

where the right vertical arrow is the restriction functor and the bottom horizontal arrow is the restricted Yoneda embedding, or “$\mathcal{A}$-nerve” functor. That is, it is the composite of the Yoneda embedding $\mathcal{E} \rightarrow \text{Pr}(\mathcal{E})$ with the restriction to $\mathcal{A} \subset \mathcal{E}$.

**Proposition 5.2.** *The forgetful functor $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \mathcal{E}$ is a monadic right adjoint functor. The functor $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \text{Pr}(\mathcal{K})$ is a fully faithful right adjoint (i.e. is an equivalence to the inclusion of a reflective subcategory).*

*Proof.* The functor $\text{Pr}(\mathcal{K}) \rightarrow \text{Pr}(\mathcal{A})$ is a monadic right adjoint functor. Indeed, it is conservative because $\mathcal{A} \rightarrow \mathcal{K}$ is essentially surjective. It satisfies the condition on split simplicial diagrams because it preserves all colimits and both $\text{Pr}(\mathcal{K})$ and $\text{Pr}(\mathcal{A})$ have all colimits.

Moreover, by Theorem 5.5.3.18 of [15], the above can be seen as a pullback in the category of presentable $\infty$-categories and accessible right adjoint functors, hence the functors $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \mathcal{E}$ and $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \text{Pr}(\mathcal{K})$ are both right adjoint functors.

The monadicity of the first one then follows from Proposition 3.23 and the second one is fully faithful since it is the pullback of $\mathcal{E} \rightarrow \text{Pr}(\mathcal{A})$ which is fully faithful as $\mathcal{A}$ is dense in $\mathcal{E}$. $\square$

**Construction 5.3.** The functoriality of the pullback in Definition 5.1 and the contravariant functoriality of $\mathcal{K} \mapsto \text{Pr}(\mathcal{K})$, make $\text{Mod}_{\mathcal{E}}(-)$ into a functor $\mathbf{PreTh}_{\mathcal{A}}^{op} \rightarrow (\mathbf{Cat}_{\infty})_{/\mathcal{E}}$. By using the identification of 3.22 and taking opposite categories, we obtain a functor:

32

$$\begin{array}{rcl} \mathbf{PreTh}_{\mathcal{A}} & \to & \mathbf{Mnd}_{\mathcal{E}} \\ \mathcal{K} & \mapsto & \mu^{\mathcal{K}}, \end{array}$$

which is characterized by the natural isomorphism $\mathcal{E}^{\mu^{\mathcal{K}}} \simeq \mathrm{Mod}_{\mathcal{E}}(\mathcal{K})$.

**Lemma 5.4.** *There is a functor $(\mathbf{Cat}_{\infty})_{\mathcal{A}/} \to \mathbf{PreTh}_{\mathcal{A}}$ which takes each arrow $\mathcal{A} \to \mathcal{X}$ to its essential image $\mathcal{A} \to \mathcal{Y} \subset \mathcal{X}$.*

*Proof.* We claim that in $\mathbf{Cat}_{\infty}$ essentially surjective functors and fully faithful functors form an orthogonal factorization system (in the sense of [15, Definition 5.2.8.8]). The result then follows from [15, Lemma 5.5.8.19].

Indeed, this is just the (-1)-connected case of the n-connected/n-truncated factorization which exists in any locally presentable $\infty$-category by Proposition 4.6 of [9]. $\mathbf{Cat}_{\infty}$ can be presented as the simplicial category of bifibrant objects of the variant of the Joyal model structure on marked simplicial sets (from [15, Proposition 3.1.3.7] in the special case where $S = \Delta[0]$), which is a simplicial combinatorial model category, so $\mathbf{Cat}_{\infty}$ is a locally presentable $\infty$-category by [15, Theorem A.3.7.6], and the factorization system exists. $\square$

**Definition 5.5.** Let $\mathrm{Th}: \mathbf{Mnd}_{\mathcal{E}} \to \mathbf{PreTh}_{\mathcal{A}}$ be the composite

$$\mathbf{Mnd}_{\mathcal{E}} \xrightarrow{\mathcal{E}_{\bullet}} (\mathbf{Cat}_{\infty})_{\mathcal{E}/} \xrightarrow{(-)\circ i} (\mathbf{Cat}_{\infty})_{\mathcal{A}/} \to \mathbf{PreTh}_{\mathcal{A}}$$

where the first functor is the Kleisli category functor constructed in Corollary 4.6 and the last functor is the functor from 5.4 that takes the fullyfaithful-essentially surjective factorization.

As shown in 2.2, to produce an adjunction of $\infty$-categories, it suffices to produce a counit and unit transformation, and verify the triangle identities on components. We will apply this strategy to show that $\mu^{(-)} \dashv \mathrm{Th}$.

**Construction 5.6.** Consider the commutative square from Definition 5.1. By taking the left adjoint of each functor, we get a commutative diagram in $(\mathrm{Cat}_{\infty})$:

$$\begin{array}{c} \mathcal{E}^{\mu^{\mathcal{K}}} \xleftarrow{\quad} \mathrm{Pr}(\mathcal{K}) \xleftarrow{y_{\mathcal{K}}} \mathcal{K} \\ \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{E} \xleftarrow{\quad} \mathrm{Pr}(\mathcal{A}). \end{array} \tag{4}$$

33

By taking the essential image of the top horizontal composite we get a map $\eta_{\mathcal{K}} : \mathcal{K} \to \mathrm{Th}(\mu^{\mathcal{K}})$. Since we can view Definition 5.1 as lying in the $\infty$-category of locally presentable $\infty$-categories and accessible functors ([15, Definition 5.5.3.1]) the operation of taking adjoints is functorial in $\mathcal{K}$ ([15, Corollary 5.5.3.4]).

Essentially surjective functors and faithful functors form an orthogonal factorization system on $\mathbf{Cat}_{\infty}$ (see Lemma 5.4). Thus, the operation of taking essential image is functorial by [15, Lemma 5.2.8.19], so $\eta_{\mathcal{K}}$ is natural in $\mathcal{K}$. This will be the unit of our adjunction.

**Construction 5.7.** We have a diagram natural in $M$

![img-0.jpeg](img-0.jpeg)

The Yoneda functoriality described in Proposition 4.9 gives us the naturality of the outer square, and the inner square is just Definition 5.1. $\epsilon_M'$ comes from the universal property of pullback and is hence (contravariantly) natural in $M$. Through the contravariant equivalence of Theorem 3.22 this corresponds to a natural transformation $\epsilon_M : \mu^{\mathrm{Th}(M)} \to M$, which will be the counit our the monad-theory adjunction.

**Lemma 5.8.** $\eta \circ \mathrm{Th}$ and $\mathrm{Th} \circ \epsilon$ are both natural equivalences.

*Proof.* By Lemma 2.1 to show that $\eta \circ \mathrm{Th}$ and $\mathrm{Th} \circ \epsilon$ are natural equivalences, it suffices to show that for each monad $M$, the functors $\eta_{\mathrm{Th}(M)}$ and $\mathrm{Th}(\epsilon_M)$ are equivalences. We will first show that $\eta_{\mathrm{Th}(M)} \circ \mathrm{Th}(\epsilon_M)$ is an equivalence. Then we will show that each $\eta_{\mathrm{Th}(M)}$ is an equivalence, from which the required results will follow.

Given a pretheory $\mathcal{K}$, we write $G_{\mathcal{K}} : \mathcal{E}^{\mu^{\mathcal{K}}} \to \mathrm{Pr}(\mathcal{K})$ for the top horizontal map in the pullback of Definition 5.1. We write $Y_M : \mathcal{E}^M \to \mathrm{Pr}(\mathrm{Th}(M))$ for the restricted Yoneda embedding. $Y_M$ restricts to an equivalence $S : \mathrm{Th}(M) \simeq im(y_{\mathrm{Th}(M)})$, and the homotopy inverse $\Psi : im(y_{\mathrm{Th}(M)}) \to \mathrm{Th}(M)$

34

of $S$ is partial left adjoint of the map $Y_M$. Consider the commutative diagram (which is part of the diagram (5)):

![img-1.jpeg](img-1.jpeg)

As noted in Proposition 5.2 $G_{\mathrm{Th}(M)}$ is a fully faithful right adjoint. We write $(G_{\mathrm{Th}(M)})^L$ for its left adjoint. By the functoriality of taking partial left adjoints established in Section 4 we have that $\mathrm{Th}(\epsilon_M) \circ (G_{\mathrm{Th}(M)})^L|_{im(y_{\mathrm{Th}(M)})} \simeq \Psi$ (note that $\mathrm{Th}(\epsilon_M)$ is a partial left adjoint to $\epsilon_M'$ by construction). Let $\psi'\psi$ be the factorization of $y_{\mathrm{Th}(M)}$ through its essential image. Since $y_{\mathrm{Th}(M)}$ is fully faithful, $\psi$ is an equivalence. We have that $\eta_{\mathrm{Th}(M)} = (G_{\mathrm{Th}(M)})^L|_{im(y_{\mathrm{Th}(M)})} \circ \psi$. Thus, $\Psi \circ \psi = \mathrm{Th}(\epsilon_M) \circ \eta_{\mathrm{Th}(M)}$ is an equivalence.

We want to show now that $\eta_{\mathrm{Th}(M)}$ is an equivalence. It is essentially surjective by construction. We want to show that it induces a bijection on homotopy groups of mapping spaces. It induces a monomorphism of homotopy groups of mapping spaces since it has a left inverse.

As noted in Proposition 5.2 $G_{\mathrm{Th}(M)}$ is fully faithful, so we have $G_{\mathrm{Th}(M)}^L \circ G_{\mathrm{Th}(M)} \simeq id$. $G_{\mathrm{Th}(M)}^L$ induces a surjection on homotopy groups for each mapping spaces between objects in the image of $G_{\mathrm{Th}(M)}$. The essential image of the restricted Yoneda embedding in (5) contains the essential image of $y_{\mathrm{Th}(M)}$, so the image of $G_{\mathrm{Th}(M)}$ contains $im(y_{\mathrm{Th}(M)})$ by the commutativity of (5). Thus $G_{\mathrm{Th}(M)}^L|_{im(y_M)}$ induces surjections on homotopy groups of mapping spaces. $\eta_{\mathrm{Th}(M)} = G_{\mathrm{Th}(M)}^L|_{im(y_M)} \circ y_{\mathrm{Th}(M)}$. Thus, we conclude that $\eta_{\mathrm{Th}(M)}$ induces bijections on homotopy groups of mapping spaces as well.

**Theorem 5.9.** $\mu^{(-)} : \mathbf{PreTh}_A \rightleftarrows \mathbf{Mnd}_E : \mathbf{Th}$ is an idempotent adjunction, with unit $\eta$.

*Proof.* By Lemma 5.8 and Lemma 2.2, it remains to verify that $\epsilon, \eta$ satisfy the second of the triangle identities, i.e. that for all $A$-pretheory $\mathcal{K}$, the morphism of monads $\epsilon_{\mu^\mathcal{K}} \circ \mu^{\eta^\mathcal{K}}$ is an equivalence. As these are morphisms of monads, we will work through the equivalence of Theorem 3.22 and instead show the induced functor between $\infty$-categories of algebras is an equivalence.

35

We have a commutative diagram, functorial in $\mathcal{K}$

![img-2.jpeg](img-2.jpeg)

where $Y_{\mu^{\mathcal{K}}}$ is the restricted Yoneda embedding. We want to show that the composite of two left vertical functors is an equivalence. The composite of the functor $\operatorname{Pr}(\eta_{\mathcal{K}}) \circ Y_{\mu^{\mathcal{K}}}$ is given by

$$x \mapsto (y \mapsto \operatorname{Map}_{\operatorname{Pr}(\mathcal{K})}(G_{\mathcal{K}}^{L} \circ y_{\mathcal{K}}(y), x)),$$

where $y_{\mathcal{K}}$ is the Yoneda embedding. This is naturally equivalent to the functor

$$\mathcal{E}^{\mu^{\mathcal{K}}} \to \operatorname{Pr}(\mathcal{K}), x \mapsto (y \mapsto \operatorname{Map}_{\operatorname{Pr}(\mathcal{K})}(y_{\mathcal{K}}(y), G_{\mathcal{K}}(x)))$$

which is equivalent to $G_{\mathcal{K}}$, by the $\infty$-categorical Yoneda Lemma (see [15, Proposition 5.5.2.1], or rather [6, Theorem 5.8.13.(ii)] as we need the equivalence to be functorial).

Thus, we have that $G_{\mathcal{K}} \circ (\mathcal{E}^{\eta_{\mathcal{K}}})^{op} \circ \epsilon_{\operatorname{Th}(M)}^{op} \simeq G_{\mathcal{K}}$. Since $G_{\mathcal{K}}$ is fully faithful, and thus an equivalence onto its essential image, we conclude that $(\mathcal{E}^{\eta_{\mathcal{K}}})^{op} \circ \epsilon_{\operatorname{Th}(M)}^{op}$ is an equivalence by 2 out of 3.

Remark 5.10. Note that there is nothing asymmetric between $\eta$ and $\epsilon$ and we have also proved that $\epsilon$ is a counit of adjunction. We just have not showed any coherence conditions between this counit $\epsilon$ and the unit $\eta$.

Definition 5.11. A monad $M$ on $\mathcal{E}$ is said to be $\mathcal{A}$-nervous if $\epsilon_{M}$ is an equivalence, i.e. if the square

![img-3.jpeg](img-3.jpeg)

36

is a pullback square. An $\mathcal{A}$-pretheory $\mathcal{K}$ is said to be an $\mathcal{A}$-theory if $\eta_{\mathcal{K}}$ is an equivalence.

The following then immediately follows from Theorem 5.9 and Remark 2.4:

**Corollary 5.12.** *For any monad $M$, $\mathrm{Th}(M)$ is an $\mathcal{A}$-theory, and for any $\mathcal{A}$-pretheory $\mathcal{K}$, the associated monad $\mu^{\mathcal{K}}$ is $\mathcal{A}$-nervous. Moreover, the monad-theory adjunction restricts to an equivalence between the full subcategories of $\mathcal{A}$-Nervous monads and $\mathcal{A}$-theories.*

## 6 General consequences of the Monad-Theories adjunction

In this section we draw general consequences from the monad-theory adjunction of Theorem 5.9. First, one can use it to construct and study colimits of $\mathcal{A}$-Nervous monads:

**Theorem 6.1.** *Let $\mathcal{E}$ be a presentable $\infty$-category, and let $\mathcal{A} \subset \mathcal{E}$ be a full dense small subcategory. Then the full subcategory of $\mathrm{Mnd}_{\mathcal{E}}$ of $\mathcal{A}$-Nervous monads has all colimits and they are preserved by the inclusion in $\mathrm{Mnd}_{\mathcal{E}}$. Moreover, the contravariant functor sending a monad to its category of algebras preserves these colimits. That is, the natural map:*

$$\mathcal{E}^{\mathrm{Colim}\,M_i} \to \lim_{i \in I} \mathcal{E}^{M_i}$$

*is an equivalence.*

*Proof.* The $\infty$-category of $\mathcal{A}$-pretheories is just the full subcategory of $(\mathrm{Cat}_{\infty})_{\mathcal{A}/}$ of essentially surjective functors, so it has all colimits and they are computed in $(\mathrm{Cat}_{\infty})_{\mathcal{A}/}$. This can be used to compute colimits of $\mathcal{A}$-nervous monads. Indeed, if $(M_i)_{i \in I}$ is a diagram of $\mathcal{A}$-nervous monads, then it induces a diagram $(T_i)_{i \in I}$ of $\mathcal{A}$-theories. The colimit $\mathrm{Colim}\,T_i$ in the $\infty$-category of $\mathcal{A}$-pretheories exists, is preserved by the left adjoint of the monad-theory correspondence and is thus taken by this left adjoint to a colimit of the diagram $(M_i)_{i \in I}$.

The claim about categories of algebras actually holds for general colimits of monads (when they exist) as one can show that every object admits an

37

endomorphism monad and one can use the universal property of the colimits for maps to endomorphism monads. Alternatively, one can also use the description of colimits given above: given that the associated monad functor sends each theory $T$ to a monad $\mu^T$ such that $T$-models get identified functorially with $\mu^T$-algebras, it is enough to check that the (contravariant) functor sending each pretheory to its category of models send colimits to limits. But this follows immediately from the fact that $\mathcal{C} \mapsto \Pr(\mathcal{C}) \simeq \operatorname{Fun}(\mathcal{C}^{op}, \mathcal{S})$ send colimits to limits. $\square$

To make this useful, one needs to provide a large supply of nervous monads. The next step is 6.4 that essentially claims that all accessible monads are nervous monads.

Following [2], one defines:

**Definition 6.2.** Let $\mathcal{A} \subset \mathcal{E}$ be a full subcategory. Let $M$ be a monad on $\mathcal{E}$. One says that $M$ is a *monad with arities in $\mathcal{A}$* if for each $X \in \mathcal{E}$, the canonical colimit

$$X \simeq \operatorname{Colim}_{a \in \mathcal{A}/X} a$$

is preserved the composite

$$\mathcal{E} \xrightarrow{M} \mathcal{E} \xrightarrow{i} \Pr(\mathcal{A}),$$

where $i$ denotes the (fully faithful) restricted Yoneda embeddings.

As in the 1-categorical case, we will show that all monads with arities in $\mathcal{A}$ are in fact $\mathcal{A}$-nervous. The proof follows essentially the same strategy as in [2]. Note that the converse is not true, it is shown in [4] that the free groupoid monad on the category of graphs is an example of a $\mathcal{A}$-nervous monad which is not a monad with arities in $\mathcal{A}$, for $\mathcal{A}$ the full subcategory of linear graphs.

**Theorem 6.3.** *Suppose that we have a commutative square of $\infty$-categories*

$$\begin{array}{c} U \xrightarrow{\Phi} V \\ R_1 \downarrow \quad \downarrow R_2 \\ A \xrightarrow{\Psi} B \end{array}$$

*where:*

38

- $\Psi$ is fully faithful,
- $R_1, R_2$ are monadic right adjoint functors, with left adjoint $L_1$ and $L_2$,
- the natural transformation $L_2\Psi \to \Phi L_1$ obtains from these adjunction is invertible.

Then the square is a pullback of $\infty$-categories.

Proof. We form the pullback:

![img-4.jpeg](img-4.jpeg)

We will show that $t$ is an equivalence using Lemma 3.25. That is we will show that $R'_2$ is a monadic right adjoint functor and that the natural transformation $L'_2 \to tL_1$ is an equivalence of categories.

$\Psi$, and hence its pullback $\Psi'$ are both fully faithful, so up to equivalences of categories, one can freely assume that $W$ and $A$ are full subcategories of $V$ and $B$. In this case, $R'_2$ is just the restriction of $R_2$ to a functor $W \to A$. The isomorphisms $L_2\Psi \simeq \Phi L_1$ show that if $X \in A$ then $L_2X \in W$, which immediately implies that $L_2$ corestricted to a functor $A \to W$ is a left adjoint to $R'_2$. Hence, by Proposition 3.23, $R'_2$ is indeed a monadic functor. Now, again as we are simply restricting to full subcategories, the natural transformation $L'_2 \to tL_1$ is exactly the same as $L_2\Psi \to \Phi L_1$ and hence is invertible.

**Theorem 6.4.** Given $\mathcal{E}$ a presentable $\infty$-category and $\mathcal{A} \subset \mathcal{E}$ a full dense small subcategory, then any monad $M$ with arities in $\mathcal{A}$ is $\mathcal{A}$-nervous.

Proof. For any monad $M \in \mathbf{Mnd}_{\mathcal{E}}$ we have a commutative square of $\infty$-categories:

![img-5.jpeg](img-5.jpeg)

39

and $M$ is $\mathcal{A}$-nervous if and only if this square is a pullback. We conclude by applying Theorem 6.3 to it. Both vertical functors are monadic right adjoint functors (for the right one, it was observed in the proof of Proposition 5.2). The functor $\mathcal{E} \rightarrow \Pr(\mathcal{A})$ is the restricted Yoneda embeddings and is fully faithful because $\mathcal{A}$ is dense in $\mathcal{E}$. On the left hand side the left adjoint is the free algebra functor, and the right hand side it is the left Kan extension of the canonical functor $\mathcal{A} \rightarrow \mathrm{Th}_{\mathcal{A}}(M)$. The natural transformation “$L_2\Psi \rightarrow \Phi L_1$” in the notation of Theorem 6.3 corresponds exactly to the map

$$\mathrm{Colim}_{\mathcal{A}/X} M(a) \rightarrow M(X)$$

where the colimit is taken in $\Pr(\mathrm{Th}_{\mathcal{A}}(M))$. This map is an equivalence if and only if its image in $\Pr(\mathcal{A})$ is an equivalence and this corresponds exactly to the definition of a monad with arities in $\mathcal{A}$. $\square$

**Definition 6.5.** Let $\lambda$ be a regular cardinal. We say that a monad on a $\lambda$-accessible $\infty$-category $C$ is $\lambda$-accessible if its underlying functor is $\lambda$-accessible in the sense of [15, 5.4.2.5]. That is, if it preserves $\lambda$-directed colimits.

**Lemma 6.6.** *Let $T$ be a monad on an $\infty$-category $\mathcal{C}$ whose underlying functor commutes to colimits of $I$-shaped diagrams. Let $(C_i)_{i \in I}$ be an $I$-shaped diagram in $\mathcal{C}^T$, then:*

- *A cocone for $C_i$ in $\mathcal{C}^T$ is a colimit cocone if and only if its image under the forgetful functor is a colimit cocone in $\mathcal{C}$.*
- *If the image under the forgetful functor of $(C_i)$ admits a colimit in $\mathcal{C}$, then the colimit diagram can be lifted into a colimit diagram in $\mathcal{C}^T$.*

*Proof.* Let $\mathrm{End}_I(\mathcal{C}) \subset \mathrm{End}(\mathcal{C})$ be the full subcategory of endofunctors preserving $I$-shaped colimits. As $\mathrm{End}_I(\mathcal{C})$ is stable under composition it is a monoidal subcategory of $\mathrm{End}(\mathcal{C})$ in the sense of section 2.2.1 of [16], and hence it is itself a monoidal $\infty$-category. A monad preserving $I$-shaped colimits can be seen as a monoid object for this subcategory. As $\mathcal{C}$ is also tensored over $\mathrm{End}_I(\mathcal{C})$, applying [16, Corollary 4.2.3.5] to $\mathcal{C} = \mathrm{End}_I(\mathcal{C})$ immediately gives the result claimed. $\square$

40

**Theorem 6.7.** *Let $\mathcal{E}$ be a $\lambda$-presentable category and let $\mathcal{A}$ be the full subcategory of $\lambda$-presentable objects. Then for a monad $M \in \mathbf{Mnd}_{\mathcal{E}}$ the following conditions are equivalent:*

1. $M$ is $\lambda$-accessible.
2. $M$ has arities in $\mathcal{A}$.
3. $M$ is $\mathcal{A}$-nervous.

*Proof.* $1 \Rightarrow 2$: If $M$ is $\lambda$-accessible then $M$ preserves all $\lambda$-directed colimits. Because all objects in $\mathcal{A}$ are $\lambda$-compact, the restricted Yoneda embedding $\mathcal{E} \rightarrow \Pr(\mathcal{A})$ preserves $\lambda$-directed colimits. Since for each $X \in \mathcal{E}$ the category $X_{/\mathcal{A}}$ is $\lambda$-directed (it has $\lambda$-small colimits) this concludes the proof.

$2 \Rightarrow 3$ is Theorem 6.4.

$3 \Rightarrow 1$: $M$ being $\mathcal{A}$-nervous means that the square:

$$\begin{array}{ccc} \mathcal{E}^M & \longrightarrow & \Pr(\text{Th}_{\mathcal{A}}(M)) \\ \downarrow & & \downarrow \\ \mathcal{E} & \longrightarrow & \Pr(\mathcal{A}) \end{array}$$

is a pullback square. Now the right vertical functor preserves all colimits (in particular, $\lambda$-directed ones), and the bottom horizontal functor preserves $\lambda$-directed colimits as mentioned above. It hence follows that all functors in the diagram preserve $\lambda$-directed colimits by 3.24. The underlying functor of the monad $M$ identifies with the composite of the forgetful functor $\mathcal{E}^M \rightarrow \mathcal{E}$ and its left adjoint (which automatically preserves colimits), so it preserves $\lambda$-directed colimits. Thus, $M$ is $\lambda$-accessible. $\square$

**Corollary 6.8.** *Let $M$ be a $\lambda$-accessible monad on a $\lambda$-presentable $\infty$-category $\mathcal{E}$. Then the $\infty$-category $\mathcal{E}^M$ of $M$-algebra is locally presentable. In particular it has all colimits.*

*Proof.* With $\mathcal{A}$ the full subcategory of $\lambda$-presentable objects, we have by Theorem 6.7 pullback diagram:

$$\begin{array}{ccc} \mathcal{E}^M & \longrightarrow & \Pr(\text{Th}_{\mathcal{A}}(M)) \\ \downarrow & & \downarrow \\ \mathcal{E} & \longrightarrow & \Pr(\mathcal{A}) \end{array}$$

41

$\Pr(M^\lambda), \Pr(C^\lambda)$ are locally presentable by [15, Theorem 5.5.1.1]. The vertical right map preserve all limits and all colimits so it is an accessible right adjoint functor and the bottom horizontal map preserves all limits and $\lambda$-directed colimits, so it is also an accessible right adjoint. It then follows from [15, Theorem 5.5.3.18] that taking this pullback in the category of presentable categories and right adjoint functors between them gives the same results, and hence $\mathcal{E}^M$ is itself locally presentable. $\square$

**Corollary 6.9.** *Let $\mathcal{E}$ be a locally presentable category and $M: I \rightarrow \mathbf{Mnd}_{\mathcal{E}}$ a diagram such that $M(i)$ is accessible for each $i \in I$, then $M$ has a colimit in $\mathbf{Mnd}_{\mathcal{E}}$ and the natural map:*

$$\mathcal{E}^{\text{Colim } M_i} \rightarrow \lim_{i \in I} \mathcal{E}^{M_i}$$

*is an equivalence of $\infty$-categories.*

More precisely, the proof will show that if $\mathcal{E}$ is $\kappa$-presentable and all $M(i)$ are $\kappa$-accessible then the colimit is $\kappa$-accessible.

*Proof.* Given $\kappa$ a regular cardinal such that $\mathcal{E}$ is $\kappa$-presentable and all $M(i)$ are $\kappa$-accessible, Theorem 6.7 shows that all $M(i)$ are $\mathcal{A}$-nervous for $\mathcal{A}$ the category of $\kappa$-compact objects in $\mathcal{A}$, and Theorem 6.3 implies the result. $\square$

## 7 Monads as Kleisli categories

The goal of this section is to show that one can works with a monad purely in terms of its Kleisli category, so that defining a monad on $\mathcal{C}$ is the same as defining a bijective on objects left adjoint functor $\mathcal{C} \rightarrow \mathcal{K}$. This section is generally independent of the rest of the paper, but uses very similar methods and fits in the general goal of providing tools to work more easily with monads on $\infty$-categories.

**Definition 7.1.** Let $\mathbf{LAdj}_{\mathcal{C}}$ be the full subcategory of $(\mathbf{Cat}_{\infty})_{\mathcal{C}/}$ on *left adjoint essentially surjective functors*.

Let $\text{Kl}: \mathbf{Mnd}_{\mathcal{C}} \rightarrow \mathbf{LAdj}_{\mathcal{C}}$ be the Kleisli category construction. The main result of this section is:

**Theorem 7.2.** *The functor $\text{Kl}$ is an equivalence of $\infty$-categories between the $\infty$-categories $\mathbf{Mnd}_{\mathcal{C}}$ and $\mathbf{LAdj}_{\mathcal{C}}$.*

42

As well, the following proposition allows us to recover the $\infty$-category of algebras of a monad out of its Kleisli categories.

**Proposition 7.3.** *Let $\mathcal{C}^M \to \mathcal{C}$ be a monadic functor The square*

$$\begin{array}{ccc} \mathcal{C}^M & \longrightarrow & \operatorname{Pr}(\mathcal{C}_M) \\ \downarrow & & \downarrow \\ \mathcal{C} & \longrightarrow & \operatorname{Pr}(\mathcal{C}) \end{array}$$

*where the horizontal arrows are the restricted Yoneda embeddings is a pullback.*

*Proof.* In the diagram, the vertical maps are monadic, and the bottom horizontal map is fully faithful. By 6.3, we must show that the adjoint natural transformation (“$L_2\Psi \to \Phi L_1$” in the notation of 6.3) is an equivalence. But this was done within the proof of Proposition 4.9, when checking that Proposition 4.8 can be applied. $\square$

A key observation is that the pullback of Proposition 7.3 allows us to associate a monad on $\mathcal{C}$ to every essentially surjective left adjoint functor $L : \mathcal{C} \to \mathcal{K}$.

**Lemma 7.4.** *Let $F : \mathcal{C} \to \mathcal{K}$ be an essentially surjective left adjoint functor, then, in the pullback square:*

$$\begin{array}{ccc} \mathcal{M} & \longrightarrow & \operatorname{Pr}(\mathcal{K}) \\ \downarrow & \downarrow^\perp & \downarrow \\ \mathcal{C} & \longrightarrow & \operatorname{Pr}(\mathcal{C}) \end{array}$$

*The functor $\mathcal{M} \to \mathcal{C}$ is a monadic right adjoint.*

*Proof.* The proof is the same as in Proposition 5.2 except for the part about the existence of a left adjoint functor $\mathcal{C} \to \mathcal{M}$ (which in Proposition 5.2 follows from a presentability argument). Because $F : \mathcal{C} \to \mathcal{K}$ has a right adjoint $R$, the restriction functor $F^* : \operatorname{Pr}(\mathcal{K}) \to \operatorname{Pr}(\mathcal{C})$ sends the representable at $X \in \mathcal{K}$ to the representable at $R(X) \in \mathcal{C}$, and (as for any functor $F$), its left adjoint functor $F_! : \operatorname{Pr}(\mathcal{C}) \to \operatorname{Pr}(\mathcal{K})$ sends representables to representables. It follows that, as $\mathcal{C}$ and $\mathcal{M}$ are respectively full subcategories of $\operatorname{Pr}(\mathcal{C})$ and $\operatorname{Pr}(\mathcal{K})$ preserved by the action of $F^*$ and $F_!$, the restriction of $F_!$ to a functor $\mathcal{C} \to \mathcal{M}$ is a left adjoint to the restriction of $F^* : \mathcal{M} \to \mathcal{C}$. $\square$

43

**Construction 7.5.** Lemma 7.4 allows us to construct a functor $\Omega : \mathbf{L}\mathbf{Adj} \rightarrow \mathbf{M}\mathbf{nd}_{\mathcal{C}}$, or more precisely, a functor $\mathbf{L}\mathbf{Adj}^{op} \rightarrow \mathbf{R}\mathbf{M}\mathbf{d}_{\mathcal{C}}$. The construction that sends an essentially surjective left adjoint functor $F : \mathcal{C} \rightarrow \mathcal{K}$ to the pullback $\mathcal{M} \rightarrow \mathcal{C}$ as in Lemma 7.4 is a contravariant functor: The presheaf construction (with its contravariant functoriality) defines a functor $((\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{\setminus \mathcal{C}})^{op} \rightarrow (\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{/\Pr(\mathcal{C})}$ (up to some easily dealt with size issues) which can be composed with the pullback functor $(\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{/\Pr(\mathcal{C})} \rightarrow (\mathbf{C}\mathbf{a}\mathbf{t}_{\infty})_{/\mathcal{C}}$. Finally Lemma 7.4 shows that this functors sends the full subcategory $\mathbf{L}\mathbf{Adj}_{\mathcal{C}}$ to $\mathbf{R}\mathbf{M}\mathbf{d}_{\mathcal{C}}$.

We conclude the proof of Theorem 7.2, with:

**Proposition 7.6.** *The functor $\Omega : \mathbf{L}\mathbf{Adj}_{\mathcal{C}} \rightarrow \mathbf{M}\mathbf{nd}_{\mathcal{C}}$ of Construction 7.5 is an inverse for $\mathrm{Kl} : \mathbf{M}\mathbf{nd}_{\mathcal{C}} \rightarrow \mathbf{L}\mathbf{Adj}$.*

*Proof.* We will construct two explicit natural isomorphisms $\Omega \circ \mathrm{Kl}(M) \rightarrow M$ and $\mathrm{Kl} \circ \Omega(\mathcal{K}) \rightarrow \mathcal{K}$.

By Corollary 4.10 the restricted Yoneda embedding $\mathcal{C}^M \rightarrow \Pr(\mathcal{C}_M)$ is natural in $M$. Given the pullback defining the category of algebras of $\Omega(\mathcal{C}_M)$ this translated into a map, natural in $M$, from $\mathcal{C}^M$ to that category of algebras, which by Proposition 7.3 is an equivalence. Though the equivalence of Theorem 3.22, this translate to a isomorphism of monads $M \rightarrow \Omega \circ \mathrm{Kl}(M)$.

Given $F : \mathcal{C} \rightarrow \mathcal{K}$ in $\mathbf{L}\mathbf{Adj}$, recall that the category of algebras $\mathcal{C}^{\Omega(F)}$ is constructed (functorially) as the pullback:

$$\begin{array}{ccc} \mathcal{C}^{\Omega(F)} & \longrightarrow & \Pr \mathcal{K} \\ \downarrow & & \downarrow_{F^*} \\ \mathcal{C} & \longrightarrow & \Pr \mathcal{C} \end{array}$$

Its Kleisli category is the essentially image of the left adjoint of $\mathcal{C}^{\Omega(F)} \rightarrow \mathcal{C}$ and it is made functorial by Proposition 4.5. It hence follows from Proposition 4.8 (that the assumption are satisfied follows from the proof of Lemma 7.4) that we have a natural transformation $\mathcal{C}_{\Omega(F)} \rightarrow \Pr \mathcal{K}$ where $\Pr$ has its covariant/left adjoint functoriality$^4$. Now the explicit construction of the left adjoint to $\mathcal{C}^{\Omega(F)} \rightarrow \mathcal{C}$ done in the proof of Lemma 7.4 shows that the functor $\mathcal{C}_{\Omega(F)} \rightarrow \Pr \mathcal{K}$ induces an equivalence between $\mathcal{C}_{\Omega(F)}$ and the full subcategory

$^4$We refer again to section 6 of [12] for the fact that the two possible definition of this covariant functoriality are equivalent.

44

of $\Pr \mathcal{K}$ of representable presheaves (which is essentially $\mathcal{K}$). As the Yoneda embedding of $\mathcal{K}$ into $\Pr \mathcal{K}$ is natural for this left adjoint/covariant functoriality of $\Pr$ (again by section 6 of [12]), this boils down to a natural equivalence (under $\mathcal{C}$) $\mathcal{C}_{\Omega(F)} \simeq \mathcal{K}$ which concludes the proof. $\square$

## 8 $E_1$, $E_2$ and $E_\infty$-algebras

In this section we show that the monads on the $\infty$-category $\mathcal{S}$ of spaces corresponding to the $E_1$, $E_2$ and $E_\infty$-operads can be seen respectively as 'induced' the free monoid monad on Set, the free braided monoid on groupoids and the free symmetric monoid on groupoids. By induced here we mean that when restricted to appropriate category of arities they corresponds to the same theories.

It should be noted that the $E_2$ and $E_\infty$ operads cannot be described by the framework of planar operads that we recalled in Section 3. It needs the more general 'symmetric' operads framework. We will not recall the details of this and we refer directly to [16]. However, to fix notation, we note that, similarly to how a planar operad is encoded by a map $\mathcal{O}^\otimes \to N(\Delta^{op})$, a symmetric operad is encoded by a map $\mathcal{O}^\otimes \to N(\mathrm{Fin}_*)$ of $\infty$-categories, where $\mathrm{Fin}_*$ is the category of finite pointed sets.

We first recall some basic facts about sifted diagrams:

**Definition 8.1.** An $\infty$-category $K$ is said to be *sifted* if the diagonal map $K \to K \times K$ is cofinal.

*Remark 8.2.* Note that the property of being sifted is invariant under equivalence of $\infty$-categories (see [15, Corollary 4.1.1.10]).

**Lemma 8.3.** *Suppose that $K$ is an $\infty$-category that has finite coproducts. Then $K$ is sifted.*

*Proof.* By [16, 4.1.3.1], it suffices to show that for all $a, b \in K$, $K \times_{K \times K} (K \times K)_{(a,b)/} \cong K_{b/} \times_K K_{a/} \cong K_{\{a,b\}/}$ is weakly contractible. But this $\infty$-category is weakly contractible since it has an initial object, the coproduct of $a, b$. $\square$

We say that an $\infty$-operad $\mathcal{O}^\otimes$ is a *non-colored $\infty$-operad* if its underlying $\infty$-category is terminal, i.e. if $\mathcal{O} \cong \Delta^0$ (see [16, Example 2.1.1.6]). When $\mathcal{O}$ is a non-colored $\infty$-operad, we have a forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{B}) \to \mathcal{B}$ for

45

any symmetric monoidal $\infty$-category $\mathcal{B}$ (or more generally any $\mathcal{O}$-monoidal $\infty$-category).

The goal of the next few paragraphs is to show that given a non-colored $\infty$-operad $\mathcal{O}^\otimes$, then the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{B}) \rightarrow \mathcal{B}$ where $\mathcal{B}$ is one of the (cartesian) symmetric monoidal $\infty$-categories Set, Gdp or $\mathcal{S}$, is monadic and the associated monad is Fin-nervous, where $\mathrm{Fin} \subset \mathcal{B}$ is the full subcategory of finite sets.

Recall that the $\infty$-category of spaces $\mathcal{S}$, as well as its full subcategory Set and Gpd of sets (i.e. discrete spaces) and groupoids (i.e. 1-truncated spaces), are cartesian closed locally presentable $\infty$-categories. In particular Lemma 8.4 and Lemma 8.5 below can be applied to them.

**Lemma 8.4.** *Let $\mathcal{O}^\otimes$ be a non-colored $\infty$-operad and $\mathcal{C}$ a locally presentable cartesian closed symmetric monoidal $\infty$-category.*

*Then $\infty$-category $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{S})$ has all sifted colimits and the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{C}) \rightarrow \mathrm{Fun}(\mathcal{O}, \mathcal{C}) \simeq \mathcal{C}$ preserves sifted colimits.*

*Proof.* For the first statement [16, Proposition 3.2.3.1] implies that it suffices to show that for $n \in \mathbb{N}$, the induced map $\mathcal{C}_{[n]}^\otimes \rightarrow \mathcal{C}_{[1]}^\otimes$ (see [16, Remark 2.1.2.6]), preserves sifted colimits separately in each variable. Because $\mathcal{C}$ is cartesian, this functor can be identified with the functor $\mathcal{C}^n \rightarrow \mathcal{C}$ that takes a collection of objects to their n-fold product. But since $\mathcal{C}$, is cartesian closed, products preserve sifted colimits separately in each variable, hence the result.

The fact that the forgetful functor preserves all sifted colimits follows from another application of [16, Proposition 3.2.3.1].

□

The left adjoint of the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{C}) \rightarrow \mathcal{C}$ (if it exists) is called the *free $\mathcal{O}$-algebra functor* and is denoted $\mathrm{Free}_{\mathcal{O}}^\mathcal{C}$.

**Lemma 8.5.** *Let $\mathcal{O}^\otimes$ and $\mathcal{C}$ as in Lemma 8.4. Then the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{C}) \rightarrow \mathcal{C}$ is a monadic right adjoint functor.*

*Proof.* We verify the three hypotheses of Barr-Beck-Lurie. Since colimits in $\mathcal{C}$ are preserved by the products and $\mathcal{C}$ is presentable, it follows from [16, Example 3.1.3.6] and Lemma 8.4 that the functor is a right adjoint. Since $N(\Delta^{\mathrm{op}})$ is sifted ([15, Lemma 5.5.8.3]), 8.4 implies that it preserves colimits of split simplicial objects. The functor reflects limits ([16, Corollary 3.2.2.5]) and hence reflects equivalences; the limit of a diagram $X : \Delta^0 \rightarrow \mathcal{C}$ is just an object equivalent to $X$.

□

46

**Lemma 8.6.** *For each $s \in \mathcal{S}$, the category $\mathrm{Fin}_{/s}$ is sifted.*

*Proof.* Coproducts in $\mathcal{S}_{/s}$ are computed as coproducts in $\mathcal{S}$, in particular $\mathrm{Fin}_{/s}$, seen as a full subcategory of $\mathcal{S}_{/s}$ is closed under finite coproducts because Fin is closed under finite coproducts in $\mathcal{S}$. The result then follows from Lemma 8.3. $\square$

**Theorem 8.7.** *Suppose that $\mathcal{B} = \mathcal{S}$, Gdp or Set. Let $\mathcal{O}^{\otimes}$ be a non-colored $\infty$-operad. Then the monad on $\mathcal{B}$ corresponding the forgetful functor $\mathrm{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}) \rightarrow \mathcal{B}$ is Fin-nervous.*

*Proof.* We will show more precisely that this monad, which we denote $M$, has arities in Fin, in the sense of Definition 6.2, which implies the result by 6.4. It suffices to show that the functor

$$\mathcal{B} \xrightarrow{M} \mathcal{B} \xrightarrow{i} \mathrm{Pr}(\mathrm{Fin})$$

preserves $\mathrm{colim}_{a \in \mathrm{Fin}/X}(a)$ for each $X \in \mathcal{B}$. By 8.6, it suffices to show that $M$ and $i$ preserve sifted colimits. The monad $M$ is the composite of the left adjoint $\mathrm{Free}_{\mathcal{O}}^{\mathcal{B}}$, which preserves all colimits, and the forgetful functor $\mathrm{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}) \rightarrow \mathcal{B}$ which preserves sifted colimits by Lemma 8.4. Hence $M$ preserves sifted colimits.

It suffices to show that the restricted Yoneda embedding $i$ preserves sifted colimits. Since colimits in $\mathrm{Pr}(\mathcal{A})$ are calculated pointwise, it suffices to show that for each $K \in \mathrm{Fin}$ and sifted $\infty$-category I, the natural map

$$\mathrm{colim}_{i \in I} \mathrm{Map}_{\mathcal{S}}(K, a_i) \rightarrow \mathrm{Map}_{\mathcal{S}}(K, \mathrm{colim}_{i \in I} a_i)$$

is an equivalence. This can be identified with the map

$$\prod_{j \in K} (\mathrm{colim}_{i \in I} a_i) \rightarrow \mathrm{colim}_{i \in I} \prod_{j \in K} a_i$$

In other words, we want to show that sifted colimits preserve finite products in $\mathcal{B}$, which follows from $\mathcal{B}$ being cartesian closed and [15, Proposition 5.5.8.6 and Lemma 5.5.8.11]. $\square$

**Lemma 8.8.** *Suppose that $G : \mathcal{C} \rightarrow \mathcal{D}$ is a fully faithful functor of $\infty$-categories, and $\mathcal{E}$ be an $\infty$-category. Then $\mathrm{Fun}(\mathcal{E}, \mathcal{C}) \rightarrow \mathrm{Fun}(\mathcal{E}, \mathcal{D})$ is fully faithful.*

47

*Proof.* Up to equivalence of $\infty$-categories, one can assume that $\mathcal{C}$ is a full subcategory of $\mathcal{D}$, in which case $\operatorname{Fun}(\mathcal{E}, \mathcal{C})$ is isomorphic (as a simplicial) set to the full subcategory of $\operatorname{Fun}(\mathcal{E}, \mathcal{D})$ of functors that sends all objects of $\mathcal{E}$ to $\mathcal{D}$.

Suppose that $\mathcal{B} \subseteq \mathcal{S}$ is either Set, Gpd. We write $\mu_{\mathcal{B}}^{(-)} \dashv \operatorname{Th}_{\mathcal{B}}$ for the adjunction of 5.9 coming from the inclusion of arities $\operatorname{Fin} \subseteq \mathcal{B}$.

**Theorem 8.9.** *Let $\mathcal{B} \subsetneq \mathcal{S}$ be as above. Let $\mathcal{O}^{\otimes}$ be a non-colored $\infty$-operad. Suppose that the free algebra functor $\mathcal{S} \rightarrow \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{S})$ takes elements of $\mathcal{B}$ to $\operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B})$. Then there exists a theory $(\operatorname{Fin} \rightarrow \mathcal{K}) \in \mathbf{PreTh}_{\operatorname{Fin}}$, so that*

$$\mathcal{S}^{\mu_{\mathcal{S}}^{\mathcal{K}}} \simeq \operatorname{Mod}_{\mathcal{K}}(\mathcal{S}) \simeq \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{S}) \qquad \mathcal{B}^{\mu_{\mathcal{B}}^{\mathcal{K}}} \simeq \operatorname{Mod}_{\mathcal{K}}(\mathcal{B}) \simeq \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}).$$

*Moreover, $\operatorname{Fin} \rightarrow \mathcal{K}$ is a theory with respect to both for $\operatorname{Fin} \subset \mathcal{S}$ and $\operatorname{Fin} \subset \mathcal{B}$.*

*Remark 8.10.* Note that in particular, if $\mathcal{B}$ is a 1-category, i.e. when $\mathcal{B} = \operatorname{Set}$, then $\mathcal{K}$ is a 1-category. To see this, note that $\operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B})$ can be identified with a full subcategory of $\operatorname{Fun}(\mathcal{O}^{\otimes}, \mathcal{B})$ by [16, Proposition 2.4.1.7], and is hence a 1-category by [15, Corollary 2.3.4.20]. But $\mathcal{K}$ is by definition a full subcategory of $\operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B})$, so the result follows. Similarly, if $\mathcal{B}$ is a 2-category, or rather a $(2, 1)$-category, i.e. when $\mathcal{B} = \operatorname{Gpd}$, then $\mathcal{K}$ is also itself a 2-category.

*Proof.* Let $\mathcal{S}^{\otimes} \rightarrow N(\operatorname{Fin}_{*})$ and $\mathcal{B}^{\otimes} \rightarrow N(\operatorname{Fin}_{*})$ be the $\infty$-operads corresponding to the cartesian monoidal structure on $\mathcal{S}$ and $\mathcal{B}$ (as explained in section 2.1.1 of [16]).

Consider the diagram

$$\begin{array}{ccc} \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}) & \longrightarrow & \operatorname{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{S}) \\ F_1 \downarrow & & F_2 \downarrow \\ \mathcal{B} & \longrightarrow & \mathcal{S} \end{array} \quad (6)$$

First, we note that the top horizontal map is fully faithful. Indeed, the categories of $\mathcal{O}$-algebras are full subcategory of the categories of functor $\operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{B}^{\otimes})$ and $\operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{S}^{\otimes})$ over $\operatorname{Fin}_{*}$. But the functor $\operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{B}^{\otimes}) \rightarrow \operatorname{Fun}_{/\operatorname{Fin}_{*}}(\mathcal{O}^{\otimes}, \mathcal{S}^{\otimes})$ is fully faithful because it is a pullback of $\operatorname{Fun}(\mathcal{O}^{\otimes}, \mathcal{B}^{\otimes}) \rightarrow \operatorname{Fun}(\mathcal{O}^{\otimes}, \mathcal{S}^{\otimes})$ which is fully faithfull by 8.8.

48

Let $M_1, M_2$ be the monads associated to the left and right vertical maps of $G$, respectively. Since the horizontal maps are fully faithful, we can without loss of generality treat the horizontal maps as inclusions of full subcategories. The restriction of the counit of $H_2 \dashv F_2$ gives the counit of the adjunction $H_2|_{\mathcal{B}} : \mathcal{B} \leftrightarrows Alg_{\mathcal{O}^\otimes}(\mathcal{B}) : F_1$, since $H_2$ takes objects of $\mathcal{B}$ to $Alg_{\mathcal{O}^\otimes}(\mathcal{B})$. Consider the composites

$$\text{Fin} \subseteq \mathcal{B} \xrightarrow{H_2|_{\mathcal{B}}} Alg_{\mathcal{O}^\otimes}(\mathcal{B}) \quad \text{Fin} \subseteq \mathcal{S} \xrightarrow{H_2} Alg_{\mathcal{O}^\otimes}(\mathcal{S})$$

the essential images of which correspond to $\text{Th}_{\mathcal{B}}(M_1), \text{Th}_{\mathcal{S}}(M_2)$. These composites are the same, since $\text{Fin} \subseteq \mathcal{B}$. We will denote the composite by $\text{Fin} \rightarrow \mathcal{K}$.

But by 8.7, $M_1, M_2$ are both Fin-Nervous, so that $M_1 \cong \mu_{\mathcal{B}}^{\text{Th}(M_1)} \cong \mu_{\mathcal{B}}^{\mathcal{K}}$, $M_2 \cong \mu_{\mathcal{S}}^{\text{Th}(M_2)} \cong \mu_{\mathcal{S}}^{\mathcal{K}}$.

*Remark 8.11.* In the situation of 8.9 the proof implies that $\text{Free}_{\mathcal{O}}^{\mathcal{B}}$ can be identified with $\text{Free}_{\mathcal{O}}^{\mathcal{S}}|_{\mathcal{B}}$. Thus, we can think of $\text{Free}_{\mathcal{O}}^{\mathcal{S}}$ as extending $\text{Free}_{\mathcal{O}}^{\mathcal{B}}$.

**Example 8.12.** Let $E_1^\otimes$ be the $E_1$-operad studied in [16, Chapter 5]. Using [16, Example 5.1.0.7] we can identify this with the associative operad $\text{Assoc}^\otimes$. By [16, Proposition 4.1.1.18], the free monad functor $\mathcal{S} \rightarrow \text{Alg}_{E_1^\otimes}(\mathcal{S})$ takes $C$ to an algebra with underlying object $\coprod_{n \in \mathbb{N}} C^n$. Since (co)products in the $\infty$-category of spaces can be identified with ordinary (co)products, the free algebra functor preserves the property of having the homotopy type of a set.

Thus, we can apply 8.9 with $\mathcal{B} = \text{Set}, \mathcal{O}^\otimes = E_1^\otimes$ and 8.11, to conclude that the “free-$E_1$-space”-monad on $\mathcal{S}$ extends the “free monoid monad” on sets.

By the rectification result of [16, Theorem 4.1.8.4], $Alg_{\text{Assoc}^\otimes}(\text{Set}) \rightarrow \text{Set}$ can be identified with the forgetful functor $\text{Monoid} \rightarrow \text{Set}$, which takes a monoid in the classical sense to its underlying set. Thus, the ‘free monoid monad’ constructed above can be identified with the classical free monoid monad from [4, Example 9]). Moreover, if $\mathcal{K}$ is the classical algebraic theory from [4] whose set-valued models are monoids, then its models in $\mathcal{S}$ can be identified with the $E_1$-spaces.

**Lemma 8.13.** *Let $\text{Comm}^\otimes$ be the commutative (or $E_\infty$) operad studied in [16, Example 2.1.1.8]. The free algebra functor $\mathcal{S} \rightarrow \text{Alg}_{\text{Comm}^\otimes}(\mathcal{S})$ takes elements of $\text{Gpd}$ to elements of $\text{Alg}_{\text{Comm}^\otimes}(\text{Gpd})$.*

49

*Proof.* By [16, Example 3.1.3.14], the left adjoint to the forgetful functor is given by $C \mapsto \coprod_{n \geq 0} \operatorname{Sym}^n(C)$, where $\operatorname{Sym}^n$ is as in [16, Construction 3.1.3.9]. Thus, it suffices to show that $\operatorname{Sym}^n(-)$ takes groupoids to groupoids.

Let $\Sigma_n$ be the symmetric group regarded as a category with one object. Unwinding [16, Construction 3.1.3.9], $\operatorname{Sym}^n(C)$ gets identified with the colimit of a diagram $N(\Sigma_n) \rightarrow \mathcal{S}$ which takes the object to $C^n$ and acts by permuting the factors. This can be further identified with the homotopy colimit of a group acting on a space.

Such a homotopy colimit is called a *homotopy orbit space*, and it fits into a homotopy fibre sequence

$$C^n \rightarrow \operatorname{Sym}^n(C) \rightarrow N(\Sigma_n)$$

(for a description of homotopy orbit spaces, and the above fibre sequence, see [7, Chapter 1, Section 6]). The long exact sequence of homotopy groups associated to the above fibre sequence shows that since $N(\Sigma_n), C^n$ are groupoids, so is $\operatorname{Sym}^n(C)$.

**Example 8.14.** By the preceding lemma we can apply 8.9, 8.11 with $\mathcal{O}^\otimes = E^\otimes_\infty, \mathcal{B} = \operatorname{Gpd}$ to show that the monad $\operatorname{Free}^\mathcal{S}_{E_\infty}$ extends $\operatorname{Free}^\operatorname{Gpd}_{E_\infty}$. In other words, the free symmetric monoidal groupoid monad is extended by the Free $E_\infty$-space monad.

Using [16, Example 2.4.2.5] and [16, Proposition 2.4.2.4], we see that the objects of $\operatorname{Alg}_{E^\otimes_\infty}(Gpd)$ can be identified with symmetric monoidal groupoids. By the definition of 1-morphisms in this $\infty$-category can be identified with functors $F: A \rightarrow B$ of symmetric monoidal categories, along with isomorphism $F(-\otimes_A -) \cong F(-) \otimes_B F(-)$, compatible with the commutativity and associativity properties of $A$ and $B$. In other words, they can be identified with monoidal functors. Similarly the 2-morphisms in $\operatorname{Alg}_{E^\otimes_\infty}(Gpd)$ can be identified with monoidal natural transformations. Thus we can identify $\operatorname{Free}^\operatorname{Gpd}_{E_\infty}$ with the classical free symmetric monoidal groupoid monad considered in [3].

**Example 8.15.** The free $E_2$-algebra $\mathcal{S} \rightarrow \operatorname{Alg}_{E^\otimes_2}(\mathcal{S})$ takes an object $X$ to $\coprod_{n \in \mathbb{N}} B^n(X)$, where $B^n(X)$ is the colimit of the braid group action on $X^n$. This functor takes $\operatorname{Gpd}$ to $\operatorname{Alg}_{E^\otimes_2}(\operatorname{Gpd})$, by the same argument as 8.13. As noted in [16, Example 5.1.2.4], the objects of $\operatorname{Alg}_{E^\otimes_2}(\operatorname{Gpd})$ can be identified with braided monoidal groupoids. Thus, as in the preceding example, we can

50

conclude that the free braided monoidal groupoid monad is extended by the free $E_2$-space monad.

*Remark 8.16.* If $n \geq 3$, is not possible to find a monad on Gpd whose algebraic theory has as its $\mathcal{S}$-models $E_n$-spaces. The reason is that by [16, Corollary 5.1.1.7], $E_\infty$-algebras and $E_n$ algebras in Gpd coincide for $n \geq 3$, so the existence of a theory with the required properties would imply that $E_\infty$-spaces are the same as $E_n$-spaces. The aforementioned fact can be viewed as an analogue of the Baez-Dolan stabilization hypothesis (see [1] and [16, Example 5.1.2.3]).

It should be noted that for all $2 < n < \infty$, the free $E_n$-algebra on a set $X$ has homotopy groups in arbitrary large dimension, i.e. is not $k$-truncated for any $k$. So replacing $\mathcal{B}$ by the category of $k$-groupoids for a larger $k$ does not allow one to deal with the case of $E_n$-algebra for larger $n$ even if the argument above does not obstruct it.

## 9 Relation to algebraic patterns

Finally, we clarify the relation between our results and Chu and Haugseng's theory of algebraic patterns from [5]. In a very simplified way, algebraic patterns are a type of 'theory' that through the monad-theory adjunction corresponds to cartesian parametric right adjoint$^5$ monads on presheaf categories.

A natural transformation is said to be *cartesian* if all of its naturality squares are cartesian. A monad is said to be cartesian if its unit and composition natural transformation $Id \rightarrow M$ and $M \rightarrow M^2$ are cartesian. This also implies that all other structural morphisms of the monad are cartesian. A parametric right adjoint monad is a monad whose underlying functor $M : \mathcal{C} \rightarrow \mathcal{C}$ admits a right adjoint when considered as a functor $\mathcal{C} \rightarrow \mathcal{C}/M(1)$ for 1 a terminal object of $\mathcal{C}$.

Note that [5] defines models in terms of covariant functors to Set while we use presheaves, i.e. contravariant functors as in the 1-categorical tradition (like [2] or [4]). To simplify the connection between the present paper and [5], we will rephrase the definitions given in [5] in terms of the opposite categories.

$^5$which are called polynomial monads in [5].

51

A *categorical pattern* in the sense of [5] is a category $\mathcal{O}$ endowed with a factorization system $(\mathcal{O}^{act}, \mathcal{O}^{in})$ whose left class is called the *active morphisms* and the right class is called the *inert morphisms*, and a full subcategory $\mathcal{O}^{el} \subset \mathcal{O}^{in}$ of objects called elementary objects.

Given a categorical pattern $(\mathcal{O}, \mathcal{O}^{act}, \mathcal{O}^{in}, \mathcal{O}^{el})$, a Segal $\mathcal{O}$-object is a presheaf $\mathcal{F}$ on $\mathcal{O}$ which satisfies the following equivalent conditions:

- For all $X \in \mathcal{O}$, the map

$$\mathcal{F}(X) \rightarrow \lim_{\substack{E \rightarrow X \in \mathcal{O}^{in} \\ E \in \mathcal{O}^{el}}} \mathcal{F}(E)$$

is an equivalence.

- The restriction of $\mathcal{F}$ to $\mathcal{O}^{in}$ is a right Kan extension of $\mathcal{F}$ restricted to $\mathcal{O}^{el}$. (See lemma 2.9 of [5]).

We can immediately see this as a special case of the notion of theory of the present paper as follows: Consider the functor $\mathcal{O}^{in} \rightarrow \Pr \mathcal{O}^{el}$ that is obtained by composing the Yoneda embedding with the restriction functor:

$$\mathcal{O}^{in} \rightarrow \Pr \mathcal{O}^{in} \rightarrow \Pr \mathcal{O}^{el}$$

The induced nerve functor $\Pr \mathcal{O}^{el} \rightarrow \Pr \mathcal{O}^{in}$ is equivalent to the fully faithful inclusion of the full subcategory of objects of $\Pr \mathcal{O}^{in}$ that satisfies the Segal condition mentioned above. By definition the $\infty$-category of Segal $\mathcal{O}$-objects, we have a pullback:

$$\begin{array}{ccc} Seg_{\mathcal{O}} & \longrightarrow & \Pr \mathcal{O} \\ \downarrow & \swarrow & \downarrow \\ \Pr \mathcal{O}^{el} & \longrightarrow & \Pr \mathcal{O}^{in} \end{array} \quad (7)$$

That is, $Seg_{\mathcal{O}}$ is the category of $\mathcal{O}$-models where $\mathcal{O}$ is seen as $\mathcal{O}^{in}$-theory for the canonical inclusion $\mathcal{O}^{in} \rightarrow \mathcal{O}$, and the dense functor $\mathcal{O}^{in} \rightarrow \Pr \mathcal{A}$.

The condition that the categorical pattern $\mathcal{O}$ is *extendable* (see Definition 8.5 of [5]) is equivalent, by Proposition 8.8 of [5] to the fact that the pullback diagram (7) satisfies a Beck-Chevalley condition. That is, that the

52

corresponding $\mathcal{O}^{in}$-Nervous monad on $\Pr \mathcal{O}^{el}$ is a monad with arities in the sense of Definition 6.2.

In particular, the mains results of Chu and Haugseng can be summarized in our language as:

- For an extendable algebraic pattern, the associated monad under the monad-theories correspondence is a parametric right adjoint cartesian monad on $\Pr \mathcal{O}^{el}$,
- conversely any such parametric right adjoint cartesian monad on a presheaf category can be obtained this way.

They also formulate a more precise form of this in terms of an equivalence of $\infty$-categories between parametric right adjoint cartesian monads and a certain subclass of algebraic pattern as Theorem 15.8.

In particular, all the examples of categorical patterns given in section 3 of [5] are examples of theories, or equivalently of nervous monads. This includes:

1. The free $\Gamma$-space monad (or equivalently $E_\infty$-space monad) on the $\infty$-category of spaces, which is described as the theory $\mathcal{A} \to \Gamma$ for $\mathcal{A}$ the category of finite sets and injections and $\Gamma$ the Segal category (i.e. the opposite category of pointed finite sets). See example 3.1 of [5].
2. A “free $n$-uple Segal spaces” monad on the $\infty$-category $\Pr(\Delta_{\leqslant 1})^n$ (Example 3.4 of [5]).
3. A “free Rezk $\Theta_n$-space” monad on the $\infty$-category of globular spaces, which are a model of $(\infty, n)$-categories. (Example 3.5 of [5]).
4. The category of dendroidal space is also obtained as the category of algebras for a monads on the category of presheaves on the category of corollas, see example 3.7 of [5]. Other kind of operads (cyclic, modular, properads, etc...) have similar description in the subsequent examples (example 3.8 to 3.11).

## References

[1] John Baez and John Dolan, *Higher dimensional algebra and topological quantum field theory*, Journal of Mathematical Physics **36** (1995), no. 11, 2029–2048.

53

[2] Clemens Berger, Paul-André Mellies, and Mark Weber, *Monads with arities and their associated theories*, Journal of Pure and Applied Algebra **216** (2012), no. 8-9, 2029-2048.[3] R. Blackwell, G.M. Kelly, and J. Power, *Two-dimensional monad theory*, Journal of Pure and Applied Algebra **59** (1989), 1-41.[4] John Bourke and Richard Garner, *Monads and theories*, Advances in Mathematics **351** (2019), 1024-1071.[5] Hongyi Chu and Rune Haugseng, *Homotopy-coherent algebra via segal conditions*, Advances in Mathematics **385** (2021).[6] Charles D. Cisinski, *Higher categories and homotopical algebra*, Cambridge Studies in Advanced Mathematics, Cambridge University Press, Cambridge, England, 2019.[7] William G. Dwyer and Hans Werner Henn, *Homotopy-theoretic methods in group cohomology*, Advanced Courses in Mathematics CRM Barcelona, Springer, Barcelona, 2001.[8] David Gepner, Rune Haugseng, and Thomas Nikolaus, *Lax colimits and free fibrations in $\infty$-categories*, Documenta Mathematica **22** (2017), 1225-1266.[9] David Gepner and Joachim Kock, *Univalence in locally cartesian closed $\infty$-categories*, Forum Mathematicum **29** (2017), no. 3, 617-652.[10] Saul Glasman, *A spectrum-level hodge filtration on topological hochschild homology*, Selecta Mathematica **22** (2016), no. 3, 1583-1612.[11] Rune Haugseng, *On lax transformations, adjunctions, and monads in $(\infty, 2)$-categories*, arXiv preprint arXiv:2002.01037 (2020).[12] Fabian Hebestreit, Sil Linskens, and Joost Nuiten, *Orthofibrations and monoidal adjunctions*, arXiv preprint arXiv:2011.11042 (2020).[13] Roman Kositsyn, *Completeness for monads and theories*, arXiv preprint arXiv:2104.00367 (2021).[14] Fred EJ Linton, *Some aspects of equational categories*, Proceedings of the Conference on Categorical Algebra, Springer, 1966, pp. 84-94.

54

[15] J. Lurie, *Higher topos theory*, Annals of Mathematics Studies, Princeton University Press, Princeton and Oxford, 2009.

[16] J Lurie, *Higher algebra (version: September 2017)*, Online book http://www.math.harvard.edu/~lurie, 2017.

[17] John L. Macdonald and Arthur Stone, *The tower and regular decomposition*, Cahiers de Topologie et Géométrie Différentielle Catégoriques **23** (1982), no. 2, 197–213.

[18] Emily Riehl and Dominic Verity, *Homotopy coherent adjunctions and the formal theory of monads*, Advances in Mathematics **286** (2016), 802–888.

55