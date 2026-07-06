UNIVERSITÉ  
CÔTE D'AZUR

ÉCOLE DOCTORALE  
SCIENCES  
FONDAMENTALES  
ET APPLIQUÉES

# THÈSE DE DOCTORAT

## Théorie et modèles des $(\infty, \omega)$-catégories

Félix Loubaton

Laboratoire J.A. Dieudonné

Présentée en vue de  
l'obtention du grade de  
docteur en mathématiques de  
l'Université Côte d'Azur.  
Dirigée par : Carlos Simpson  
Co-dirigé par : Denis-Charles  
Cisinski  
Soutenue le : 10 Octobre 2023

Devant le jury, composé de :  
Dimitri Ara, Maître de Conférences,  
Université d'Aix-Marseille  
Clemens Berger, Professeur, Université Côte  
d'Azur  
Yonatan Harpaz, Chargé de Recherche,  
Université Sorbonne Paris Nord  
Georges Maltsiniotis, Directeur de Recherche  
Emerite, Université Paris Cité  
Emily Riehl, Professeure, Université Johns  
Hopkins  
Dominic Verity, Professeur Emerite,  
Université Macquarie

arXiv:2307.11931v2 [math.CT] 11 Oct 2023



# Theory and models of $(\infty, \omega)$-categories

## Jury :

### Rapporteurs

Yonatan Harpaz, Chargé de Recherche, Université Sorbonne Paris Nord

Dominic Verity, Professeur Emerite, Université Macquarie

### Examinateur·rice·s

Dimitri Ara, Maître de Conférences, Université d'Aix-Marseille

Clemens Berger, Professeur, Université Côte d'Azur

Georges Maltsiniotis, Directeur de Recherche Emerite, Université Paris Cité

Emily Riehl, Professeure, Université Johns Hopkins

### Directeurs de Thèse

Carlos Simpson, Directeur de Recherche, Université d'Aix-Marseille

Denis-Charles Cisinski (co-directeur), Professeur, Université de Ratisbonne



# Résumé

La théorie des $(\infty, 1)$-catégories est aujourd'hui un domaine de recherche prolifique avec des applications dans divers domaines. Ces dernières années ont également vu l'essor des $(\infty, n)$-catégories. Par exemple, les travaux de Gaitsgory et Rozenblyum ([GR19]) en géométrie algébrique dérivée utilisent les $(\infty, 2)$-catégories pour encoder le formalisme des six foncteurs. On peut aussi citer la théorie topologique des champs quantiques, qui utilise la notion de $(\infty, n)$-catégories dans la formalisation et la preuve de l'hypothèse du cobordisme ([BD95], [Lur08], [GP21], [CS19]).

Il convient donc de développer une théorie des $(\infty, n)$-catégories. Cependant, pour réaliser une telle tâche, il est utile de manipuler les catégories $(\infty, k)$ pour $k \geq n$. Par exemple, la construction de Grothendieck, qui est toujours essentielle lorsque l'on travaille avec n'importe quel type de catégories, est une colimite lax dans la $(\infty, n + 1)$-catégorie ambiante des $(\infty, n)$-catégories. Un deuxième exemple provient du produit tensoriel de Gray, qui est nécessaire pour encoder la notion de transformation lax, et donc pour définir la notion de colimite et limite lax. Le produit tensoriel de Gray ajoute la dimension des entrées, et les $(\infty, n)$-catégories ne sont donc pas stables sous ce bifoncteur. Une façon d'éviter tous ces problèmes liés à l'augmentation de la dimension est de se concentrer directement sur les $(\infty, \omega)$-catégories, ce qui sera le parti pris de ce travail.

Dans la première partie de cette thèse, nous étudions les modèles des $(\infty, \omega)$-catégories. Le résultat principal consiste à établir une équivalence de Quillen entre les $\Theta$-espaces complets de Segal et les ensembles compliciaux de Verity. Une des conséquences majeures de ce résultat est que lorsque l'on travaillera dans la $(\infty, 1)$-catégorie correspondant à ces structures modèles, son lien avec les $\Theta$-espaces complets de Segal de Rezk nous permettra d'utiliser le langage globulaire, tandis que son lien avec les ensembles compliciaux nous donnera accès au produit tensoriel de Gray.

Dans la seconde partie de cette thèse, nous adapterons les constructions de la théorie classique des catégories au cas $(\infty, \omega)$. Le chapitre 4 est consacré à la théorie de base des $(\infty, \omega)$-catégories. Le chapitre 5 introduit la notion de $(\infty, \omega)$-catégories marquées et étudie les fibrations cartésiennes. Le chapitre 6 est consacré à la construction de Grothendieck, à l'univalence, au lemme de Yoneda, et à d'autres constructions catégoriques standard.

**Mots clés.** Ensembles compliciaux, $(\infty, \omega)$-catégories, $(\infty, n)$-catégories, fibrations cartésiennes, construction de Grothendieck, univalence, lemme de Yoneda, (co)limites lax.

# Abstract

The theory of $(\infty, 1)$-categories is today a prolific area of research with applications in a variety of fields. Recent years have also seen the rise of $(\infty, n)$-categories. For example, the work of Gaitsgory and Rozenblyum ([GR19]) in derived algebraic geometry uses $(\infty, 2)$-categories to encode the formalism of six functors. Another example is topological quantum field theory, which uses the notion of $(\infty, n)$-categories in the formalization and proof of the cobordism hypothesis ([BD95], [Lur08], [GP21], [CS19]).

A theory of $(\infty, n)$-categories therefore needs to be developed. However, to accomplish such a task, it is useful to manipulate $(\infty, k)$-categories for $k \geq n$. For example, the Grothendieck construction, which is always essential when working with any type of category, is a lax colimit in the ambient $(\infty, n+1)$-category of $(\infty, n)$-categories. A second example comes from the Gray tensor product, which is needed to encode the notion of lax transformation, and thus to define the notion of lax colimit and limit. The Gray tensor product adds the dimension of the inputs, and the $(\infty, n)$-categories are not stable under this bifonctor. One way of avoiding all these problems associated with the increasing of the dimension is to focus directly on $(\infty, \omega)$-categories.

In the first part of this thesis, we study models of $(\infty, \omega)$-categories. The main result is to establish a Quillen equivalence between Segal $\Theta$-complete spaces and Verity complicial sets. A major consequence of this result is that when working in the $(\infty, 1)$-category corresponding to these model structures, its link with Rezk's $\Theta$-complete Segal spaces will allow us to use the globular language, while its link with complicial sets will give us access to Gray's tensor product.

In the second part of this thesis, we will adapt the constructions of classical category theory to the $(\infty, \omega)$ case. Chapter 4 is devoted to the basic theory of $(\infty, \omega)$-categories. The chapter 5 introduces the notion of $(\infty, \omega)$-marked categories and studies cartesian fibrations. The chapter 6 is devoted to the Grothendieck construction, the univalence, the Yoneda lemma, and other standard categorical constructions.

**Keywords.** Complicial sets, $(\infty, \omega)$-categories, $(\infty, n)$-categories, cartesian fibrations, Grothendieck construction, univalence, lemme de Yoneda, lax (co)limits.

# Remerciements

Tout d'abord, je tiens à remercier mes directeurs de thèse. Merci à vous, Carlos, d'avoir immédiatement répondu oui à ma demande d'inscrire ma thèse à Nice, sous votre direction, alors que nous ne nous connaissons pas. Merci de votre invitation enthousiasmante à participer à un séminaire à Miami avec vous et de nombreux mathématiciens dès la première année : le Covid ne l'a pas permis, cela reste un grand regret. Merci de m'avoir permis de travailler dans de si bonnes conditions à Nice, au sein du LJAD. Merci à toi, Denis-Charles. Travailler sous ta direction fut un honneur et un plaisir. Merci pour les visions, les intuitions et, je ne sais pas comment le dire autrement, la sagesse que tu as partagée avec moi pendant les dernières années. Aussi bien tes recherches que ta pratique de la recherche m'ont profondément inspiré.

I would like to thank Dominic Verity and Yonatan Harpaz for the honor of being my referees. Thank you, Yonatan Harpaz, for helping me to improve my text through your careful and rigorous reading. Thank you, Dominic Verity, for your extraordinarily detailed report, and I have no doubt that all your comments and advice will help me for the continuation of this work and beyond. As my work is built upon your work, having you as a referee has a real special meaning for me.

I would also like to thank Dimitri Ara, Clemens Berger, George Maltsiniotis, and Emily Riehl for agreeing to be part of my jury. I think you'll have understood that each of you has produced works that have deeply inspired me. It is therefore a great honor to defend my thesis in front of you.

Merci à Marnie Valentini pour la relecture attentive de ce manuscrit. Cela fait maintenant plusieurs années qu'elle est l'une de mes plus fidèles (re)lectrices.

Merci à Clara Salaun du LJAD et Birgit Tiefenbach de l'université de Ratisbonne pour avoir rendu l'organisation de tous les déplacements que j'ai effectués lors des dernières années si simple. Merci à Roland Ruelle et Jean-Marc Lacroix pour les multiples aides informatiques. Merci plus généralement à tous ceux qui travaillent dans l'administration et la gestion des laboratoires que j'ai fréquentés.

Cette thèse n'est pas seulement le résultat de trois années de travail, mais aussi l'aboutissement d'un long parcours scolaire qui a commencé il y a un peu plus d'une vingtaine d'années. Merci à tous les professeurs, du primaire au secondaire, que j'ai eus.

Merci à Louis Ritter, Thomas Rouvier, Etienne Chardonnet, Sophie Durrieu et mes autres amis qui ont choisi cette profession. Nos métiers sont cousins, et de toutes les vocations liées à la transmission, la vôtre est sans doute l'une des plus importantes.

Ces trois dernières années ont été rythmées par les émissions des radios du service public. En particulier, merci à Nicolas Stoufflet (Le jeu des 1000 euros) qui sonnait le moment où je devais aller à la fac, merci à Fabienne Sintes (Le téléphone sonne) pour tous les dîners que nous avons partagés, et merci à Jacques Monin (Secrets d'info) pour tous les dimanches midi que nous avons passés ensemble.

Enfin, dans une envolée que je m'autorise, je tiens à remercier plus généralement tous les agents du service public pour leur engagement.

Merci à tous les chercheurs qui m'ont accueilli parmi eux. Merci à George Maltsiniotis pour m'avoir initié à la recherche avec tant de patience, d'acharnement, et de générosité. C'est aussi grâce à toi que Marie se passionne maintenant pour ceux qui pratiquent les mathématiques, et je te remercie pour cela. Merci à Dimitri Ara pour sa prévenance et le climat de confiance qu'il a su instaurer entre nous, si précieux pour moi. Merci à Paul-André Melliès pour sa constante chaleur et curiosité. Merci à Simon Henry grâce à qui j'ai pu me remettre sur pied après presque un an de travail infructueux. Thanks to Viktoriya Ozornova for welcoming me to her team. I'm looking forward to my two years in Bonn!

Merci à tous ceux qui ont été doctorants en même temps que moi, et qui rendent moins solitaire ce travail qui l'est parfois tant. Merci à Hugo Pourcelot, qui fut la première personne que j'ai rencontrée par les mathématiques, et qui me prouva que ce monde était peuplé de belles personnes. Merci à Corentin Le Bars pour cette fin de thèse, ce moment si spécial, que nous avons partagé et durant lequel nous nous sommes aidés. Merci à Hugo Moeneclaey pour avoir été un si bon guide, puis compagnon, dans la découverte de l'homotopie et la logique. Merci à Nicolas Longuet Marx, pour sa proche et constante présence malgré 6419 kilomètres. Thanks to Niklas Kipp, Sebastian Wolf, Linda Hu, and all the people I met during my stays in Regensburg. The warmth of your welcome was more important than you might imagine.

Merci encore à Arnaud Vanhaecke, Léonard Pille-Schneider, Lucie Leszez, Nicolas Le Borgne, Dimitri Navarro, Pauline Rocca, Jonas Pentzien, Leo Hubert, et à tous les doctorants avec lesquels nous avons partagé nos peines et nos joies.

Merci à tous ceux qui rendent le départ de Nice plus triste. Merci à Victor Iwaniack pour sa gentillesse, sa franchise et pour avoir toujours eu un moment pour rêver math, bavarder ou prendre un verre. Je pense que nous avons été de fidèles alliés. Merci à Yash Chopra pour son exigence du doute et son amour du pathétique, ce sont pour moi de très belles qualités. Merci à Victor Pecanha Brittes pour ce bureau que nous avons partagé trop peu de temps. Merci encore à Christian Tayou Fotso, Alex Moriani, Antoine Commaret, Jérémie Marquès, Gustave Billon, Marc Monticelli et toutes les autres personnes gravitant autour du LJAD. A ceux qui arriveront après mon départ, parlez de moi comme celui qui apporta le café.

Merci à Simon Girel et Maëlle Bertier pour avoir été le plus proches de ce qui ressemblait à une famille, et merci à Violette pour l'accueil si chaleureux qu'elle a réservé à notre ami commun.

Merci à Sophie et Laurent d'avoir tant fait pour que je me sente chez moi à Nice.

Merci à tous mes amis proches et ma sœur qui participent pour beaucoup à mon bonheur, et qui sont une composante essentielle de ma vie. En cela, ils ont aidé à la réalisation de ce travail.

Merci à mon père qui sait mieux que quiconque s'occuper du concret, et qui en même temps, rêve peut-être encore plus que moi aux objets que je manipule. Merci à ma mère. Ce choix de vie doit beaucoup à l'admiration que j'ai pour toi, j'espère que tu t'en rends compte. Merci à vous deux pour votre soutien constant.

Enfin, merci Marie. Il n'est pas facile d'exprimer dans un texte public, à la mesure de ce que je pense, ma reconnaissance. Je me contenterais donc pudiquement de te remercier pour transformer tout ce qui aurait pu nous éloigner en des choses qui nous rapprochent, et bien sûr, encore plus, pour tout le reste.



# Contents

|  **Introduction** | **5**  |
| --- | --- |
|  A brief definition of $(\gamma, n)$-categories for $n \in \mathbb{N} \cup \{\omega\}$ | 6  |
|  Overview of the thesis | 9  |
|  Preliminaries | 9  |
|  On the side of models | 11  |
|  On the side of theory | 13  |
|  Notice of authority | 20  |
|  **Preliminaries** | **21**  |
|  **1 The category of $(0, \omega)$-categories** | **23**  |
|  1.1 Basic constructions | 25  |
|  1.1.1 $(0, \omega)$-Categories | 25  |
|  1.1.2 The category $\Theta$ | 29  |
|  1.1.3 The link between presheaves on $\Theta$ and on $\Delta[\Theta]$ | 34  |
|  1.2 Gray Operations | 40  |
|  1.2.1 Recollection on Steiner theory | 40  |
|  1.2.2 Gray operations on augmented directed complexes | 47  |
|  1.2.3 Gray operations on $(0, \omega)$-categories | 53  |
|  **I On the side of models** | **63**  |
|  **2 Study of the complicial model** | **65**  |
|  2.1 Preliminaries | 67  |
|  2.1.1 Generalities on model categories | 67  |
|  2.1.2 Marked and stratified presheaves | 70  |
|  2.2 The complicial model | 73  |
|  2.2.1 Model structure on marked simplicial sets | 73  |
|  2.2.2 Gray tensor product | 76  |

1

|  2.2.3 | Gray cylinder, Gray cone and Gray o-cone | 84  |
| --- | --- | --- |
|  2.2.4 | Street nerve | 85  |
|  2.3 | Suspension and Gray operations | 87  |
|  2.3.1 | Formula for the Gray cylinder | 87  |
|  2.3.2 | Formulas for the Gray cone and the Gray o-cone | 90  |
|  2.4 | Globular equivalences | 93  |
|  2.4.1 | Homotopy categories | 93  |
|  2.4.2 | A criterion to be a weak equivalence | 97  |
|  2.4.3 | A criterion to be a weakly invertible transformation | 101  |
|  2.4.4 | Weak characterization of the identity | 103  |
|  **3** | **Complicial sets as a model of $$(\infty, \omega)$$-categories** | **113**  |
|  3.1 | Preliminaries | 115  |
|  3.1.1 | Segal $$A$$-precategories | 115  |
|  3.1.2 | Stratified Segal $$A$$-precategories | 118  |
|  3.1.3 | Gray module | 123  |
|  3.2 | Gray constructions for stratified Segal $$A$$-categories | 126  |
|  3.2.1 | Gray cylinder | 126  |
|  3.2.2 | Gray cone | 128  |
|  3.2.3 | Link between the Gray cylinder and Gray cone | 131  |
|  3.2.4 | Gray constructions are left Quillen | 133  |
|  3.3 | Quillen Adjunction with $$\text{tPsh}(\Delta)$$ | 136  |
|  3.3.1 | Cosimplicial object | 137  |
|  3.3.2 | Complicial horn inclusions | 143  |
|  3.3.3 | Complicial thinness extensions | 150  |
|  3.3.4 | Saturation extensions | 161  |
|  3.4 | The case $$A := \text{tPsh}(\Delta)^n$$ | 162  |
|  3.4.1 | Comparison with $$(0, \omega)$$-cat | 162  |
|  3.4.2 | The other adjunction | 166  |
|  3.4.3 | Complicial sets as a model of $$(\infty, \omega)$$-categories | 168  |
|  **II** | **On the side of theory** | **171**  |
|  **4** | **The $$(\infty, 1)$$-category of $$(\infty, \omega)$$-categories** | **173**  |
|  4.1 | Preliminaries | 175  |
|  4.1.1 | Explicit computation of some colimits | 175  |
|  4.1.2 | Factorization sytems | 177  |

2

|  4.1.3 | Reflexive localization | 183  |
| --- | --- | --- |
|  4.2 | Basic constructions | 185  |
|  4.2.1 | $$(\infty, \omega)$$-Categories | 185  |
|  4.2.2 | Discrete Conduché functors | 202  |
|  4.3 | Gray Operations | 207  |
|  4.3.1 | Gray operations on $$(\infty, \omega)$$-categories | 207  |
|  4.3.2 | Gray deformation retract | 212  |
|  4.3.3 | Gray operations and strict objects | 216  |
|  **5** | **The $$(\infty, 1)$$-category of marked $$(\infty, \omega)$$-categories** | **231**  |
|  5.1 | Marked $$(\infty, \omega)$$-categories | 233  |
|  5.1.1 | Definition of marked $$(\infty, \omega)$$-categories | 233  |
|  5.1.2 | Gray tensor product of marked $$(\infty, \omega)$$-categories | 241  |
|  5.1.3 | Gray operations on marked $$(\infty, \omega)$$-categories | 247  |
|  5.1.4 | Marked Gray deformation retract | 254  |
|  5.2 | Cartesian fibrations | 258  |
|  5.2.1 | Left and right cartesian fibrations | 258  |
|  5.2.2 | Cartesian fibration are exponentiable | 271  |
|  5.2.3 | Colimits of cartesian fibrations | 277  |
|  5.2.4 | Smooth and proper morphisms | 283  |
|  5.2.5 | The **W**-small $$(\infty, \omega)$$-category of **V**-small left cartesian fibrations | 290  |
|  **6** | **The $$(\infty, \omega)$$-category of small $$(\infty, \omega)$$-categories** | **299**  |
|  6.1 | Univalence | 302  |
|  6.1.1 | Internal category | 302  |
|  6.1.2 | Grothendieck construction | 310  |
|  6.1.3 | Univalence | 320  |
|  6.1.4 | $$(\infty, \omega)$$-Functorial Grothendieck construction | 330  |
|  6.2 | Yoneda lemma and applications | 336  |
|  6.2.1 | Yoneda lemma | 336  |
|  6.2.2 | Adjoint functors | 343  |
|  6.2.3 | Lax colimits | 349  |
|  6.2.4 | Kan extensions | 360  |

3

Index of symbols 363
Index of notions 367
Bibliography 371

4

# Introduction

The theory of $(\infty, 1)$-categories is now a prolific field of research with applications in various domains. The past years have also witnessed the rise of $(\infty, 2)$-categories. We will provide two reasons motivating the study of $(\infty, 2)$-categories.

A first motivation comes from their applications in other domains. We think in particular of the work of Gaitsgory and Rozenblyum ([GR19]) in derived algebraic geometry, where $(\infty, 2)$-categories are an essential tool for encoding the six functor formalism.

A second motivation for considering $(\infty, 2)$-categories arises from the theory of $(\infty, 1)$-categories itself. Just as 1-categories organize into a 2-category, $(\infty, 1)$-categories organize into an $(\infty, 2)$-category. Working with this richer structure provides a powerful framework for developing formal category theory, as performed in [Gra06] for the strict case and [RV22] for $(\infty, 1)$-categories.

However, there is no reason to stop at dimension 2. Let us once again mention two reasons for exploring $(\infty, n)$-categories for $n \in \mathbb{N} \cup \{\omega\}$.

Firstly, $(\infty, n)$-categories are already being used in other research fields, such as topological quantum field theory, where this notion is essential to the formalization and proof of the cobordism hypothesis ([BD95], [Lur08], [GP21], [CS19]).

Secondly, even to understand the theory of $(\infty, n)$-categories, it is useful to manipulate $(\infty, k)$-categories for $k \geq n$. A first example is given by the fact that $(\infty, n)$-categories organize into an $(\infty, n+1)$-category, and this richer structure plays an important role in the theory of $(\infty, n)$-categories. For instance, the Grothendieck construction, which is always essential when working with any flavor of categories, is a lax colimit in the ambient $(\infty, n+1)$-category of $(\infty, n)$-categories. A second example arises from the Gray tensor product, which is a fundamental operation that arises when $n > 1$. This operation is necessary to encode the notion of lax transformation, which leads to the concepts of lax colimits and limits. It is also worth noticing that it plays a crucial role in [GR19].

**Example** (examples of some Gray tensor products). We denote by $\mathbf{D}_1$ the 1-category generated by the 1-graph

$$0 \longrightarrow 1$$

5

Introduction

and by $\mathbf{D}_2$ the 2-category generated by the 2-graph

The Gray tensor product of $\mathbf{D}_1$ with itself, denoted by $\mathbf{D}_1 \otimes \mathbf{D}_1$, is the 2-category generated by the diagram

![img-0.jpeg](img-0.jpeg)

The Gray tensor product of $\mathbf{D}_2$ with $\mathbf{D}_1$, denoted by $\mathbf{D}_2 \otimes \mathbf{D}_1$, is the 3-category generated by the diagram

![img-1.jpeg](img-1.jpeg)

As we can see from these examples, the Gray tensor product adds the dimension of the inputs (in contrast to the cartesian product, which takes the maximum). Thus, $(\infty, n)$-categories are not stable under this operation. One can handle this by considering a truncated version of the Gray tensor product, but we believe that avoiding such violent operation will lead to a more natural understanding of the complex combinatorics it encodes.

One way to avoid all these issues related to the increasing of dimension is to directly focus on $(\infty, \omega)$-categories, which will be the standpoint of this thesis.

## A brief definition of $(\gamma, n)$-categories for $n \in \mathbb{N} \cup \{\omega\}$

A *globular set* is the data of a diagram of sets

$$X_0 \xleftarrow{\pi_0^+} X_1 \xleftarrow{\pi_1^+} X_2 \xleftarrow{\pi_2^+} \dots$$

with the relations $\pi_{n-1}^\epsilon \pi_n^+ = \pi_n^\epsilon \pi_n^-$ for any $n > 0$ and $\epsilon \in \{+, -\}$. We also denote by $\pi_k^\epsilon$ the map $X_n \to X_k$ for $k < n$ obtained by composing any string of arrows starting with $\pi_k^\epsilon$. An $\omega$-*category* is a globular set $X$ together with

(1) operations of *compositions*

$$X_n \times_{X_k} X_n \to X_n \quad (0 \le k < n)$$

which associate to two $n$-cells $(x, y)$ verifying $\pi_k^+(x) = \pi_k^-(y)$, an $n$-cell $x \circ_k y$,

6

(2) as well as *units*

$$X_n \rightarrow X_{n+1}$$

which associate to an $n$-cell $x$, an $(n+1)$-cell $\mathbb{I}_x$,

and satisfying some associativity and unitaly axioms which will be expected by any reader familiar with 2-categories (see 1.1.1.2 for the precise formulation of these axioms). A *morphism of $\omega$-categories* is a map of globular sets commuting with both operations. The category of $\omega$-categories is denoted by $\omega$-cat.

The category $\Theta$ of Joyal is the full subcategory of $\omega$-cat spanned by the *globular sums*. These objects are precisely defined in paragraph 1.1.2.2. Roughly speaking, globular sums are the $\omega$-categories obtained by "directed" gluing of *globes*. In particular, globes are the easiest example of globular sums. Here are a few examples of globes and globular sums, where we identify the pasting diagrams with the $\omega$-categories they generate.

**Example** (some examples of globes).

![img-2.jpeg](img-2.jpeg)

**Example** (some examples of globular sums).

![img-3.jpeg](img-3.jpeg)

**Example** (some examples of morphisms between globular sums).

![img-4.jpeg](img-4.jpeg)

For $n \in \mathbb{N} \cup \{\omega\}$, we define $\Theta_n$ as the full subcategory of $\Theta$ whose objects correspond to $n$-categories. In particular, $\Theta_0$ is the terminal category, $\Theta_1$ is $\Delta$, and $\Theta_\omega$ is $\Theta$.

Let $\gamma$ be a complete $(\infty, 1)$-category and $n \in \mathbb{N} \cup \{\omega\}$. A $(\gamma, n)$-category is a functor $\Theta_n^{op} \rightarrow \gamma$ that satisfies the *Segal conditions* and *completeness conditions*. We denote

7

Introduction

by $(\gamma, n)$-cat the $(\infty, 1)$-category of $(\gamma, n)$-categories. Since we have not given a precise definition of $\Theta$, we cannot explicitly state these conditions, but we will try to explain their essence.

**Segal conditions.** As the diagrams given in the examples suggest, every globular sum is a colimit of globes. For instance, $a_2$ is the colimit of the following diagram

$$\begin{array}{c} \mathbf{D}_2 \\ i_1^+ \uparrow \\ \mathbf{D}_1 \xleftarrow{i_0^+} \mathbf{D}_0 \xrightarrow{i_0^-} \mathbf{D}_2 \\ i_1^- \downarrow \\ \mathbf{D}_3 \end{array}$$

A functor $X : \Theta_n^{op} \to \gamma$ satisfies the *Segal conditions* if it sends these colimits to limits. For instance, the presheaf $X$ must send $a_2$ to the limit of the diagram

$$\begin{array}{c} X(\mathbf{D}_2) \\ \pi_1^+ \downarrow \\ X(\mathbf{D}_1) \xrightarrow{\pi_0^+} X(\mathbf{D}_0) \xleftarrow{\pi_0^-} X(\mathbf{D}_2) \\ \pi_1^- \uparrow \\ X(\mathbf{D}_3) \end{array}$$

The morphisms $X(f_0)$ and $X(f_1)$ can then be interpreted as compositions and the morphism $X(f_3)$ as a unit.

**Completeness conditions.** Let $X : \Theta_n^{op} \to \gamma$ be a functor satisfying the Segal conditions. Given an integer $k \le n$, we have two notions of equivalence on the $k$-cells of $X$, i.e. the morphisms $1 \to X(\mathbf{D}_k)$. The first comes from the canonical equivalence provided by the $\infty$-groupoid $\operatorname{Hom}(1, X(\mathbf{D}_k))$, and the second is more categorical and identifies *isomorphic* elements, i.e. $k$-cells $a, b$ such that there exists $(k+1)$-cells $f : a \to b$, $g : b \to a$ and equivalences

$$g \circ_k f \sim id_a \qquad \text{and} \qquad f \circ_k g \sim id_b.$$

The presheaf $X$ satisfies the completeness condition if these two notions of equivalence coincide. Thus, *groupoids*, i.e., $(\gamma, n)$-categories in which all $k$-cells are equivalent to the identity of their source (or target), correspond to constant functors $\Theta^{op} \to \gamma$. The datum of the $(\infty, 1)$-category $\gamma$ can be understood as a *choice of a notion of groupoid*.

When $\gamma$ is the category of sets, the $(\gamma, n)$-categories will simply be denoted as $(0, n)$-categories, and when $\gamma$ is the $(\infty, 1)$-category of spaces, they will be denoted as $(\infty, n)$-categories.

8

For instance, $(0, \omega)$-categories correspond to $\Theta$-sets satisfying the Segal and completeness conditions. The first one induce an inclusion of $(0, \omega)$-categories into $\omega$-categories and the latter forces isomorphisms to be identities. The $(0, \omega)$-categories then correspond to *Gaunt $\omega$-categories*.

Although this concept is not studied in the present thesis, it is worth noticing that one could define $(k, n)$-categories for any $k \in \mathbb{N}$. In this case, we would consider the $(\gamma, n)$-categories with $\gamma$ being the $(\infty, 1)$-category of $k$-truncated $\infty$-groupoids. This notation is compatible with the one given in [Rez10] when $k \geq n$ but it also allows to give meaning to $(k, n)$-categories for $k < n$.

As stated earlier, this work is devoted to the concept of $(\infty, \omega)$-categories, which corresponds to the case where $\gamma$ is the category of spaces. This notion is sometimes considered ambiguous. Indeed, Schommer-Pries and Rezk have independently argued ([hsp]) that there should be more than one notion of $(\infty, \omega)$-categories. The one we use here is commonly referred to as *the inductive one*, in the sense that $(\infty, \omega)$-cat is identified with the limit of the sequence:

$$(\infty, 0)\text{-cat} \xleftarrow{\tau_0} (\infty, 1)\text{-cat} \leftarrow \dots \leftarrow (\infty, n)\text{-cat} \xleftarrow{\tau_n} (\infty, n+1)\text{-cat} \leftarrow \dots$$

where the functors $\tau_n$ 'forget' the cells of dimension $n$. For a more detailed discussion in the (semi-)strict case, we refer to [HL23].

## Overview of the thesis

This thesis is divided into two parts which can be read independently. However, each of them uses results from the preliminary section.

### Preliminaries

**Chapter 1.** The first section is devoted to the definition of $(0, \omega)$-categories and of the category $\Theta$ of Joyal. We also show that the category $\Theta$ presents the category of $(0, \omega)$-categories, and we also exhibit an other presentation of this category (corollary 1.1.3.4).

The second section begins with a review of Steiner theory, which is an extremely useful tool for providing concise and computational descriptions of $(0, \omega)$-categories. Following Ara and Maltsiniotis, we employ this theory to define the Gray tensor product, denoted by $\otimes$, in $(0, \omega)$-categories. We then introduce the Gray operations, starting with the Gray cylinder $\_ \otimes [1]$ which is the Gray tensor product with the directed interval $[1] := 0 \rightarrow 1$.

9

Introduction

Then, we have the Gray cone and Gray o-cone, denoted by \(\_ \star 1\) and \(1 \stackrel{co}{\star} \_\), that send an \((0, \omega)\)-category \(C\) onto the following pushouts:

![img-5.jpeg](img-5.jpeg)

![img-6.jpeg](img-6.jpeg)

We also present a formula that illustrates the interaction between the suspension and the Gray cylinder. As this formula plays a crucial role in both Part I and Part II, we provide its intuition at this stage.

If \( A \) is any \( (0, \omega) \)-category, the suspension of \( A \), denoted by \( [A, 1] \), is the \( (0, \omega) \)-category having two objects - denoted by 0 and 1- and such that

\[
\operatorname{Hom} _ {[ A, 1 ]} (0, 1) := A, \quad \operatorname{Hom} _ {[ A, 1 ]} (1, 0) := \emptyset , \quad \operatorname{Hom} _ {[ A, 1 ]} (0, 0) = \operatorname{Hom} _ {[ A, 1 ]} (1, 1) := \{i d \}.
\]

We also define  \( [1] \vee [A,1] \)  as the gluing of [1] and  \( [A,1] \)  along the 0-target of [1] and the 0-source of  \( [A,1] \) . We define similarly  \( [A,1] \vee [1] \) . These two objects come along with whiskerings:

\[
\nabla : [ A, 1 ] \to [ 1 ] \vee [ A, 1 ] \quad \text { and } \quad \nabla : [ A, 1 ] \to [ A, 1 ] \vee [ 1 ]
\]

that preserve the extremal points.

The \((0,\omega)\)-category \([1]\otimes [1]\) is induced by the diagram:

![img-7.jpeg](img-7.jpeg)

and is then equal to the colimit of the following diagram:

\[
[ 1 ] \vee [ 1 ] \stackrel {\triangledown} {\leftarrow} [ 1 ] \hookrightarrow [ [ 1 ], 1 ] \leftrightarrow [ 1 ] \stackrel {\triangledown} {\rightarrow} [ 1 ] \vee [ 1 ].
\]

The \((0,\omega)\)-category \([1],1]\otimes [1]\) is induced by the diagram:

![img-8.jpeg](img-8.jpeg)

and is then equal to the colimit of the following diagram:

\[
[ 1 ] \vee [ [ 1 ], 1 ] \stackrel {\triangledown} {\leftarrow} [ [ 1 ] \otimes \{0 \}, 1 ] \hookrightarrow [ [ 1 ] \otimes [ 1 ], 1 ] \leftrightarrow [ [ 1 ] \otimes \{1 \}, 1 ] \stackrel {\triangledown} {\rightarrow} [ [ 1 ], 1 ] \vee [ 1 ]
\]

We prove a formula that combines these two examples:

10

**Theorem 1.2.3.13.** *In the category of $(0, \omega)$-categories, there exists an isomorphism, natural in $A$, between $[A, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A \otimes \{0\}, 1] \longrightarrow [A \otimes [1], 1] \longleftarrow [A \otimes \{1\}, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

We also provide similar formulas for the *Gray cone* and the *Gray $\circ$-cone*.

**Theorem 1.2.3.14.** *There is a natural identification between $1 \stackrel{\circ}{\star} [A, 1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $[A, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\circ}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

## On the side of models

Following the terminology of Barwick and Schommer-Pries ([BSP21]), we call *model of $(\infty, n)$-categories* any model category whose corresponding $(\infty, 1)$-category is $(\infty, n)$-cat.

With the definition of $(\infty, n)$-categories given above, we have a natural model for the $(\infty, 1)$-category $(\infty, n)$-cat, given by Rezk's complete Segal $\Theta_n$-spaces, i.e. space valued presheaves on $\Theta_n$ satisfying the (homotopical) Segal conditions and (homotopical) completeness conditions. However, there are many other models, see for instance [Ara14], [BR13a], [BR20], [BR13b] (we refer to [BSP21] for a comprehensive presentation of these models and their equivalences). For example, one can mention $n$-fold Segal spaces and Simpson's and Tamsamani's Segal $n$-categories among others.

It was conjectured ([Str87], [Ver17], [BSP21]) that Verity's $n$-complicial sets were also a model of $(\infty, n)$-categories. This would imply that Campion-Kapulkin-Maehara's $n$-comical sets also are, as they are shown to be Quillen equivalent to $n$-complicial sets in [DKM21]. In the second chapter, we will give a positive answer to this conjecture (theorem 3.4.3.2).

One of the major consequences of this result is to endow $(\infty, \omega)$-cat with a monoidal product called the *Gray tensor product*. This operation will play a crucial role in the second part of this thesis, which is dedicated to the theory of $(\infty, \omega)$-categories.

The two main models we work with are Verity's complicial sets (definition 2.2.1.5) and (a slight modification of) Segal $A$-precategories (defined in paragraph 3.1.1.6) as developed by Simpson ([Sim11]). In the complicial model, we will make crucial use of the strictification results of Ozornova and Rovelli ([OR20a], [OR22]).

11

Introduction

**Chapter 2.** One of the benefits of complicial sets is that they admit a simple definition of the Gray tensor product. Being strongly linked to $(0, \omega)$-categories by the Street nerve, they are also a privileged framework for stating and proving strictification results, as done in [OR20a], [GOR21], [OR22] and [Mae23]. However, they do not interact *a priori* well with the globular language. The goal of this chapter is to show that, with some computation, it is possible to have a globular point of view in this model.

The first section is a recollection of usual results and definitions about complicial sets. In the second section, we aim to prove an analogue of the formula given in 1.2.3.13 to the complicial setting. We also have a suspension in this category, which is denoted by $X \mapsto \Sigma X$. Objects $[1] \ \forall \ \Sigma X$ and $\Sigma X \ \forall \ [1]$ are defined in 2.2.2.19, but for now, we can suppose that they are fibrant replacements of respectively $[1] \coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \ \forall \ \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \ \forall \ [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:*

$$\Sigma X \ \forall \ [1] \ \stackrel{\nabla}{\leftarrow} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \ \forall \ \Sigma X.$$

We also provide similar formulas for the *Gray cone* and Gray $\circ$-*cone*:

**Theorem 2.3.2.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \ \star \ [0]$ and the colimit of the following diagram:*

$$\Sigma X \ \forall \ [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{co}{\star} X).$$

*There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{co}{\star} \Sigma X$ and the colimit of the following diagram:*

$$\Sigma(X \ \star \ [0]) \leftarrow \Sigma X \to [1] \ \forall \ \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[i_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[i_3^-]{i_3^+} \dots$$

12

**Theorem 2.4.4.14.** *Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.*

Proposition 15.10 of [BSP21] provides a similar result for models of $(\infty, n)$-categories.

**Chapter 3.** Results of Bergner, Gagna, Harpaz, Lanari, Lurie and Rezk ([BR13a],[BR20], [Rez10], [Lur09a],[Lur09b], [GHL22]) imply that 2-complicial sets are a model of $(\infty, 2)$-categories (see [GHL22] to understand how to use all this source to obtained the desired result and [BOR21] for a direct comparison between complete Segal $\Theta_2$-spaces and 2-complicial sets). The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

To this extend, we first address the more general problem of finding sufficient conditions on a model category $A$ to build a *Gray cylinder* $C \mapsto I \otimes C$ and a *Gray cone* $C \mapsto e \star C$ on Segal precategories enriched in $A$. These two operations should be linked by the following homotopy cocartesian square

$$\begin{array}{c} \{0\} \otimes C \longrightarrow I \otimes C \\ \downarrow \qquad \qquad \qquad \downarrow \\ e \longrightarrow e \star C \end{array}$$

where $e$ is the terminal object. The conditions that $A$ has to fulfill are encapsulated in the notion of *Gray module* (paragraph 3.1.3.3). Thanks to the Gray cylinder and cone, we can show the following theorem:

**Theorem 3.3.4.2.** *If $A$ is a Gray module, there is a Quillen adjunction between the Ozornova-Rovelli model structure for $\omega$-complicial sets on stratified simplicial sets and stratified Segal precategories enriched in $A$ where the left adjoint sends $[n]$ to $e \star e \star \dots \star e \star \emptyset$*

We will apply this theorem to the case where $A$ is the category of stratified simplicial sets endowed with the model structure for $\omega$-complicial sets, and after tedious work, we get

**Theorem 3.4.3.2.** *Let $n \in \mathbb{N}$. The model structure for $n$-complicial sets is a model of $(\infty, n)$-categories.*

As a corollary we have

**Theorem 3.4.3.14.** *The adjunction between the model structure for complete Segal $\Theta$-spaces and $\omega$-complicial set constructed in [OR22] is a Quillen equivalence.*

13

Introduction

## On the side of theory

In the second part of this thesis, we will adapt the constructions of classical category theory to the case $(\infty, \omega)$. In this part, we will freely use the language of $(\infty, 1)$-categories$^{1}$.

Chapter 4 is devoted to the basic theory of $(\infty, \omega)$-categories. Chapter 5 introduces the notion of *marked* $(\infty, \omega)$-categories and studies *left Cartesian fibrations*. Chapter 6 is dedicated to the *Grothendieck construction, univalence*, the *Yoneda lemma*, and other standard categorical constructions.

Several of these results, or their analogues in the $(\infty, n)$ setting for some integer $n$, are already present in the literature. The case $n = 1$, i.e. that of $(\infty, 1)$-category theory, is now a prolific research field, and it would be impossible to list all the authors who have contributed to it. Nonetheless, we would like to mention Joyal for his pioneering work ([Joy02]), Lurie for his major contribution ([Lur09a]), and Cisinski ([Cis19]) because his approach has deeply inspired the present work.

For the case $n = 2$, the Grothendieck construction as well as lax limits and colimits have been extensively studied by Gagna, Lanari and Harpaz in [GHL20] and [GHL21], as well as by García and Stern in [GS21] and [GS22].

For arbitrary $n$, Grothendieck construction has been described in [Nui21] and [Ras21]. A partial version of the Yoneda lemma is also present in [Ras21], [Hin21], and [Hei20].

**Chapter 4.** This chapter is dedicated to the basic definition of $(\infty, \omega)$-categories. In the first section, we recall some results on factorization systems in presentable $(\infty, 1)$-categories. In the second section, we define $(\infty, \omega)$-categories and give some basic properties. We also define and study *discrete Conduché functor*, which are morphisms having

$^{1}$As there are currently several directions for the formalization of the language of $(\infty, 1)$-categories ([RV22], [RS17], [Nor19], [CNW]), talking about 'the' language of $(\infty, 1)$-categories may be confusing.

In such case, the reader may consider that we are working within the quasi-category Qcat of **T**-small quasi-categories for **T** a Grothendieck universe. This quasi-category may be obtained either using the coherent nerve as described in [Lur09a, chapter 3], or by considering it as the codomain of the universal co-cartesian fibration with **T**-small fibers as done in [CN22]. In both cases, the straightening/unstraightening correspondence provides a morphism

$$\mathrm{N}(\mathrm{Psh}(\Delta)_\mathbf{T}) \rightarrow \mathrm{Qcat}$$

that exhibits Qcat as the quasi-categorical localization of $\mathrm{N}(\mathrm{Psh}(\Delta)_\mathbf{T})$ with respect to the weak equivalences of the Joyal's model structure ([CN22, theorem 8.13]).

The constructions we use to build new objects - (co)limits of functor between quasi-categories, quasi-categories of functor, localization of quasi-categories, sub maximal Kan complex, full sub quasi-category, adjunction, left and right Kan extension, Yoneda lemma - are well documented in the Joyal model structure (see [Lur09a] or [Cis19]), and therefore have direct incarnation in the quasi-category Qcat.

14

the unique right lifting property against units $\mathbb{I}_{n+1} : \mathbf{D}_{n+1} \rightarrow \mathbf{D}_n$ for any integer $n$, and against compositions $\nabla_{k,n} : \mathbf{D}_n \rightarrow \mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$ for any pair of integers $k \leq n$. This notion was originally defined and studied in the context of strict $\omega$-category by Guetta in [Gue18].

**Theorem 4.2.2.9.** *Let $f : C \rightarrow D$ be a discrete Conduché functor. The pullback functor $f^* : (\infty, \omega)\text{-cat}_{/D} \rightarrow (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.*

In the third section, we study Gray operations for $(\infty, \omega)$-categories. We conclude this chapter by proving results of strictification. In particular, we demonstrate the following theorem:

**Theorem 4.3.3.19.** *Let $C$ be an $(\infty, \omega)$-category, $b$ a globular sum, and $f : b \rightarrow C$ any morphism. The $(\infty, \omega)$-categories*

$$1 \stackrel{co}{\star} b \coprod_b C, \quad C \coprod_b b \otimes [1] \quad \text{and} \quad C \coprod_b b \star 1$$

*are strict whenever $C$ is.*

We will also prove the following theorem:

**Theorem 4.3.3.26.** *If $C$ is strict, so are $C \star 1$, $1 \stackrel{co}{\star} C$ and $C \otimes [1]$.*

In the process, we will demonstrate another fundamental equation combining $C \otimes [1]$, $1 \stackrel{co}{\star} C$, $C \star 1$, and $[C, 1]$.

**Theorem 4.3.3.25.** *Let $C$ be an $(\infty, \omega)$-category. The five squares appearing in the following canonical diagram are both cartesian and cocartesian:*

$$\begin{array}{ccc} & C \otimes \{0\} & \longrightarrow & 1 \\ & \downarrow & & \downarrow \\ C \otimes \{1\} & \longrightarrow & C \otimes [1] & \longrightarrow & C \star 1 \\ \downarrow & & \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{co}{\star} C & \longrightarrow & [C, 1] \end{array}$$

*where $[C, 1]$ is the suspension of $C$.*

**Chapter 5.** This chapter is dedicated to the study of *marked* $(\infty, \omega)$-categories, which are pairs $(C, tC)$, where $C$ is an $(\infty, \omega)$-category and $tC := (tC_n)_{n>0}$ is a sequence of full sub $\infty$-groupoids of $C_n$ that include identities and are stable under composition and whiskering with (possibly unmarked) cells of lower dimensions. There are two canonical

15

Introduction

ways to mark an $(\infty, \omega)$-category $C$. In the first, denoted by $C^0$, we mark as little as possible. In the second, denoted by $C^\sharp$, we mark everything.

The first section of the chapter defines these objects and establishes analogs of many results from section 4.2 to this new framework. In particular, the marked Gray cylinder $\_ \otimes [1]^\sharp$ is defined. If $A$ is an $(\infty, \omega)$-category, the underlying $(\infty, \omega)$-category of $A^\sharp \otimes [1]^\sharp$ is $A \times [1]$, and the underlying $(\infty, \omega)$-category of $A^0 \otimes [1]^\sharp$ is $A \otimes [1]$. By varying the marking, and at the level of underlying $(\infty, \omega)$-categories, we "continuously" move from the cartesian product with the directed interval to the Gray tensor product with the directed interval.

The motivation for introducing markings comes from the notion of left (and right) cartesian fibrations. A left cartesian fibration is a morphism between marked $(\infty, \omega)$-categories such that only the marked cells of the codomain have cartesian lifting, and the marked cells of the domain correspond exactly to such cartesian lifting. For example, a left cartesian fibration $X \to A^\sharp$ is just a "usual" left cartesian fibration where we have marked the cartesian lifts of the domain, and every morphism $C^0 \to D^0$ is a left cartesian fibration. This shows that marking plays a very different role here than in the case of marked simplicial sets, where it was there to represent (weak) invertibility. For example, if we had wanted to carry out this work in a complicial-like model category, we would have had to consider bimarked simplicial sets.

After defining and enumerating the stability properties enjoyed by this class of left (and right) cartesian fibration, we give several characterizations of this notion in theorem 5.2.1.26.

The more general subclass of left cartesian fibrations that still behaves well is the class of classified left cartesian fibrations. This corresponds to left cartesian fibrations $X \to A$ such that there exists a cartesian square:

![img-9.jpeg](img-9.jpeg)

where the right vertical morphism is a left cartesian fibration and $A^\sharp$ is obtained from $A$ by marking all cells. In the second section, we prove the following fundamental result:

**Theorem 5.2.2.12.** Let $p : X \to A$ be a classified left cartesian fibration. Then the functor $p^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/A} \to (\infty, \omega)\text{-cat}_{\mathrm{m}/X}$ preserves colimits.

The third subsection is devoted to the proof of the following theorem

**Theorem 5.2.3.3.** Let $A$ be an $(\infty, \omega)$-category and $F : I \to (\infty, \omega)\text{-cat}_{\mathrm{m}/A^\sharp}$ be a diagram that is pointwise a left cartesian fibration. The induced morphism $\operatorname{colim}_I F$ is a left cartesian fibration over $A^\sharp$.

16

In the fourth subsection we study *smooth* and *proper* morphisms and we obtain the following expected result:

**Proposition 5.2.4.16.** *For a morphism $X \rightarrow A^\sharp$, and an object $a$ of $A$, we denote by $X_{/a}$ the marked $(\infty, \omega)$-category fitting in the following cartesian squares.*

![img-10.jpeg](img-10.jpeg)

*We denote by $\perp : (\infty, \omega)\text{-cat}_m \rightarrow (\infty, \omega)\text{-cat}$ the functor sending a marked $(\infty, \omega)$-category to its localization by marked cells.*

(1) *Let $E$, $F$ be two elements of $(\infty, \omega)\text{-cat}_{m/A^\sharp}$ corresponding to morphisms $X \rightarrow A^\sharp$, $Y \rightarrow A^\sharp$, and $\phi : E \rightarrow F$ a morphism between them. We denote by $\mathbf{F}E$ and $\mathbf{F}F$ the left cartesian fiborant replacement of $E$ and $F$.*

*The induced morphism $\mathbf{F}\phi : \mathbf{F}E \rightarrow \mathbf{F}F$ is an equivalence if and only if for any object $a$ of $A$, the induced morphism*

$$\perp X_{/a} \rightarrow \perp Y_{/a}$$

*is an equivalence of $(\infty, \omega)$-categories.*

(2) *A morphism $X \rightarrow A^\sharp$ is initial if and only if for any object $a$ of $A$, $\perp X_{/a}$ is the terminal $(\infty, \omega)$-category.*

Finally, in the last subsection, for a marked $(\infty, \omega)$-category $I$, we define and study a (huge) $(\infty, \omega)$-category $\underline{\mathrm{LCart}}^c(I)$ that has classified left cartesian fibrations as objects and morphisms between classified left cartesian fibrations as arrows.

**Chapter 6.** This chapter aims to establish analogs of the fundamental categorical constructions to the $(\infty, \omega)$ case. In the first section, we define the $(\infty, \omega)$-category of small $(\infty, \omega)$-categories $\underline{\omega}$ (paragraph 6.1.1.15), and we prove a first incarnation of the Grothendieck construction:

**Corollary 6.1.2.21.** *Let $\underline{\omega}$ be the $(\infty, \omega)$-category of small $(\infty, \omega)$-categories, and $A$ an $(\infty, \omega)$-category. There is an equivalence*

$$\int_A : \mathrm{Hom}(A, \underline{\omega}) \rightarrow \tau_0 \mathrm{LCart}(A^\sharp).$$

*where $\tau_0 \mathrm{LCart}(A^\sharp)$ is the $\infty$-groupoid of left cartesian fibrations over $A^\sharp$ with small fibers.*

17

Introduction

Given a functor $f : A \to \underline{\omega}$, the left cartesian fibration $\int_A f$ is a colimit (computed in $(\infty, \omega)$-cat$_{\text{m}/A^{\sharp}}$) of a simplicial object whose value on $n$ is of shape

$$\coprod_{x_0, \dots, x_n : A_0} X(x_0)^{\flat} \times \hom_A (x_0, \dots, x_n)^{\flat} \times A_{x_n/}^{\sharp} \to A^{\sharp}$$

This formula is similar to the one given in [GHN] for $(\infty, 1)$-categories, and to the one given in [War11] for strict $\omega$-categories.

We also prove a univalence result:

**Corollary 6.1.3.31.** *Let $I$ be a marked $(\infty, \omega)$-category. We denote by $I^{\sharp}$ the marked $(\infty, \omega)$-category obtained from $I$ by marking all cells and $\iota : I \to I^{\sharp}$ the induced morphism. There is a natural correspondence between*

(1) functors $f : I \otimes [1]^{\sharp} \to \underline{\omega}^{\sharp}$,
(2) pairs of small left cartesian fibration $X \to I^{\sharp}$, $Y \to I^{\sharp}$ together with diagrams

![img-11.jpeg](img-11.jpeg)

Recall that if $I$ is of shape $B^{\sharp}$, then the underlying $(\infty, \omega)$-category of $B^{\sharp} \otimes [1]^{\sharp}$ is $B \times [1]$, and if $I$ is of shape $B^{\flat}$, the underlying $(\infty, \omega)$-category of $B^{\flat} \otimes [1]^{\sharp}$ is $B \otimes [1]$. On the other hand, if $I$ is $B^{\sharp}$, $\iota$ is the identity, and $\phi$ then preserves all cartesian liftings, and if $I$ is $B^{\flat}$, $\phi$ doesn't need to preserve cartesian liftings.

By varying the marking, we can continuously move from the cartesian product with the interval to the Gray product with the interval on one side, and on the other side, we can continuously move from morphisms between left cartesian fibrations that preserve the marking to the ones that do not preserve it *a priori*.

Eventually, we also get an $(\infty, \omega)$-functorial Grothendieck construction, expressed by the following corollary:

**Corollary 6.1.4.3.** *Let $A$ be a $\mathbf{U}$-small $(\infty, \omega)$-category. Let $\underline{\text{LCart}}(A^{\sharp})$ be the $(\infty, \omega)$-category of small left cartesian fibrations over $A^{\sharp}$. There is an equivalence*

$$\underline{\text{Hom}}(A, \underline{\omega}) \sim \underline{\text{LCart}}(A^{\sharp})$$

natural in $A$.

18

In the second section of this chapter, for a locally small $(\infty, \omega)$-category $C$, we construct the Yoneda embedding, which is a functor $y : C \to \widehat{C}$ where $\widehat{C} := \underline{\mathrm{Hom}}(C^t, \underline{\omega})$. We prove the Yoneda lemma:

**Theorem 6.2.1.16.** *The Yoneda embedding is fully faithful.*

**Theorem 6.2.1.18.** *Let $C$ be an $(\infty, \omega)$-category. There is an equivalence between the functor*

$$\mathrm{hom}_{\widehat{C}}(y_\_, \underline{\phantom{0}}) : C^t \times \widehat{C} \to \underline{\omega}$$

*and the functor*

$$ev : C^t \times \widehat{C} \to \underline{\omega}.$$

In the last three sections, we use these results to study and demonstrate the basic properties of adjunctions, lax (co)limits, and left Kan extensions.

We begin by studying adjunctions, and we establish the following expected result.

**Theorem 6.2.2.9.** *Let $u : C \to D$ and $v : D \to C$ be two functors between locally $\mathbf{U}$-small $(\infty, \omega)$-categories. The two following are equivalent.*

(1) *The pair $(u, v)$ admits an adjoint structure.*
(2) *Their exists a pair of natural transformations $\mu : id_C \to vu$ and $\epsilon : uv \to id_D$ together with equivalences $(\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u$ and $(v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v$.*

In the next subsection, given a morphism $f : I \to C^\sharp$ between marked $(\infty, \omega)$-categories, we define the notion of lax colimit and lax limit for the functor $f$. If $f$ admits such a lax colimit, for any 1-cell $i : a \to b$ in $I$, we have a triangle

![img-12.jpeg](img-12.jpeg)

If $i$ is marked, the preceding 2-cell is an equivalence. For any 2-cell $u : i \to j$, we have a diagram

![img-13.jpeg](img-13.jpeg)

If $u$ is marked, the 3-cell is an equivalence. We can continue these diagrams in higher dimensions and we have similar assertions for lax limits. The marking therefore allows us to play on the "lax character" of the universal property that the lax colimit must verify.

After providing several characterizations of lax colimits and limits, we prove the following result:

19

Introduction

**Theorem 6.2.3.24.** *Let $C$ be a $\mathbf{U}$-small $(\infty, \omega)$-category. Let $f$ be an object of $\widehat{C}$. We define $C_{/f}^{\sharp}$ as the following pullback*

$$\begin{array}{ccc} C_{/f}^{\sharp} & \longrightarrow & \widehat{C}_{/f}^{\sharp} \\ \downarrow & & \downarrow \\ C^{\sharp} & \xrightarrow[y^{\sharp}]{} & \widehat{C}^{\sharp} \end{array}$$

*The colimit of the functor $\pi : C_{/f}^{\sharp} \to C^{\sharp} \xrightarrow{y^{\sharp}} \widehat{C}^{\sharp}$ is $f$.*

We conclude this chapter by studying Kan extensions.

## Notice of authority

The chapter 2 is a shorter version of the preprint [Lou22a]. Chapter 3 is almost identical to the preprint [Lou22b]. During this thesis, two other papers were written: [Lou21] (in progress of publication at the SMF) and [HL23] (in collaboration with Simon Henry). Although the topics are similar, the questions addressed are quite different, and these papers are thus not included in the present text.

20

# Preliminaries

21



# Chapter 1

## The category of $(0, \omega)$-categories

### Contents

|  **1.1** | **Basic constructions** | **25**  |
| --- | --- | --- |
|  1.1.1 | $(0, \omega)$-Categories | 25  |
|  1.1.2 | The category $\Theta$ | 29  |
|  1.1.3 | The link between presheaves on $\Theta$ and on $\Delta[\Theta]$ | 34  |
|  **1.2** | **Gray Operations** | **40**  |
|  1.2.1 | Recollection on Steiner theory | 40  |
|  1.2.2 | Gray operations on augmented directed complexes | 47  |
|  1.2.3 | Gray operations on $(0, \omega)$-categories | 53  |

The first section is devoted to the definition of $(0, \omega)$-categories and of the category $\Theta$ of Joyal. We also show that the category $\Theta$ presents the category of $(0, \omega)$-categories, and we also exhibit an other presentation of this category (corollary 1.1.3.4).

The second section begins with a review of Steiner theory, which is an extremely useful tool for providing concise and computational descriptions of $(0, \omega)$-categories. Following Ara and Maltsiniotis, we employ this theory to define the Gray tensor product, denoted by $\otimes$, in $(0, \omega)$-categories. We then introduce the Gray operations, starting with the Gray cylinder $\_ \otimes [1]$ which is the Gray tensor product with the directed interval $[1] := 0 \rightarrow 1$. Then, we have the Gray cone and Gray $\circ$-cone, denoted by $\_ \star 1$ and $1 \stackrel{\circ}{\star} \_,$ that send an

23

CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

(0, ω)-category C onto the following pushouts:

![img-14.jpeg](img-14.jpeg)

We also present a formula that illustrates the interaction between the suspension and the Gray cylinder. As this formula plays a crucial role in both Part I and Part II, we provide its intuition at this stage.

If A is any (0, ω)-category, the suspension of A, denoted by [A, 1], is the (0, ω)-category having two objects - denoted by 0 and 1- and such that

$$\operatorname{Hom}_{[A,1]}(0, 1) := A, \quad \operatorname{Hom}_{[A,1]}(1, 0) := \emptyset, \quad \operatorname{Hom}_{[A,1]}(0, 0) = \operatorname{Hom}_{[A,1]}(1, 1) := \{id\}.$$

We also define [1] ∨ [A, 1] as the gluing of [1] and [A, 1] along the 0-target of [1] and the 0-source of [A, 1]. We define similarly [A, 1] ∨ [1]. These two objects come along with whiskerings:

$$\nabla : [A, 1] \rightarrow [1] \vee [A, 1] \quad \text{and} \quad \nabla : [A, 1] \rightarrow [A, 1] \vee [1]$$

that preserve the extremal objects.

The (0, ω)-category [1] ⊗ [1] is induced by the diagram:

![img-15.jpeg](img-15.jpeg)

and is then equal to the colimit of the following diagram:

$$[1] \vee [1] \xleftarrow{\nabla} [1] \hookrightarrow [[1], 1] \hookleftarrow [1] \xrightarrow{\nabla} [1] \vee [1].$$

The (0, ω)-category [[1], 1] ⊗ [1] is induced by the diagram:

![img-16.jpeg](img-16.jpeg)

and is then equal to the colimit of the following diagram:

$$[1] \vee [[1], 1] \xleftarrow{\nabla} [[1] \otimes \{0\}, 1] \hookrightarrow [[1] \otimes [1], 1] \hookleftarrow [[1] \otimes \{1\}, 1] \xrightarrow{\nabla} [[1], 1] \vee [1]$$

We prove a formula that combines these two examples:

24

1.1. BASIC CONSTRUCTIONS

**Theorem 1.2.3.13.** *In the category of $(0, \omega)$-categories, there exists an isomorphism, natural in $A$, between $[A, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\triangledown} [A \otimes \{0\}, 1] \longrightarrow [A \otimes [1], 1] \longleftarrow [A \otimes \{1\}, 1] \xrightarrow{\triangledown} [A, 1] \vee [1]$$

We also provide similar formulas for the *Gray cone* and the *Gray $\circ$-cone*.

**Theorem 1.2.3.14.** *There is a natural identification between $1 \stackrel{\circ\circ}{\star} [A, 1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\triangledown} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $[A, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\circ\circ}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\triangledown} [A, 1] \vee [1]$$

## 1.1 Basic constructions

### 1.1.1 $(0, \omega)$-Categories

**1.1.1.1.** A *globular set* is a presheaf on the *category of globes* G, which is the category induces by the diagram

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

with the relations $i_n^+ i_{n-1}^\epsilon = i_n^- i_{n-1}^\epsilon$ for any $n > 0$ and $\epsilon \in \{+, -\}$. We also denote by $i_k^\epsilon$ the map $\mathbf{D}_k \to \mathbf{D}_n$ for $k < n$ obtained by composing any string of arrows ending with $i_k^\epsilon$. These and the identity arrows are the only maps in the category G.

If $X$ is a globular set, one denotes by $X_n$ the set $X(\mathbf{D}_n)$. Its elements are called *n-cells*. The 0-cells are sometimes called *objects*. The maps $X_n \to X_k$ induced by $i_k^\epsilon : \mathbf{D}_k \to \mathbf{D}_n$ is denoted by $\pi_k^\epsilon$.

# **1.1.1.2.** An $\omega$-*category* is a globular set $X$ together with

(1) operations of *compositions*

$$X_n \times_{X_k} X_n \to X_n \quad (0 \le k < n)$$

which associate to two $n$-cells $(x, y)$ verifying $\pi_k^-(x) = \pi_k^+(y)$, a $n$-cells $x \circ_k y$,

25

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

(2) as well as units

\[
X _ {n} \rightarrow X _ {n + 1}
\]

which associate to an \(n\)-cell \(x\), a \((n + 1)\)-cell \(\mathbb{I}_x\),

and satisfying the following axioms:

(1) \(\forall x\in X_n,\pi_n^\epsilon (\mathbb{I}_x) = x.\)
(2) \(\pi_k^+ (x\circ_ny) = \pi_k^+ (x)\) and \(\pi_k^- (x\circ_ny) = \pi_k^- (y)\) whenever the composition is defined and \(k\leqslant n\)
(3) \(\pi_k^\epsilon (x\circ_ny) = \pi_k^\epsilon (x)\circ_n\pi_k^\epsilon (y)\) whenever the composition is defined and \(k > n\)
(4) \(x\circ_{n}\mathbb{I}_{\pi_{n}^{-}x} = x\) and \(\mathbb{I}_{\pi_n^+ x}\circ_nx = x.\)
(5) \((x\circ_{n}y)\circ_{n}z = x\circ_{n}(y\circ_{n}z)\) as soon as one of these is defined.
(6) If \( k < n \)

\[
(x \circ_ {n} y) \circ_ {k} (z \circ_ {n} w) = (x \circ_ {k} z) \circ_ {n} (y \circ_ {k} w)
\]

when the left-hand side is defined.

A \(n\)-cell \(a\) is non trivial if is not in the image of the application \(\mathbb{I}: X_{n-1} \to X_n\).

A morphism of  \( \omega \) -categories is a map of globular sets commuting with both operations. The category of  \( \omega \) -categories is denoted by  \( \omega \) -cat.

1.1.1.3. By abuse of notation, we also denote by  \( D_{n} \)  the  \( \omega \) -category that admits for any k < n only two k-non-trivial cells, denoted by  \( e_{k}^{-} \)  and  \( e_{k}^{+} \) , and a single n-non-trivial cell, denoted by  \( e_{n} \)  verifying :

\[
\pi_ {l} ^ {-} (e _ {k} ^ {\epsilon}) = e _ {l} ^ {-} \quad \pi_ {l} ^ {+} (e _ {k} ^ {\epsilon}) = e _ {l} ^ {+} \quad \text {for} l \leq k <   n
\]

\[
\pi_ {l} ^ {-} (e _ {n}) = e _ {l} ^ {-} \quad \pi_ {l} ^ {+} (e _ {n}) = e _ {l} ^ {+} \quad \mathrm{for} l \leq n
\]

Remark furthermore that the  \( \omega \) -category  \( D_{n} \)  represents n-cells, in the sense that  \( \operatorname{Hom}(\mathbf{D}_{n}, C) \cong C_{n} \) . We will not make the difference between n-cells and the corresponding morphism of  \( D_{n} \to C \) .

The \(\omega\)-category \(\partial \mathbf{D}_n\) is obtained from \(\mathbf{D}_n\) by removing the \(n\)-cell \(e_n\). We thus have a morphism

\[
i _ {n}: \partial \mathbf {D} _ {n} \to \mathbf {D} _ {n}.
\]

Note that \(\partial \mathbf{D}_0 = \emptyset\).

26

1.1. BASIC CONSTRUCTIONS

**1.1.1.4.** We say that an $(0, \omega)$-category $X$ is a *polygraph* if it can be constructed from the empty $(0, \omega)$-category by freely adding arrows with specified source and target. That is if $X$ can be obtained as a transfinite composition $\emptyset = X_0 \rightarrow X_1 \rightarrow \cdots \rightarrow X_i \rightarrow \text{colim } X_i = X$ where for each $i$, the map $X_i \rightarrow X_{i+1}$ is a pushout of $\coprod_S \partial \mathbf{D}_n \rightarrow \coprod_S \mathbf{D}_{n+1}$.

An arrow of a polygraph is said to be a *generator* if it is one of the arrows that has been freely added at some stage.

Each cell in a polygraph can be written as an iterated composite of generators or iterated unit of generators (not necessarily in a unique way). For a $n$-cell $f$, the set of generators of dimension $n$ that appear in such an expression (and even the number of times they appear) is the same for all such expressions. As a consequence, a iterated composition of non trivial cells is always non trivial.

**1.1.1.5.** For any subset $S$ of $\mathbb{N}^*$, we define the functor $(\_)^S : \omega\text{-cat} \rightarrow \omega\text{-cat}$ sending a $\omega$-category $C$ to the category $C^S$ such that for any $n$, there is an isomorphism $C_n \rightarrow C_n^S$ that sends every $n$-cell $f$ to a cell $\overline{f}$ fulfilling

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^+(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^-(f)}$$

if $i \in S$ and

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^-(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^+(f)}$$

if $i \notin S$. These functors are called *dualities* as they are inverse of themselves. Even if there are plenty of them, we will be interested in only a few of them. In particular, we have the *odd duality* $(\_)^{op}$, corresponding to the set of odd integer, the *even duality* $(\_)^{co}$, corresponding to the subset of non negative even integer, the *full duality* $(\_)^\circ$, corresponding to $\mathbb{N}^*$ and the *transposition* $(\_)^t$, corresponding to the singleton $\{1\}$. Eventually, we have equivalences

$$((\_)^{co})^{op} \sim (\_)^\circ \sim ((\_)^{op})^{co}.$$

**1.1.1.6.** Let $\text{Psh}(\text{G})_{\bullet,\bullet}$ be the category of globular set with two distinguished points, i.e. of triples $(X, a, b)$ where $a$ and $b$ are elements of $X_0$. Let $[\_, 1] : \text{G} \rightarrow \text{Psh}(\text{G})_{\bullet,\bullet}$ be the functor sending $\mathbf{D}_n$ on $(\mathbf{D}_{n+1}, \{0\}, \{1\})$ and $i_n^\epsilon$ on $i_{n+1}^\epsilon$. This induces a functor $[\_, 1] : \text{Psh}(\text{G}) \rightarrow \text{Psh}(\text{G})$ that we call the *suspension*. We leave it to the reader to check that whenever $C$ has a structure of $\omega$-category, $[C, 1]$ inherits one from it. This functor then induces a functor

$$[\_, 1] : \omega\text{-cat} \rightarrow \omega\text{-cat}$$

that we calls again the *suspension*. Eventually, we denote by $i_0^- : \{0\} \rightarrow [C, 1]$ (resp. $i_0^+ : \{1\} \rightarrow [C, 1]$) the morphism corresponding to the left point (resp. to the right point).

27

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

For an integer $n$, we define by induction the functor $\Sigma^n : \mathrm{Psh}(\mathrm{G}) \to \mathrm{Psh}(\mathrm{G})$ with the formula:

$$\Sigma^0 := id \qquad \Sigma^{n+1} := \Sigma^n[\_, 1].$$

**1.1.1.7.** Let $n$ be a non null integer. A $n$-cells $f : s \to t$ is an *equivalence* if there exists $n$-cells $g : t \to s$ and $g' : t \to s$ such that

$$f \circ_{n-1} g = \mathbb{I}_t \qquad g \circ_{n-1} f = \mathbb{I}_s$$

A $(0, \omega)$-category is an $\omega$-category whose only equivalences are the identities. These objects are called *Gaunt $\omega$-categories* in [BSP21] and *rigid $\omega$-categories* in [Rez10]. Remark that $(0, \omega)$-categories are stable under suspensions and dualities. We then define $(0, \omega)$-cat as the full subcategory of $\omega$-cat whose objects are the $(0, \omega)$-categories.

**1.1.1.8.** Let $n$ be an integer. An $(0, n)$-category is an $(0, \omega)$-category whose cell of dimension strictly higher than $n$ are units. The category of $n$-categories is denoted by $(0, n)$-cat and is the full subcategory of $(0, \omega)$-cat whose objects are $(0, n)$-categories.

Remark that the category $(0, n)$-cat is the localization of $(0, \omega)$-cat along morphisms $\mathbf{D}_k \to \mathbf{D}_n$ for $k \geq n$. We then have for any $n$ an adjunction

$$i_n : (0, n)\text{-cat} \xrightarrow[\downarrow]{} (0, \omega)\text{-cat} : \tau_n$$

The right adjoint is called the $n$-truncation. For any $n$, we define the colimit preserving functor $\tau_n^i : (0, \omega)\text{-cat} \to (0, n)\text{-cat}$, called the *intelligent $n$-truncation*, sending $\mathbf{D}_k$ on $\mathbf{D}_{\min(n,k)}$. The functor $\tau_n^i$ fits in an adjunction

$$\tau_n^i : (0, \omega)\text{-cat} \xrightarrow[\downarrow]{} (0, n)\text{-cat} : i_n$$

We will identify objects of $(0, n)$-cat with their image in $(0, \omega)$-cat and we will then also note by $\tau_n$ and $\tau_n^i$ the composites $i_n \tau_n^i$ and $i_n \tau_n^i$.

**1.1.1.9.** The family of truncation functor induces a sequence

$$\dots \to (0, n+1)\text{-cat} \xrightarrow{\tau_n} (0, n)\text{-cat} \to \dots \to (0, 1)\text{-cat} \xrightarrow{\tau_0} (0, 0)\text{-cat}.$$

The canonical morphism

$$(0, \omega)\text{-cat} \to \lim_{n \in \mathbb{N}} (0, n)\text{-cat},$$

that sends an $(0, \omega)$-category $C$ to the sequence $(\tau_n C, \tau_n \tau_{n+1} C \cong \tau_n C)$, has an inverse given by the functor

$$\operatorname{colim}_{\mathbb{N}} : \lim_{n \in \mathbb{N}} (0, n)\text{-cat} \to (0, \omega)\text{-cat}$$

28

1.1. BASIC CONSTRUCTIONS

that sends a sequence \((C_n, \tau_n C_{n+1} \cong C_n)\) to the colimit of the induced sequence:

\[
i _ {0} C _ {0} \rightarrow i _ {1} C _ {1} \rightarrow \dots \rightarrow i _ {n} C _ {n} \rightarrow \dots
\]

We then have an equivalence

\[
(0, \omega) \text {-cat} \cong \lim _ {n: \mathbb {N}} (0, n) \text {-cat}.
\]

#### 1.1.2 The category \(\Theta\)

1.1.2.1. Let n be a non negative integer and  \( a := \{a_{0}, a_{1}, ..., a_{n-1}\} \)  a sequence of  \( (0, \omega) \) -categories. We denote  \( [a, n] \)  the colimit of the following diagram:

![img-17.jpeg](img-17.jpeg)

1.1.2.2. We define  \( \Theta \)  as the smallest full subcategory of  \( (0,\omega) \) -cat that includes the terminal  \( (0,\omega) \) -category [0], and such that for any non negative integer n, and any finite sequence  \( a := \{a_{0}, a_{1}, ..., a_{n-1}\} \)  of objects of  \( \Theta \) , it includes the  \( (0,\omega) \) -category  \( [a, n] \) . Objects of  \( \Theta \)  are called globular sum.

Remark that a morphism \( g:[\mathbf{a},n]\to [\mathbf{b},m] \) is exactly the data of a morphism \( f:[n]\to [m] \), and for any integer \( i \), a morphism

\[
a _ {i} \rightarrow \prod_ {f (i) \leq k <   f (i + 1)} b _ {k}.
\]

Example 1.1.2.3. For any n,  \( D_{n} \)  is a globular sum. The  \( (0,\omega) \) -category induced by the  \( \omega \) -graph

![img-18.jpeg](img-18.jpeg)

is a globular sum.

1.1.2.4. For a globular sum \(a\) and an integer \(n\), we define \([a, n] := [\{a, a, ..., a\}, n]\). For a sequence of integer \(\{n_0, .., n_k\}\) and a sequence of globular sum \(\{a_0, .., a_k\}\), we define \([a_0, n_0] \vee [a_1, n_1] \vee ... \vee [a_k, n_k]\) as the globular sum \([\{a_0, .., a_1, ..., a_k, ...\}, n_0 + n_1 + ... + n_k]\).

We denote by [0] the terminal \((\infty, \omega)\)-category, and \([n]\) the globular sum \([[0], n]\). We have a fully faithful functor \(\Delta \to \Theta\) sending \([n]\) onto \([n]\).

29

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

**1.1.2.5.** A *Reedy category* is a small category $A$ equipped with two subcategories $A_+$, $A_-$ and a *degree* function $d : ob(A) \to \mathbb{N}$ such that:

(1) for every non identity morphism $f : a \to b$, if $f$ belongs to $A_-$, $d(a) > d(b)$, and if $f$ belongs to $A_+$, $d(a) < d(b)$.

(2) every morphism of $A$ uniquely factors as a morphism of $A_-$ followed by a morphism of $A_+$.

A Reedy category $A$ is *elegant* if for any presheaf $X$ on $A$, for any $a \in A$ and any $c \in X(a)$, there exists a unique morphism $f : a \to a' \in A_-$ and a unique non degenerate object $c' \in X(a')$ such that $c = X(f)(c')$.

**Proposition 1.1.2.6.** *Let $X$ be a presheaf on an elegant Reedy category $A$. The category $A_{/X}$ is an elegant Reedy category.*

*Proof.* We have a canonical projection $\pi : A_{/X} \to A$. A morphism is positive (resp. negative) if it's image by $\pi$ is. The degree of an element $c$ of $A_{/X}$ is the degree of $\pi(c)$. We leave it to the reader to check that this endows $A_{/X}$ with a structure of Reedy category.

The fact that $A_{/X}$ is elegant is a direct consequence of the isomorphism $\mathrm{Psh}(A_{/X}) \cong \mathrm{Psh}(A)_{/X}$. $\square$

**1.1.2.7.** We define by induction the *dimension* of a globular sum $a$, denoted by $|a|$. The dimension of $[0]$ is $0$, and the dimension of $[\mathbf{a}, n]$ is the maximum of the set $\{|a_k| + 1\}_{k < n}$. We denote by $\Theta_n$ the full subcategory of $\Theta$ whose objects are the globular sum of dimension inferior or equal to $n$.

**Proposition 1.1.2.8** (Berger, Bergner-Rezk). *The category $\Theta$ and, for any $n \in \mathbb{N}$, the category $\Theta_n$ are elegant Reedy category.*

*A morphism $g : [\mathbf{a}, n] \to [\mathbf{b}, m]$ is degenerate (i.e a morphism of $\Theta_-$) if the corresponding morphism $f : [n] \to [m]$ is a degenerate morphism of $\Delta$, and for any $i < n$ and any $f(i) \leq k < f(k+1)$, the corresponding morphism $a_i \to b_k$ is degenerate. Furthermore, a morphism is degenerate if and only if it is a epimorphism in $\mathrm{Psh}(\Theta)$.*

*A morphism is in $\Theta^+$ if and only if it is a monomorphism in $\mathrm{Psh}(\Theta)$.*

*Proof.* The Reedy structure is a consequence of lemma 2.4 of [Ber02]. The fact that for any $n < \omega$, $\Theta_n$ is elegant is [BR13b, corollary 4.5.]. As for any $n < \omega$, the inclusion $\Theta_n \to \Theta$ preserves strong pushout, the characterization of elegant Reedy category given by [BR13b, proposition 3.8.] implies that $\Theta$ is also elegant. $\square$

30

1.1. BASIC CONSTRUCTIONS

1.1.2.9. We recall that a morphism $g : [\mathbf{a}, n] \to [\mathbf{b}, m]$ is exactly the data of a morphism $f : [n] \to [m]$, and for any integer $i$, a morphism

$$a_i \to \prod_{f(i) \le k < f(i+1)} b_k.$$

The morphism $g$ is *globular* if for any $k < n$, $f(k+1) = f(k) + 1$ and the morphism $a_k \to b_k$ is globular. The morphism $g$ is *algebraic* if it cannot be written as a composite $ig'$ where $i$ is a globular morphism.

**Example 1.1.2.10.** The morphism

![img-19.jpeg](img-19.jpeg)

is globular. This is not the case for the morphism

![img-20.jpeg](img-20.jpeg)

that sends the 2-cell of the left globular sum on the 1-composite of the two 2-cells of the right globular sum.

**Proposition 1.1.2.11** ([Ara10, Proposition 3.3.10]). *Every morphism in $\Theta$ can be factored uniquely in an algebraic morphism followed by a globular morphism.*

1.1.2.12. We define for any globular sum $a$ and any integer $n$ a globular sum $s_n(a) :=: t_n(a)$ and two morphisms

$$s_n(a) \to a \leftarrow t_n(a).$$

We first set $s_0(a) :=: t_0(a) := [0]$. The inclusion $s_0(a) \to a$ corresponds to the initial point and $t_0(a) \to a$ to the terminal point. For $n > 0$, we define $s_n([\mathbf{a}, n]) :=: t_n([\mathbf{a}, n]) := [s_{n-1}(\mathbf{a}), n]$ where $s_{n-1}(\mathbf{a})$ is the sequence $\{s_{n-1}(a_i)\}_{i<n}$.

31

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

Example 1.1.2.13. If a is the globular sum of example 1.1.2.3, we have:

![img-21.jpeg](img-21.jpeg)

1.1.2.14. The morphism  \( [\_, 1] : \Theta \to \Theta \)  induces by extension by colimit a functor

\[
[ \_, 1 ]: \mathrm{Psh} (\Theta) \to \mathrm{Psh} (\Theta).
\]

We define by induction on \(a\) a \(\Theta\)-presheaf \(\mathrm{Sp}_a\) and a morphism \(\mathrm{Sp}_a \to a\). If \(a\) is [0], we set \(\mathrm{Sp}_{[0]} := [0]\). For \(n > 0\), we define \(\mathrm{Sp}_{[\mathbf{a}, n]}\) as the set valued presheaf on \(\Theta\) obtained as the colimit of the diagram

![img-22.jpeg](img-22.jpeg)

We define  \( E^{eq} \)  as the set valued preheaves on  \( \Delta \)  obtained as the colimit of the diagram

![img-23.jpeg](img-23.jpeg)

For any integer n, the morphism  \( \Sigma^{n}:\Theta\to\Theta \) , which is the n-iteration of  \( [\_,1] \) , induces by colimit a functor

\[
\Sigma^ {n}: \mathrm{Psh} (\Theta) \to \mathrm{Psh} (\Theta).
\]

We define two sets of morphisms of  \( \mathrm{Psh}(\Theta) \) :

\[
\mathrm{W} _ {\text {Seg}} := \left\{\mathrm{Sp} _ {a} \rightarrow a, a \in \Theta \right\} \quad \mathrm{W} _ {\text {Sat}} := \left\{\Sigma^ {n} E ^ {e q} \rightarrow \mathbf {D} _ {n} \right\}
\]

and we set

\[
\mathrm{W} := \mathrm{W} _ {\mathrm{Seg}} \cup \mathrm{W} _ {\mathrm{Sat}}.
\]

For any \(n\), we also define

\[
\mathrm{W} _ {n} := \mathrm{W} \cap \Theta_ {n}.
\]

32

1.1. BASIC CONSTRUCTIONS

1.1.2.15. We recall that for an integer $n$ and a globular sum $a$, we defined $[a, n] := [\{a, a, \dots, a\}, n]$. This defines a functor $i : \Delta[\Theta] \to \Theta$ sending $(n, a)$ on $[a, n]$ where $\Delta[\Theta]$ is the following pushout of category:

![img-24.jpeg](img-24.jpeg)

For the sake of simplicity, we will also denote by $[a, n]$ (resp. $[n]$) the object of $\Delta[\Theta]$ corresponding to $(n, a)$ (resp. to $(n, [0])$). We define two sets of morphisms:

$$\mathrm{M}_{\mathrm{Seg}} := \{[a, \mathrm{Sp}_n] \to [a, n], \ a : \Theta\} \cup \{[f, 1], \ f \in \mathrm{W}_{\mathrm{Seg}}\}$$

$$\mathrm{M}_{\mathrm{Sat}} := \{E^{eq} \to [0]\} \cup \{[f, 1], \ f \in \mathrm{W}_{\mathrm{Sat}}\}$$

and we set

$$\mathrm{M} := \mathrm{M}_{\mathrm{Seg}} \cup \mathrm{M}_{\mathrm{Sat}}.$$

For an integer $n$, we define $\Delta[\Theta_n]$ as the following pushout of category:

![img-25.jpeg](img-25.jpeg)

and the functor $i$ induces a functor $\Delta[\Theta_n] \to \Theta_{n+1}$. For any $n$, we define

$$\mathrm{M}_n := \mathrm{M} \cap \Delta[\Theta_n].$$

1.1.2.16. Let $C$ be a presentable category and $S$ a set of monomorphisms with small codomains. An object $x$ is $S$-local if for any $i : a \to b \in S$, the induced functor $\mathrm{Hom}(i, x) : \mathrm{Hom}(b, x) \to \mathrm{Hom}(a, x)$ is an isomorphism. We define $C_S$ as the full subcategory of $C$ composed of $S$-local objects. According to theorem 4.1.3.3, the inclusion $\iota : C_S \to C$ is part of an adjunction

$$\mathbf{F}_S : C \xrightarrow[\longleftarrow]{} C_S : \iota$$

Moreover, the theorem op cit also states that $\mathbf{F}_S : C \to C_S$ is the localization of $C$ by the smallest class of morphisms containing $S$ and stable under composition and colimit.

Suppose given an other category $D$ fitting in an adjunction

$$F : C \xrightarrow[\longleftarrow]{} D : G$$

33

CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

with unit ν and counit ε, as well as a set of morphisms T of D such that F(S) ⊂ T. By adjunction property, it implies that for any T-local object d ∈ D, G(d) is S-local. The previous adjunction induces a derived adjunction

$$\mathbf{L}F : C_S \xrightarrow{\perp} D_T : \mathbf{R}G$$

where LF is defined by the formula c ↦ F_T F(c) and RG is the restriction of G to D_T. The unit is given by ν ∘ F_S and the counit by the restriction of ε to D_T.

1.1.2.17. The functor i : Δ[Θ] → Θ defined in paragraph 1.1.2.15 induces an adjunction:

$$i_! : \mathrm{Psh}(\Delta[\Theta]) \xrightarrow{\longleftarrow} \mathrm{Psh}(\Theta) : i^*$$

where the left adjoint is the left Kan extension of the functor Δ[Θ] → Θ → Psh(Θ). Remark that there is an obvious inclusion i_!(M) ⊂ W. In virtue of the last paragraph, this induces an adjunction between derived categories:

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta])_\mathrm{M} \xrightarrow{\longleftarrow} \mathrm{Psh}(\Theta)_\mathrm{W} : \mathbf{R}i^* \tag{1.1.2.18}$$

The corollary 12.3 of [BSP21] and the corollary 1.1.3.4 (which is proved in the next section) induce equivalences

$$(0, \omega)\text{-cat} \cong \mathrm{Psh}(\Theta)_\mathrm{W} \cong \mathrm{Psh}(\Delta[\Theta])_\mathrm{M}.$$

Similarly, for any integer n, the inclusion i : Δ[Θ_n] → Θ_{n+1} induces an adjunction between derived categories:

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta]_n)_{\mathrm{M}_n} \xrightarrow{\longleftarrow} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_n} : \mathbf{R}i^* \tag{1.1.2.19}$$

and corollary 12.3 of [BSP21] and corollary 1.1.3.4 induce equivalences

$$(0, n+1)\text{-cat} \cong \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n+1}} \cong \mathrm{Psh}(\Delta[\Theta_n])_{\mathrm{M}_{n+1}}.$$

### 1.1.3 The link between presheaves on Θ and on Δ[Θ]

1.1.3.1. A class of monomorphism T is precocomplete if

- It is closed by transfinite compositions and pushouts.
- It is closed by left cancellation, i.e for any pair of composable morphisms f and g, if gf and f are in S, so is g.
- For any elegant Reedy category A, and any functor F : A → Arr(C) such that the induced morphism colim_{∂a} F → F(a) is a monomorphism for any object a, and such that F is pointwise in S, then colim_A F is in S.

For a set of morphisms S, we denote S̅ the smallest precocomplete class of morphisms containing S.

34

1.1. BASIC CONSTRUCTIONS

1.1.3.2. The aim of this subsection is to demonstrate the following proposition:

**Theorem 1.1.3.3.** *For any $a \in \Theta$ and $b \in \Delta[\Theta]$, morphisms $i_!i^*a \to a$ and $b \to i^*i_!b$ are respectively in $\overline{\mathrm{W}}$ and $\overline{\mathrm{M}}$.*

As a corollary, we directly have:

**Corollary 1.1.3.4.** *The adjunction*

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta])_\mathrm{M} \xleftarrow{\quad} \mathrm{Psh}(\Theta)_\mathrm{W} : \mathbf{R}i^*$$

*given in (1.1.2.18) is an adjoint equivalence. For any integer $n$, the adjunction*

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta]_n)_{\mathrm{M}_n} \xleftarrow{\quad} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_n} : \mathbf{R}i^*$$

*given in (1.1.2.19) is an adjoint equivalence.*

*Proof.* The first assertion is a consequence of theorem 1.1.3.3 and of the fact that $\overline{\mathrm{W}}$ (resp. $\overline{\mathrm{M}}$) is a included in the smallest class containing W (resp. M) and stable by two out of three and colimits. We prove the second assertion similarly. $\square$

1.1.3.5. We denote by

$$[\_, \_] : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$$

the extension by colimit of the functor $\Theta \times \Delta \to \mathrm{Psh}(\Delta[\Theta])$ sending $(a, n)$ onto $[a, n]$. For an integer $n$, we denote

$$[\_, n] : \mathrm{Psh}(\Theta)^n \to \mathrm{Psh}(\Theta)$$

the extension by colimit of the functor $\Theta^n \to \mathrm{Psh}(\Theta)$ sending $\mathbf{a} := \{a_1, \dots, a_n\}$ onto $[\mathbf{a}, n]$. Eventually, we define

$$[\_, d^0 \cup d^n] : \mathrm{Psh}(\Theta)^n \to \mathrm{Psh}(\Theta)$$

the extension by colimit of the functor $\Theta^n \to \mathrm{Psh}(\Theta)$ sending $\mathbf{a} := \{a_1, \dots, a_n\}$ onto the colimit of the span.

$$[\{a_0, \dots, a_{n-2}\}, n-1] \leftarrow [\{a_1, \dots, a_{n-2}\}, n-2] \to [\{a_1, \dots, a_{n-1}\}, n-1]$$

**Lemma 1.1.3.6.** *The image of $\overline{\mathrm{W}} \times \overline{\mathrm{W}_1}$ by the functor $[\_, \_] : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$ is included in $\overline{\mathrm{W}}$.*

*Proof.* As $[\_, \_]$ preserves colimits and monomorphisms, it is enough to show that for any pair $f, g \in \mathrm{W} \times \mathrm{W}_1$, $[f, g]$ is in W which is obvious. $\square$

35

CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

**Lemma 1.1.3.7.** *For any globular sum v, and any integer n, the morphism [v, d⁰ ∪ dⁿ] ∪ [∂v, n] → [v, n] appearing in the diagram*

![img-26.jpeg](img-26.jpeg)

is in M̅.

*Proof.* Let a be a globular sum. Remark that the morphism [a, Spₙ] → [a, d⁰ ∪ dⁿ] is in M̅. By left cancellation, this implies that [a, d⁰ ∪ dⁿ] → [a, n] is in M̅. For any presheaf X on Θ, Θ/X is an elegant Reedy category, and [X, d⁰ ∪ dⁿ] → [X, n] is then in M̅. In particular, [∂v, d⁰ ∪ dⁿ] → [∂v, n] is in M̅, and so is [v, d⁰ ∪ dⁿ] → [∂v, n] ∪ [v, d⁰ ∪ dⁿ] by stability by coproduct. A last use of the stability by left cancellation then concludes the proof. □

**1.1.3.8.** Let [b, m] be an element of Δ[Θ]. We denote Hom*(i([b, m]), [a, n]) the subset of Hom(i([b, m]), [a, n]) that consists of morphisms that preserve extremal objects. The explicit expression of morphism in Θ implies the bijection:

$$\mathrm{Hom}_{\Theta}^{*}(i([b, m]), [a, n]) \cong \mathrm{Hom}_{\Delta}([n], [m])^{*} \times \prod_{i<n} \mathrm{Hom}_{\Theta}(b, a_{i}) \quad (1.1.3.9)$$

where Hom*Δ([n], [m]) is the subset of HomΔ([n], [m]) consisting of morphisms that preserve extremal objects.

Let a := {a₀, a₁, ..., aₙ₋₁} be a finite sequence of globular sums. We define Θ→/a as the category whose objects are collections of maps {b → aᵢ}ᵢ<ₙ such that there exists no degenerate morphism b → b' factorizing all b → aᵢ. Morphisms are monomorphisms b → b' making all induced triangles commute.

The bijection (1.1.3.9) induces a bijection between the objects of Θ→/a and the morphisms [b, n] → i*[a, n] that are the identity on objects and that can not be factored through any degenerate morphism [b, n] → [b̅, n].

**Lemma 1.1.3.10.** *For any morphism p : [b, m] → i*[a, n] in Psh(Δ[Θ]) that preserves extremal objects, there exists a unique pair ({b' → aᵢ}ᵢ<ₙ, [f, i] : [b, m] → [b', n]) where {b' → aᵢ}ᵢ<ₙ is an element of Θ→/a, f is a degenerate morphism, and such that the induced*

36

1.1. BASIC CONSTRUCTIONS

triangle

![img-27.jpeg](img-27.jpeg)

commutes.

Proof. By adjunction and thanks to the bijection (1.1.3.9), p corresponds to a pair  \( (j : [m] \to [n], \{b \to a_i\}_{i < n}) \) , and i has to be equal to j.

Using once again this bijection, and the fact that degeneracies are epimorphisms, we have to show that there exists a unique degenerate morphism  \( g : b \to b' \)  that factors the morphisms  \( b \to a_i \)  for all i < n, and such that the induced family of morphisms  \( \{b' \to a_i\}_{i < n} \)  is an element of  \( \Theta_{/a}^{\rightarrow} \) .

As any infinite sequence of degenerate morphisms is constant at some point, the existence is immediate.

Suppose given two morphisms  \( b \rightarrow b' \) ,  \( b \rightarrow b'' \)  fulfilling the previous condition. The proposition 3.8 of [BR13b] implies that there exists a globular sum  \( \tilde{b} \)  and two degenerate morphisms  \( b' \rightarrow \tilde{b} \)  and  \( b'' \rightarrow \tilde{b} \)  such that the induced square

![img-28.jpeg](img-28.jpeg)

is cartesian. The universal property of pushout implies that  \( b \rightarrow \tilde{b} \)  also fulfills the previous condition. By definition of  \( b' \)  and  \( b'' \) , this implies that they are equal to  \( \tilde{b} \) , and this shows the uniqueness.

Lemma 1.1.3.11. Let \(\{b\to a_i\}_{i < n}\) be an element of \(\Theta_{/a}^{\rightarrow}\) and \(i:b'\to b\) a monomorphism of \(\Theta\). The induced family \(\{b'\to b\to a_i\}_{i < n}\) is an object of \(\Theta_{/a}^{\rightarrow}\).

Proof. The lemma 1.1.3.10 implies that there exists a unique degenerate morphism \( j: b' \to \tilde{b} \) that factors all the morphism \( b' \to b \to a_i \) for \( i < n \), and such the induced family of morphisms \( \{\tilde{b} \to a_i\}_{i < n} \) is an element of \( \Theta_{/a}^{\rightarrow} \). We proceed by contradiction, and we then suppose that \( j \) is different from the identity.

We then have, for any i < n, a commutative square

![img-29.jpeg](img-29.jpeg)

37

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

As the morphism $j$ is degenerate and different of the identity, there exists an integer $k$ and a non trivial $k$-cell $d$ of $b'$ that is sent to an identity by $j$. Now, let $d'$ be a $k$-generator of the polygraph $b$ that appears in the decomposition of $i(d)$. The commutativity of the previous square and the fact that the $(0, \omega)$-categories $a_i$ are polygraphs implies that for any $i$, the $k$-cell $a'$ is sent to an identity by the morphism $b \to a_i$. As for any $i < n$ and any $l \ge k$, there is no non trivial $l$-cell in $a_i$ whose $(k-1)$-source and $(k-1)$-target are the same, this implies that every $l$-cell of $b$ that is $(k-1)$-parallel with $d'$ is send to the identity by the morphism $b \to a_i$.

We denote $\bar{b}$ the globular sum obtained by crushing all $l$-cells of $b$ that are $(k-1)$-parallel with $d'$. The induced degenerate morphism $b \to \bar{b}$ factors all the morphisms $b \to a_i$ which is in contradiction with the fact that $\{b \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\hookrightarrow}$. $\square$

**1.1.3.12.** We say that an element $\{v \to a_i\}_{i<n}$ in the category $\Theta_{/\mathbf{a}}^{\hookrightarrow}$ is of height 0 if $v \to a_0$ factors through $\partial a_0$ or $v \to a_{n-1}$ factors through $\partial a_{n-1}$. The height of an element $w$ is the maximal integer $m$ such that there exists a sequence $v_0 \to v_1 \to \ldots \to v_m = w$ in $\Theta_{/\mathbf{a}}^{\hookrightarrow}$ with $v_i \neq v_{i+1}$ for any $i < m$ and such that $v_0$ is of height 0 and $v_1$ is not. As $\Theta$ is a Reedy category, all elements have finite height.

**Lemma 1.1.3.13.** *For any morphism $p : [b, m] \to i^*[\mathbf{a}, n]$ that preserves extremal objects, there exists a unique integer $k$, a unique element $\{b' \to a_i\}_{i<n}$ of height $k$, and a unique morphism $[f, i] : [b, m] \to [b', n]$ that doesn't factors through $[\partial b', n]$, and such that the induced triangle*

$$\begin{array}{c} [b, m] \xrightarrow{[f, i]} [b', n] \\ \searrow \quad \downarrow_{p'} \\ i^*[\mathbf{a}, n] \end{array}$$

commutes.

*If $\{\tilde{b} \to a_i\}_{i<n}$ is any other object of non negative height, and $[\tilde{f}, j] : [b, m] \to [\tilde{b}, n]$ is a morphism that make the induced triangle*

$$\begin{array}{c} [b, m] \xrightarrow{[\tilde{f}, j]} [\tilde{b}, n] \\ \searrow \quad \downarrow_{\tilde{p}} \\ i^*[\mathbf{a}, n] \end{array}$$

commutative, then $\{\tilde{b} \to a_i\}_{i<n}$ is of height strictly superior to $k$ and $[\tilde{f}, j]$ factors through $[\partial \tilde{b}, n]$.

*Proof.* The lemma 1.1.3.10 implies the first assertion. For the second one, suppose given an object $\{\tilde{b} \to a_i\}_{i<n}$ of non negative height and a morphism $[\tilde{f}, j] : [b, m] \to [\tilde{b}, n]$

38

1.1. BASIC CONSTRUCTIONS

fulfilling the desired condition. The bijection (1.1.3.9) directly implies that $j$ is equal to $i$, and the first assertion implies that $\tilde{f}$ is non degenerate.

We can then factor $\tilde{f}: b \to \tilde{b}$ in a degenerate morphism $b \to \tilde{b}$ followed by a monomorphism $\tilde{b} \to \tilde{b}$ which is not the identity. The lemma 1.1.3.11 then implies that $\{\tilde{b} \to \tilde{b} \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\rightarrow}$. The first assertion then implies that the two morphisms $[b, m] \to [b', n]$ and $[b, m] \to [\tilde{b}, n]$ are equals. As the monomorphism $[b', n] = [\tilde{b}, n] \to [\tilde{b}, n]$ is not the identity, this concludes the proof. $\square$

**Lemma 1.1.3.14.** *The morphism $i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n] \to i^*[\mathbf{a}, n]$ is in $\overline{\mathrm{M}}$, where $\partial^j \mathbf{a}$ corresponds to the sequence $\{a_1, .., \partial a_j, .., a_n\}$.*

*Proof.* For $k \in \mathbb{N} \cup \{\infty\}$, we define $x_k$ as the smallest sub object of $i^*[\mathbf{a}, n]$ such that for any element of height inferior or equal to $k$ of $\Theta_{/\mathbf{a}}^{\rightarrow}$, the corresponding morphism $[b, n] \to i^*[\mathbf{a}, n]$ factors through $x_k$. In particular we have $x_0 = i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n]$, and the lemma 1.1.3.10 implies that $x_\infty = i^*[\mathbf{a}, n]$.

Every morphism $[b, m] \to i^*[\mathbf{a}, n]$ that does not preserve extremal points then factors through $x_0$. The lemma 1.1.3.13 implies that for any integer $k$, the canonical square

$$\begin{array}{c} \coprod_{(\Theta_{/\mathbf{a}}^{\rightarrow})_{k+1}} [b, d^0 \cup d^n] \cup [\partial b, n] \longrightarrow x_k \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(\Theta_{/\mathbf{a}}^{\rightarrow})_{k+1}} [b, n] \longrightarrow x_{k+1} \end{array} \tag{1.1.3.15}$$

is cocartesian. The lemma 1.1.3.7 and the stability under pushout of $\overline{\mathrm{M}}$ imply that $x_k \to x_{k+1}$ is in $\overline{\mathrm{M}}$. As $i^*[\mathbf{a}, n]$ is the transfinite composition of the sequence $x_0 \to x_1 \to \dots$, this implies that $x_0 \to i^*[\mathbf{a}, n]$ is in $\overline{\mathrm{M}}$ which conclude the proof. $\square$

**Lemma 1.1.3.16.** *The morphism $i^* \mathrm{Sp}_a \to i^* a$ is in $\overline{\mathrm{M}}$ for any globular sum $a$.*

*Proof.* Let $[\mathbf{a}, n] := a$. As $\overline{\mathrm{M}}$ is closed under pushouts and composition, lemma 1.1.3.14 implies that the morphism

$$i^*[\{a_0, \dots, a_{n-2}\}, n-1] \cup i^*[\{a_1, \dots, a_{n-1}\}, n-1] \to i^*[\mathbf{a}, n]$$

is in $\widehat{\mathrm{M}}$. An easy induction on $n$ shows that this is also the case for the morphism

$$[a_0, 1] \cup \dots \cup [a_{n-1}, 1] = i^*[a_0, 1] \cup \dots \cup i^*[a_{n-1}, 1] \to i^*[\mathbf{a}, n].$$

Now remark that $i^* \mathrm{Sp}_{[\mathbf{a}, n]}$ is equivalent to

$$[\mathrm{Sp}_{a_0}, 1] \cup \dots \cup [\mathrm{Sp}_{a_{n-1}}, 1].$$

As the morphisms $[\mathrm{Sp}_i, 1] \to [a_i, 1]$ are by definition in $\mathrm{M}$, this concludes the proof. $\square$

39

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

**Proposition 1.1.3.17.** *There is an inclusion $i^* \mathbb{W} \subset \overline{\mathbb{M}}$.*

*Proof.* For Segal extensions, this is precisely the content of the last lemma. For saturation extensions, remark that $i^* \mathbb{W}_{\text{Sat}} = \mathbb{M}_{\text{Sat}}$. $\square$

*Proof of theorem 1.1.3.3.* Let $a$ be a globe. We then have $i_! i^* a = a$. Suppose now that $a$ is any globular sum. We then have a commutative diagram

![img-30.jpeg](img-30.jpeg)

where the upper horizontal morphism is an identity. The proposition 1.1.3.17 and the fact that $i_!(\mathbb{M}) \subset \mathbb{W}$ implies that the vertical morphisms of the previous diagram are in $\overline{\mathbb{W}}$. By left cancellation, this implies that $i_! i^* a \to a$ belongs to $\overline{\mathbb{W}}$ for any globular sum. We proceed analogously to show that for any $b \in \Delta[\Theta]$, $b \to i^* i_! b$ is in $\overline{\mathbb{M}}$. $\square$

## 1.2 Gray Operations

### 1.2.1 Recollection on Steiner theory

We present here the Steiner theory developed in [Ste04].

**1.2.1.1.** An augmented directed complex $(K, K^*, e)$ is given by a complex of abelian groups $K$, with an augmentation $e$:

$$\mathbb{Z} \xleftarrow{e} K_0 \xleftarrow{\partial_0} K_1 \xleftarrow{\partial_1} K_2 \xleftarrow{\partial_2} K_3 \xleftarrow{\partial_3} \dots$$

and a graded set $K^* = (K_n^*)_{n \in \mathbb{N}}$ such that for any $n$, $K_n^*$ is a submonoid of $K_n$. A morphism of directed complexes between $(K, K^*, e)$ and $(L, L^*, e')$ is given by a morphism of augmented complexes of abelian groups $f : (K, e) \to (L, e')$ such that $f(K_n^*) \subset L_n^*$ for any $n$. We note by ADC the category of augmented directed complexes.

Steiner then constructs an adjunction

$$\lambda : \omega\text{-cat} \xrightarrow{\perp} \text{ADC} : \nu$$

The functor $\lambda$ is the simplest to define:

**Definition 1.2.1.2.** Let $C$ be a $\omega$-category. We denote by $(\lambda C)_n$ the abelian group generated by the set $\{[x]_n : x \in C_n\}$ and the relations

$$[x *_m y]_n \sim [x]_n + [y]_n \text{ for } m < n.$$

40

1.2. GRAY OPERATIONS

We define the morphism $\partial_n : (\lambda C)_{n+1} \rightarrow (\lambda C)_n$ on generators by the formula:

$$\partial_n([x]_{n+1}) := [d_n^+ x]_n - [d_n^- x]_n.$$

We can easily check that the morphism $\partial$ is a differential. We define an augmentation $e : (\lambda C)_0 \rightarrow \mathbb{Z}$ by setting $e([x]_0) = 1$ on generators. We denote by $(\lambda C)_n^*$ the additive submonoid generated by the elements $[x]_n$. We then set:

$$\lambda C := (\{(\lambda C)_n\}_{n \in \mathbb{N}}, \{(\lambda C)_n^*\}_{n \in \mathbb{N}}, e).$$

This assignation lifts to a functor:

$$\begin{array}{rcl} \lambda & : & \omega\text{-cat} \rightarrow \text{ADC} \\ & & C \rightarrow \lambda C. \end{array}$$

### Example 1.2.1.3.

(1) For any integer $n$, $\lambda \mathbf{D}_n$ is the augmented directed complex whose underlying chain complex is given by:

$$\mathbb{Z} \xleftarrow{e} \mathbb{Z}[e_0^-, e_0^+] \xleftarrow{\partial_0} \dots \xleftarrow{\partial_{n-2}} \mathbb{Z}[e_{n-1}^-, e_{n-1}^+] \xleftarrow{\partial_{n-1}} \mathbb{Z}[e_n] \xleftarrow{\partial_n} 0 \leftarrow \dots$$

where for any $0 < k < n$ and $\alpha \in \{-, +\}$

$$e(e_0^\alpha) = 1 \quad \partial_{k-1}(e_k^\alpha) = e_{k-1}^+ - e_{k-1}^- \quad \partial_{n-1}(e_n) = e_{n-1}^+ - e_{n-1}^-.$$

(2) The augmented directed complex $\lambda[n]$ has for underlying chain complex:

$$\mathbb{Z} \xleftarrow{e} \mathbb{Z}[v_0, v_1, \dots, v_n] \xleftarrow{\partial_0} \mathbb{Z}[v_{0,1}, v_{1,2}, \dots, v_{n-1,n}] \xleftarrow{\partial_1} 0 \leftarrow \dots$$

where for any $k < n$ and $\alpha \in \{-, +\}$

$$e(v_k) = e(v_n) = 1 \quad \partial_1(v_{k,k+1}) = v_{k+1} - v_k.$$

**1.2.1.4.** We now define the functor $\nu : \text{ADC} \rightarrow \omega\text{-cat}$. Throughout, we fix an augmented directed complex $(K, K^*, e)$. A *Steiner array* (or simply a *array*) of dimension $n$ is the data of a finite double sequence:

$$\begin{pmatrix} x_0^- & x_1^- & x_2^- & x_3^- & \dots & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & x_3^+ & \dots & x_n^+ \end{pmatrix}$$

such that

$$(1) \ x_n^- = x_n^+;$$

41

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

(2) For any \(i \leq n\) and \(\alpha \in \{-, +\}\), \(x_i^\alpha\) is an element of \(K_i^*\);
(3) For any \(0 < i \leq n\), \(\partial_{i-1}(x_i^\alpha) = x_{i-1}^+ - x_{i-1}^-\);

An array is said to be coherent if $e(x_0^+) = e(x_0^-) = 1$.

Definition 1.2.1.5. We define the globular set $\nu K$, whose $n$-cells are the coherent arrays of dimension $n$. The source and target maps are defined for $k < n$ by the formula:

$$d_k^\alpha \begin{pmatrix} x_0^- & x_1^- & x_2^- & \dots & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & \dots & x_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- & x_1^- & x_2^- & \dots & x_{k-1}^- & x_k^\alpha \\ x_0^+ & x_1^+ & x_2^+ & \dots & x_{k-1}^+ & x_k^\alpha \end{pmatrix}$$

There is an obvious group structure on the arrays:

$$\begin{pmatrix} x_0^- & x_1^- & \dots & x_n^- \\ x_0^+ & x_1^+ & \dots & x_n^+ \end{pmatrix} + \begin{pmatrix} y_0^- & y_1^- & \dots & y_n^- \\ y_0^+ & y_1^+ & \dots & y_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- + y_0^- & x_1^- + y_1^- & \dots & x_n^- + y_n^- \\ x_0^+ + y_0^+ & x_1^+ + y_1^+ & \dots & x_n^+ + y_n^+ \end{pmatrix}$$

- For two coherent arrays $x$ and $y$ such that $d_k^-(x) = d_k^+(y) = z$, we define their $k$-composition by the following formula:

$$x *_k y := x - z + y.$$

More explicitly:

$$\begin{pmatrix} x_0^- & \dots & x_n^- \\ x_0^+ & \dots & x_n^+ \end{pmatrix} *_k \begin{pmatrix} y_0^- & \dots & y_n^- \\ y_0^+ & \dots & y_n^+ \end{pmatrix} := \begin{pmatrix} y_0^- & \dots & y_k^- & y_{k+1}^- + x_{k+1}^- & \dots & y_n^- + x_n^- \\ x_0^+ & \dots & x_k^+ & y_{k+1}^+ + x_{k+1}^+ & \dots & y_n^+ + x_n^+ \end{pmatrix}$$

- For an integer $m > n$, we define the $m$-sized array $1_x^m$ as follows:

$$1_x^m := \begin{pmatrix} x_0^- & \dots & x_n^- & 0 & \dots & 0 \\ x_0^+ & \dots & x_n^+ & 0 & \dots & 0 \end{pmatrix}$$

The globular set $\nu K$, equipped with these compositions and units is an $\omega$-category.

Definition 1.2.1.6. We define the functor $\nu : \text{ADC} \to \omega$-cat which associates to an augmented directed complex $K$, the $\omega$-category $\nu K$, and to a morphism of augmented directed complexes $f : K \to L$, the morphism of $\omega$-categories.

$$\begin{array}{c c c c c c} \nu f : & \nu K & \to & \nu L \\ & \begin{pmatrix} x_0^- & \dots & x_n^- \\ x_0^+ & \dots & x_n^+ \end{pmatrix} & \mapsto & \begin{pmatrix} f_0(x_0^-) & \dots & f_n(x_n^-) \\ f_0(x_0^+) & \dots & f_n(x_n^+) \end{pmatrix} \end{array}$$

42

1.2. GRAY OPERATIONS

**Theorem 1.2.1.7** (Steiner). *The functors $\lambda$ and $\nu$ form an adjoint pair*

$$\lambda : \omega\text{-cat} \xrightleftharpoons[\perp]{\text{ADC}} : \nu$$

*For a $\omega$-category $C$, the unit of the adjunction is given by:*

$$\begin{aligned} \eta : & C \rightarrow \nu\lambda C \\ & x \in C_n \mapsto \begin{pmatrix} [d_0^-(x)]_0 & \dots & [d_{n-1}^-(x)]_{n-1} & [x]_n \\ [d_0^+(x)]_0 & \dots & [d_{n-1}^+(x)]_{n-1} & [x]_n \end{pmatrix} \end{aligned}$$

*For an augmented directed complex $K$, the counit is given by:*

$$\begin{aligned} \pi : & \lambda\nu K \rightarrow K \\ & [x]_n \in (\lambda\nu K)_n \mapsto x_n^+ = x_n^- \end{aligned}$$

*Proof.* This is [Ste04, theorem 2.11].

**1.2.1.8.** A *basis* for an augmented directed complex $(K, K^*, e)$ is a graded set $B = (B_n)_{n \in \mathbb{N}}$ such that for every $n$, $B_n$ is both a basis for the monoid $K_n^*$ and for the group $K_n$.

**Remark 1.2.1.9.** The elements of $B_n$ can be characterized as the minimal elements of $K_n^* \setminus 0$ for the following order relation:

$$x \leq y \text{ iff } y - x \in K_n^*$$

This shows that if a basis exists, it is unique.

**1.2.1.10.** Any element of $K_n$ can then be written uniquely as a sum $\sum_{b \in B_n} \lambda_b b$. This leads us to define new operations: For an element $x := \sum_{b \in B_n} \lambda_b b$ of $K_n$, we define the *positive part* and the *negative part*:

$$\begin{aligned} (x)_+ & := \sum_{b \in B_n, \lambda_b > 0} \lambda_b b \\ (x)_- & := \sum_{b \in B_n, \lambda_b < 0} -\lambda_b b \end{aligned}$$

We then have $x = (x)_+ - (x)_-$. An element $x$ is *positive* (resp. *negative*) when $x = (x)_+$ (resp. when $x = -(x)_-$). Let $y = \sum_{b \in B_n} \mu_b b$, we set :

$$x \wedge y := \sum_{b \in B_n} \min(\lambda_b, \mu_b) \ b$$

Eventually, we set

$$\begin{aligned} \partial_n^+(\_) & := (\partial_n(\_))_+ : K_{n+1} \rightarrow K_n^* \\ \partial_n^-(\_) & := (\partial_n(\_))_- : K_{n+1} \rightarrow K_n^* \end{aligned}$$

When an element $b$ of the basis is in the support of $x$, i.e $\lambda_b \neq 0$, we say that $b$ *belongs to $x$*, which is denoted by $b \in x$.

43

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

Example 1.2.1.11. For any integer $n$, $\lambda\mathbf{D}_n$ admits a basis, given by the graded set $B_{\lambda\mathbf{D}_n}$ fulfilling:

$$(B_{\lambda\mathbf{D}_n})_k := \begin{cases} \{e_k^-, e_k^+\} & \text{if } k < n \\ \{e_n\} & \text{if } k = n \\ \emptyset & \text{if } k > n \end{cases}$$

The augmented directed complex $\lambda[n]$ also admits a basis, given by the graded set $B_{\lambda\mathbf{D}_n}$ fulfilling:

$$(B_{\lambda\mathbf{D}_n})_k := \begin{cases} \{v_0, v_1, ..., v_n\} & \text{if } k = 0 \\ \{v_{0,1}, v_{1,2}..., v_{n-1,n}\} & \text{if } k = 1 \\ \emptyset & \text{if } k > 1 \end{cases}$$

1.2.1.12. Let $a \in K_n^*$. We set by a decreasing induction on $k \le n$:

$$\begin{array}{lcl} \langle a \rangle_k^\alpha & := & a \quad \text{if } k = n \\ & := & \partial_k^\alpha \langle a \rangle_{k+1}^\alpha \quad \text{if not} \end{array}$$

The array associated to $a$ is then:

$$\langle a \rangle := \begin{pmatrix} \langle a \rangle_0^- & \dots & \langle a \rangle_{n-1}^- & a \\ \langle a \rangle_0^+ & \dots & \langle a \rangle_{n-1}^+ & a \end{pmatrix}$$

The basis is said to be unitary when for any $b \in B$, the array $\langle b \rangle$ is coherent.

1.2.1.13. We define the relation $\odot$ on $B$ as being the smallest transitive and reflexive relation such that for any pair of elements of the basis $a, b$,

$$a \odot_n b \text{ if } (|a| > 0 \text{ and } b \in \langle a \rangle_{|a|-1}^-) \text{ or } (|b| > 0 \text{ and } a \in \langle b \rangle_{|b|-1}^+)$$

A basis is said to be loop free when for any $n$, the relation $\odot_n$ is a (partial) order on $B$.

Remark 1.2.1.14. In [AM20], this notion is called strongly loop free.

Example 1.2.1.15. For any integer $n$, $\lambda\mathbf{D}_n$ and $\lambda[n]$ admit a loop free and unitary basis.

1.2.1.16. We now define the subcategory $\mathrm{ADC_B}$ of ADC composed of augmented directed complexes which admit a unitary and loop free basis. We will now describe the analog of the notion of basis for $\omega$-categories.

Definition 1.2.1.17. A $\omega$-category $C$ is generated by composition by a set $E \subset C$ when any cell can be written as a composition of elements of $E$ and iterated units of elements of $E$. This set is a basis if $\{[e]_{d(e)}\}_{e \in E}$ is a basis of the augmented directed complex $\lambda C$.

44

1.2. GRAY OPERATIONS

**Proposition 1.2.1.18.** *An $\omega$-category $C$ that admits a basis is an $(0, \omega)$-category.*

*Proof.* Let $C$ be an $\omega$-category that admits a basis $E$. Suppose that there exists a non trivial $n$-cell $\alpha$ that admits an inverse $\beta$. We then have $[\alpha]_n + [\beta]_n = [\alpha \circ_{n-1} \beta]_n = 0$. As $\lambda C$ is free, we have $[\alpha]_n = 0$. This implies the equality $[e]_n = 0$ for any element $e \in E$ of dimension $n$ that appears in a decomposition of $\alpha$. This is obviously in contradiction with the fact that $\{[e]_{d(e)}\}_{e \in E}$ is a basis of the augmented directed complex $\lambda C$. $\square$

**Definition 1.2.1.19.** A basis $E$ of an $(0, \omega)$-category is :

(1) *Loop free* when $\{[e]_{d(e)}\}_{e \in E}$ is.
(2) *Atomic* when $[d_n^+ e]_n \wedge [d_n^- e]_n = 0$ for any $e \in E$ and any natural number $n$ strictly smaller than the dimension of $e$.

**Proposition 1.2.1.20.** *If a loop free basis $E$ is atomic then $\{[e]\}_{e \in E}$ is unitary.*

*Proof.* This is [Ste04, proposition 4.6]. $\square$

**Example 1.2.1.21.** For any integer $n$, $\mathbf{D}_n$ and $[n]$ admit a loop free and atomic basis. More generally, [AM20, proposition 4.13] states that any globular sum admits a loop free and atomic basis.

**1.2.1.22.** Proposition 1.23 of [AGOR23] states that if an $(0, \omega)$-category admits a loop-free and atomic basis, it is unique. We then define the category $(0, \omega)$-cat$_B$ as the full subcategory of $\omega$-cat composed of $(0, \omega)$-categories admitting an atomic and loop-free basis.

**Theorem 1.2.1.23** (Steiner). *Once restricted to $(0, \omega)$-cat$_B$ and ADC$_B$, the adjunction*

$$\lambda : \omega\text{-cat} \xrightarrow[\downarrow]{\perp} \text{ADC} : \nu$$

*becomes an adjoint equivalence, i.e. :*

$$\lambda|_{(0,\omega)\text{-cat}_B} \circ \nu|_{\text{ADC}_B} \cong id|_{\text{ADC}_B} \qquad id|_{(0,\omega)\text{-cat}_B} \cong \nu|_{\text{ADC}_B} \circ \lambda|_{(0,\omega)\text{-cat}_B}$$

*Proof.* See [Ste04, theorem 5.11]. $\square$

If $K$ is an augmented directed complex admitting a unitary and loop-free basis $B$, then the $(0, \omega)$-category $\nu K$ admits an atomic and loop-free basis given by the set $\langle B \rangle := \{\langle b \rangle, b \in B\}$. Conversely if an $(0, \omega)$-category $C$ admits an atomic and loop-free basis $E$, then the augmented directed complex $\lambda C$ admits a unitary and loop-free basis given by the family of sets $[E_n] := \{[e]_{d(e)}, e \in E_n\}$. The isomorphisms

$$\lambda \nu K \cong K \quad \text{and} \quad C \cong \nu \lambda C$$

45

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

induce isomorphisms:

$$[\langle B \rangle] \cong B \quad \text{and} \quad E \cong \langle [E] \rangle.$$

**1.2.1.24.** We define the *full duality*

$$(\_)^\circ : \mathrm{ADC} \to \mathrm{ADC}$$

that sends a augmented directed complex $((K, \partial), K^*, e)$ to $((K, -\partial), K^*, e)$. We left the reader to check that $K^\circ$ admits a loop free and atomic basis when this is the case for $K$. This functor then induces a functor:

$$(\_)^\circ : \mathrm{ADC}_\mathrm{B} \to \mathrm{ADC}_\mathrm{B}.$$

Moreover, we have a canonical equivalence:

$$\lambda(C^\circ) \cong (\lambda C)^\circ$$

natural in $C$.

**1.2.1.25.** Let $f : M \to N$ be a morphism between two augmented directed complexes admitting unitary and loop-free bases $B_M$ and $B_N$. The morphism $f$ is *quasi-rigid* if for any $n$, and any $b \in (B_M)_n$,

$$f_n(b) \neq 0 \ \Rightarrow \ f_n(b) \in B_N \text{ and } \nu(f)\langle b \rangle = \langle f_n(b) \rangle.$$

**Theorem 1.2.1.26.** *Suppose given a commutative square in $\mathrm{ADC}_\mathrm{B}$*

$$\begin{array}{ccc} K & \xrightarrow{k^0} & M_1 \\ k^0 \Big\downarrow & & \Big\downarrow l^1 \\ M_0 & \xrightarrow{l^0} & M \end{array}$$

*and such that all morphisms are quasi-rigid. Let $B_K$, $B_{M_0}$, $B_{M_1}$, $B_M$ be the bases of $K$, $M_0$, $M_1$, $M$.*

*Then, this square is cocartesian if and only if for any $n$, the induced diagram of sets*

$$\begin{array}{ccc} (B_K)_n \cup \{0\} & \xrightarrow{k_n^0} & (B_{M_1})_n \cup \{0\} \\ k_n^0 \Big\downarrow & & \Big\downarrow l_n^1 \\ (B_{M_0})_n \cup \{0\} & \xrightarrow{l_n^0} & (B_M)_n \cup \{0\} \end{array}$$

46

1.2. GRAY OPERATIONS

is cocartesian. Furthermore, the induced square in $(0, \omega)$-cat

$$\begin{array}{ccc} \nu K & \xrightarrow{\nu k^0} & \nu M_1 \\ \nu k^0 \downarrow & & \downarrow \nu l^1 \\ \nu M_0 & \xrightarrow{\nu l^0} & \nu M \end{array}$$

is cocartesian.

*Proof.* This is a combination of theorems 3.1.2 and 3.2.7 of [Lou21].

## 1.2.2 Gray operations on augmented directed complexes

We follow Steiner ([Ste04]) and Ara-Maltsiniotis ([AM20]) for the definitions and first properties of Gray operations on augmented directed complexes.

**1.2.2.1.** Let $(K, K^*, e)$ and $(L, L^*, f)$ be two augmented directed complexes. We define the *Gray tensor product* of $(K, K^*, e)$ and $(L, L^*, f)$ as the augmented directed complex

$$(K, K^*, e) \otimes (L, L^*, f) := (K \otimes L, (K \otimes L)^*, e \otimes f)$$

where

- $K \otimes L$ is the chain complex whose value on $n$ is:

$$(K \otimes L)_n := \oplus_{k+l=n} K_k \otimes L_l$$

and the differential is the unique graded group morphism fulfilling:

$$\partial(x \otimes y) := \partial x \otimes y + (-1)^{|x|} x \otimes \partial y$$

where we set the convention $\partial x := 0$ if $|x| = 0$.

- $(K \otimes L)^*$ is given on all integer $n$ by :

$$(K \otimes L)_n^* := \oplus_{k+l=n} K_k^* \otimes L_l^*.$$

- $e \otimes f : K_0 \otimes L_0 \to \mathbb{Z}$ is the unique morphism fulfilling

$$(e \otimes f)(x \otimes y) = e(x)f(y).$$

**1.2.2.2.** The Gray tensor product induces a monoidal structure on ADC. Its unit is given by $\lambda \mathbf{D}_0$. Furthermore, Steiner shows that if $K$ and $L$ admit loop free and unitary bases, so does $K \otimes L$. The monoidal structure then restricts to a monoidal structure on $\text{ADC}_\text{B}$. Eventually [AM20, proposition A.20] provides an equivalence

$$(K \otimes L)^\circ \cong K^\circ \otimes L^\circ \quad (1.2.2.3)$$

47

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

1.2.2.4. To simplify notion, the augmented directed complex \(\lambda[1]\) will simply be denoted by [1]. The induced functor

\[
\_ \otimes [ 1 ]: \mathrm{ADC} \rightarrow \mathrm{ADC}
\]

is called the Gray cylinder. For  \( (K, K^{*}, e) \)  an augmented directed complex, we then have

\[
(K, K ^ {*}, e) \otimes [ 1 ] := (K \otimes [ 1 ], (K \otimes [ 1 ]) ^ {*}, e)
\]

where

- \(K \otimes [1]\) is the chain complex whose value on \(n\) is:

\[
(K \otimes [ 1 ]) _ {n} := \left\{ \begin{array}{l l} \{x \otimes \{\epsilon \}, x \in K _ {0}, \epsilon = 0, 1 \} & \text {if n = 0} \\ \{x \otimes \{\epsilon \}, x \in K _ {n}, \epsilon = 0, 1 \} \oplus \{x \otimes [ 1 ], x \in K _ {n - 1} \} & \text {if n > 0} \end{array} \right.
\]

and the differential is the unique graded group morphism fulfilling:

\[
\partial (x \otimes [ 1 ]) := \partial x \otimes [ 1 ] + (- 1) ^ {| x |} (x \otimes \{1 \} - x \otimes \{0 \}) \quad \partial (x \otimes \{\epsilon \}) = (\partial x) \otimes \{\epsilon \}
\]

for \(\epsilon \in \{0,1\}\), and where we set the convention \(\partial x := 0\) if \(|x| = 0\).

- \((K\otimes [1])^{*}\) is given on all integer \(n\) by:

\[
(K \otimes [ 1 ]) _ {n} ^ {*} := \left\{ \begin{array}{l l} \{x \otimes \{\epsilon \}, x \in K _ {0} ^ {*}, \epsilon = 0, 1 \} & \text {if n = 0} \\ \{x \otimes \{\epsilon \}, x \in K _ {n} ^ {*}, \epsilon = 0, 1 \} \oplus \{x \otimes [ 1 ], x \in K _ {n - 1} ^ {*} \} & \text {if n > 0} \end{array} \right.
\]

- \(e:(K\otimes [1])_0\to \mathbb{Z}\) is the unique morphism fulfilling

\[
e (x \otimes \{0 \}) = e (x \otimes \{1 \}) = e (x).
\]

1.2.2.5. We define the Gray cone and the Gray o-cone:

\[
\begin{array}{c c c c c c} \text {ADC} & \to & \text {ADC} & \text {ADC} & \to & \text {ADC} \\ K & \mapsto & K \star 1 & K & \mapsto & 1 ^ {c o} \star K \end{array}
\]

where \(K \star 1\) and \(1 \stackrel{co}{\star} K\) are defined as the following pushout:

\[
\begin{array}{c c c} K \otimes \{1 \} \longrightarrow K \otimes [ 1 ] & K \otimes \{0 \} \longrightarrow K \otimes [ 1 ] \\ \Big \downarrow & \Big \downarrow & \Big \downarrow \\ 1 \longrightarrow K \star 1 & 1 \longrightarrow 1 ^ {c o} \star K \end{array} \tag {1.2.2.6}
\]

The equation (1.2.2.3) provides an equivalence

\[
(C \star 1) ^ {\circ} \cong 1 \stackrel {c o} {\star} C ^ {\circ}.
\]

According to [AM20, corollary 6.21] and to the previous equivalence, if \( K \) admits a loop free and unitary basis, this is also the case for \( K \star 1 \) and \( 1 \stackrel{co}{\star} K \). The Gray cone and the Gray o-cone then induce functors:

\[
\begin{array}{c c c c c c} \mathrm{ADC} _ {\mathrm{B}} & \to & \mathrm{ADC} _ {\mathrm{B}} & \mathrm{ADC} _ {\mathrm{B}} & \to & \mathrm{ADC} _ {\mathrm{B}} \\ K & \mapsto & K \star 1 & K & \mapsto & 1 ^ {c o} \star K \end{array}
\]

48

1.2. GRAY OPERATIONS

### 1.2.2.7. Unfolding the definition, we have

$$
(K, K', e) \star 1 := (K \star 1, (K \star 1)^*, e) \quad 1 \stackrel{co}{\star} (K, K', e) := (1 \stackrel{co}{\star} K, (1 \stackrel{co}{\star} K)^*, e)
$$

where

- $K \star 1$ and $1 \stackrel{co}{\star} K$ are the chain complex whose value on $n$ are:

$$
(K \star 1)_n := \left\{ \begin{array}{ll} \mathbb{Z}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n\} \oplus \{x \star 1, x \in K_{n-1}\} & \text{if } n > 0 \end{array} \right.
$$

$$
(1 \stackrel{co}{\star} K)^n := \left\{ \begin{array}{ll} \mathbb{Z}[1 \stackrel{co}{\star} \emptyset] \oplus \{\emptyset \stackrel{co}{\star} x, x \in K_0\} & \text{if } n = 0 \\ \{\emptyset \stackrel{co}{\star} x, x \in K_n\} \oplus \{1 \stackrel{co}{\star} x, x \in K_{n-1}\} & \text{if } n > 0 \end{array} \right.
$$

and the differentials are the unique graded group morphisms fulfilling:

$$
\partial(x \star 1) = \partial x \star 1 + (-1)^{|x|} x \star \emptyset \quad \partial(x \star \emptyset) = \partial x \star \emptyset
$$

$$
\partial(1 \stackrel{co}{\star} x) = 1 \stackrel{co}{\star} \partial x + (-1)^{|x|} \emptyset \stackrel{co}{\star} x \quad \partial(\emptyset \stackrel{co}{\star} x) = \emptyset \stackrel{co}{\star} x
$$

where we set the convention $\partial x := 0$ if $|x| = 0$.

- The graded monoids $(K \star 1)^*$ and $(1 \stackrel{co}{\star} K)^*$ are given on all integer $n$ by:

$$
(K \star 1)^* := \left\{ \begin{array}{ll} \mathbb{N}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0^*\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n^*\} \oplus \{x \star 1, x \in K_{n-1}^*\} & \text{if } n > 0 \end{array} \right.
$$

$$
(1 \stackrel{co}{\star} K)^* := \left\{ \begin{array}{ll} \mathbb{N}[1 \stackrel{co}{\star} \emptyset] \oplus \{\emptyset \stackrel{co}{\star} x, x \in K_0^*\} & \text{if } n = 0 \\ \{\emptyset \stackrel{co}{\star} x, x \in K_n^*\} \oplus \{1 \stackrel{co}{\star} x, x \in K_{n-1}^*\} & \text{if } n > 0 \end{array} \right.
$$

- The augmentations $e : (K \star 1)_0 \to \mathbb{Z}$ and $e : (1 \stackrel{co}{\star} K)_0 \to \mathbb{Z}$ are the unique ones fulfilling

$$
e(\emptyset \star 1) = 1 \quad e(x \star \emptyset) = e(x)
$$

$$
e(1 \stackrel{co}{\star} \emptyset) = 1 \quad e(\emptyset \stackrel{co}{\star} x) = e(x).
$$

**Proposition 1.2.2.8.** *Let $A$ be an augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexes $A \star 1$ and $1 \stackrel{co}{\star} A$ have no non-trivial automorphisms.*

*Proof.* Let $\phi : A \star 1 \to A \star 1$ be an automorphism. The morphism $\phi$ then induces a bijection on the elements of the basis of $A \star 1$.

As the element $\emptyset \star 1 \in (A \star 1)_0$ is the only element of the basis such that for all $v \in (A \star 1)_1$ $\partial_0^-(v) \neq \emptyset \star 1$, it is preserved by $\phi$. As a consequence, for any element $x$ of the basis of $A_0$, $\phi(x \star \emptyset)$ is of shape $x' \star \emptyset$. The morphism $\phi$ then preserves $(A \star \emptyset)_0$.

49

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

Now, remark that for any element \( e \in (A \star 1)_{n+1}^* \), there exists \( x \in (A \star 1)_n^* \) such that \( x \star 1 \leq e \) if and only if there exists \( y \in (A \star 1)_{n-1}^* \) such that \( y \star 1 \leq \partial^{+}(e) \). By a direct induction, this implies that there exists \( x \in (A \star 1)_n^* \) such that \( x \star 1 \leq e \) if and only if \( \partial_0^+(e) \in \mathbb{Z}[\emptyset \star 1] \).

Combined with the previous observation, this implies that for any element x of the basis of  \( A_{n+1} \) ,  \( \phi(x \star \emptyset) \)  is of shape  \( x' \star \emptyset \) . The automorphism  \( \phi \)  then induces by restriction an automorphism  \( \phi_{|A \star \emptyset}: A \to A \) , and the hypothesis implies that it is the identity.

We now show by induction on n that  \( \phi_{n}:(A\star1)_{n}\to(A\star1)_{n} \)  is the identity. Suppose the result true at the stage n. For any element x of the basis of  \( A_{n} \) , we then have

\[
\partial \phi (x \star 1) = \phi (\partial (x \star 1)) = \partial (x \star 1).
\]

By the definition of the derivative of  \( A \star 1 \) , and as  \( \phi \)  preserves the basis, this forces the equality  \( \phi(x \star 1) = x \star 1 \) . As we already know that for any element x of the basis of  \( A_{n+1} \)  we have  \( \phi(x \star \emptyset) = x \star \emptyset \) , this concludes the induction.

We then have \(\phi = id\) and \(A\star 1\) has no non trivial automorphisms. The case \(1^{\text{co}}\star A\) follows directly by using the fact that dualities preserve augmented directed complexes admitting no non-trivial automorphisms.

□

##### 1.2.2.9. We define the suspension as the functor

\[
[ \_, 1 ]: \mathrm{ADC} \to \mathrm{ADC}
\]

where \([K,1]\) is defined as the following pushout:

\[
\begin{array}{c} K \otimes \{0, 1 \} \longrightarrow K \otimes [ 1 ] \\ \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text { (1.2.2.10) } \\ 1 \coprod 1 \longrightarrow [ K, 1 ] \end{array}
\]

We leave to the reader to check that \([K,1]\) admits a loop free and unitary basis when this is the case for \(K\). This functor then induces a functor:

\[
[ \_, 1 ]: \mathrm{ADC} _ {\mathrm{B}} \to \mathrm{ADC} _ {\mathrm{B}}
\]

##### 1.2.2.11. Unfolding the definition, we have

\[
[ (K, K ^ {\prime}, e), 1 ] := ([ K, 1 ], ([ K, 1 ]) ^ {*}, e)
\]

where

50

1.2. GRAY OPERATIONS

- \([K,1]\) is the chain complex whose value on \(n\) is:

\[
[ K, 1 ] := \left\{ \begin{array}{l l} \mathbb {Z} [ \{0 \}, \{1 \} ] & \text {if n = 0} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 0} \end{array} \right.
\]

and the differential is the unique graded group morphism fulfilling:

\[
\partial ([ x, 1 ]) := \left\{ \begin{array}{l l} \{1 \} - \{0 \} & \text {if} | x | = 0 \\ [ \partial x, 1 ] & \text {if} | x | > 0 \end{array} \right.
\]

- \(([K,1])^{*}\) is given on all integer \(n\) by:

\[
([ K, 1 ]) _ {n} ^ {*} := \left\{ \begin{array}{l l} \mathbb {N} [ 0, 1 ] & \text {if n = 0} \\ \{[ x, 1 ], x \in K _ {n - 1} ^ {*} \} & \text {if n > 0} \end{array} \right.
\]

- \(e: ([K, 1])_0 \to \mathbb{Z}\) is the unique morphism fulfilling

\[
e (0) = e (1) = e (x).
\]

Proposition 1.2.2.12. Let A be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complex  \( [A,1] \)  has no non-trivial automorphisms.

Proof. Let \(\phi : [A,1] \to [A,1]\) be an automorphism. As the element \(\{1\} \in ([A,1])_0\) is the only element of the basis such that for all \(v \in [A,1]_1 \partial_0^- (v) \neq \{1\}\), it is preserved by \(\phi\). As a consequence, \(\phi\) also preserves \(\{0\}\). The induced morphism \(\phi_0 : [A,1]_0 \to [A,1]_0\) is then the identity.

Now, remark that  \( (\phi_{n+1})_{n\in\mathbb{N}}: A \to A \)  is an automorphism and is then the identity. This implies that for all n > 0,  \( \phi_{n}: [A,1]_{n} \to [A,1]_{n} \)  is then identity, which concludes the proof. □

1.2.2.13. We define the wedges as the functors

\[
[ \_, 1 ] \vee [ 1 ]: \mathrm{ADC} \rightarrow \mathrm{ADC} \quad [ 1 ] \vee [ \_, 1 ]: \mathrm{ADC} \rightarrow \mathrm{ADC}
\]

where  \( [K,1]\vee[1] \)  and  \( [1]\vee[K,1] \)  are defined as the following pushouts:

![img-31.jpeg](img-31.jpeg)

![img-32.jpeg](img-32.jpeg)

Once again, we can easily check that  \( [K,1]\vee[1] \)  and  \( [1]\vee[K,1] \)  have a loop free and unitary basis when this is the case for K. These functors then induce functors

\[
[ \_, 1 ] \vee [ 1 ]: \mathrm{ADC} _ {\mathrm{B}} \rightarrow \mathrm{ADC} _ {\mathrm{B}} \quad [ 1 ] \vee [ \_, 1 ]: \mathrm{ADC} _ {\mathrm{B}} \rightarrow \mathrm{ADC} _ {\mathrm{B}}
\]

51

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

##### 1.2.2.14. Unfolding the definition, we have

\[
[ (K, K ^ {\prime}, e), 1 ] \vee [ 1 ] := ([ K, 1 ] \vee [ 1 ], ([ K, 1 ] \vee [ 1 ]) ^ {*}, e)
\]

\[
[ 1 ] \vee (K, K ^ {\prime}, e), 1 ] := ([ 1 ] \vee [ K, 1 ], ([ 1 ] \vee [ K, 1 ]) ^ {*}, e)
\]

where

- \([K,1]\vee [1]\) and \([1]\vee [K,1]\) are the chain complexes whose value on \(n\) are:

\[
[ K, 1 ] \vee [ 1 ] := \left\{ \begin{array}{l l} \mathbb {Z} [ \{0 \}, \{1 \}, \{2 \} ] & \text {if n = 0} \\ \{[ x, 1 ], x \in K _ {0} \} \oplus \mathbb {Z} [ e _ {1} ] & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 1} \end{array} \right.
\]

\[
[ 1 ] \vee [ K, 1 ] := \left\{ \begin{array}{l l} \mathbb {Z} [ \{0 \}, \{1 \}, \{2 \} ] & \text {if n = 0} \\ \mathbb {Z} [ e _ {1} ] \oplus \{[ x, 1 ], x \in K _ {0} \} & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 1} \end{array} \right.
\]

and the differentials are the unique graded group morphism fulfilling:

\[
\partial_ {[ K, 1 ] \vee [ 1 ]} (e _ {1}) := \{2 \} - \{1 \} \quad \partial_ {[ K, 1 ] \vee [ 1 ]} ([ x, 1 ]) := \left\{ \begin{array}{l l} \{1 \} - \{0 \} & \text {if} | x | = 0 \\ [ \partial x, 1 ] & \text {if} | x | > 0 \end{array} \right.
\]

\[
\partial_ {[ 1 ] \vee [ K, 1 ]} (e _ {1}) := \{1 \} - \{0 \} \quad \partial_ {[ 1 ] \vee [ K, 1 ]} ([ x, 1 ]) := \left\{ \begin{array}{l l} \{2 \} - \{1 \} & \text {if} | x | = 0 \\ [ \partial x, 1 ] & \text {if} | x | > 0 \end{array} \right.
\]

- \(([K,1]\vee [1])^{*}\) and \(([1]\vee [K,1])^{*}\) are given on all integer \(n\) by:

\[
([ K, 1 ] \vee [ 1 ]) ^ {*} := \left\{ \begin{array}{l l} \{\{0 \}, \{1 \}, \{2 \} \} & \text {if n = 0} \\ \{[ x, 1 ], x \in K _ {0} ^ {*} \} \oplus \mathbb {N} [ e _ {1} ] & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 1} \end{array} \right.
\]

\[
([ 1 ] \vee [ K, 1 ]) ^ {*} := \left\{ \begin{array}{l l} \{\{0 \}, \{1 \}, \{2 \} \} & \text {if n = 0} \\ \mathbb {N} [ e _ {1} ] \oplus \cup \{[ x, 1 ], x \in K _ {0} ^ {*} \} & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} ^ {*} \} & \text {if n > 1} \end{array} \right.
\]

- The augmentations \( e \) are the unique morphism fulfilling

\[
e (\{0 \}) = e (\{1 \}) = e (\{2 \}) = 1.
\]

Proposition 1.2.2.15. Let A be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexes  \( [A,1]\vee[1] \)  and  \( [1]\vee[A,1] \)  have no non-trivial automorphisms.

Proof. The proof is similar to the one of proposition 1.2.2.12 and we leave it to the reader. \(\square\)

52

1.2. GRAY OPERATIONS

#### 1.2.2.16. There are two canonical morphisms

$$\nabla : \Sigma K \rightarrow \Sigma K \vee [1] \qquad \nabla : \Sigma K \rightarrow [1] \vee \Sigma K$$

that are the unique ones fulfilling

$$\nabla(\{0\}) := \{0\} \quad \nabla(\{1\}) := \{2\} \quad \nabla([x, 1]) := \begin{cases} [x, 1] + e_1 & \text{if } |x| = 0 \\ [x, 1] & \text{if } |x| > 0 \end{cases}$$

When we write $\Sigma K \rightarrow \Sigma K \vee [1]$ and $\Sigma K \rightarrow [1] \vee \Sigma K$ and nothing more is specified, it will always mean that we considered the morphisms $\nabla$.

**Proposition 1.2.2.17.** *Let $K$ be an augmented directed complex. There is a natural transformation between the colimit of the following diagram*

$$[1] \vee [K, 1] \longleftarrow [K \otimes \{0\}, 1] \longrightarrow [K \otimes [1], 1] \longleftarrow [K \otimes \{1\}, 1] \longrightarrow [K, 1] \vee [1]$$

and $[K, 1] \otimes [1]$.

*Proof.* The cone is induced by morphisms

$$\begin{aligned} & [1] \vee [K, 1] \rightarrow [K, 1] \otimes [1] \\ & (\text{resp. } [K, 1] \vee [1] \rightarrow [K, 1] \otimes [1]) \end{aligned}$$

sending an element $x$ in the basis of $[1]$ to $\{0\} \otimes x$ (resp. $\{1\} \otimes x$), an element $y$ in the basis of $[K, 1]$ to $y \otimes \{1\}$ (resp. $y \otimes \{0\}$), and by the morphism

$$f : [K \otimes [1], 1] \rightarrow [K, 1] \otimes [1]$$

defined by the formula

$$f([x \otimes y, 1]) := [x, 1] \otimes y$$

for $x$ in the basis of $K$ and $y$ in the basis of $[1]$. We leave it to the reader to check the compatibilities of this three morphisms. $\square$

### 1.2.3 Gray operations on $(0, \omega)$-categories

We follow Ara-Maltsiniotis [AM20] for the definitions and first properties of Gray operations on $(0, \omega)$-categories. Originally, these authors work with $\omega$-categories, and not with $(0, \omega)$-categories. However, this modification does not affect proof, and we then allow ourselves to use their results in our framework.

**Theorem 1.2.3.1** (Steiner, Ara-Maltsiniotis). *There is a unique colimit preserving monoidal structure on $(0, \omega)$-cat, up to a unique monoidal isomorphism, making the functor $\nu_{|\text{ADC}_\text{B}} : \text{ADC}_\text{B} \rightarrow (0, \omega)$-cat a monoidal functor, when $\text{ADC}_\text{B}$ is endowed with the monoidal structure given by the Gray tensor product.*

*Proof.* This is [AM20, theorem A.15]. $\square$

53

CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

1.2.3.2. The monoidal product on  \( (0,\omega) \) -cat induced by the previous theorem is called the Gray tensor product and is denoted by  \( \otimes \) . It's unit is  \( D_{0} \) . If C and D are  \( (0,\omega) \) -categories with an atomic and loop free basis, we have by construction

\[
C \otimes D := \nu (\lambda C \otimes \lambda D).
\]

The induced functor

\[
\_ \otimes [ 1 ]: (0, \omega) \text {-cat} \to (0, \omega) \text {-cat}
\]

is called the Gray cylinder.

Proposition 1.2.3.3. Let \(C\) be an \((\infty, \omega)\)-category. The following canonical square

![img-33.jpeg](img-33.jpeg)

is cocartesian

Proof. As all these functors commute with colimits, it is sufficient to demonstrate this assertion when C is a globular sum, and a fortiori when C admits a loop free and atomic basis. In this case, remark that all the morphisms appearing in canonical cartesian square

![img-34.jpeg](img-34.jpeg)

are quasi-rigid. The results then follow from an application of theorem 1.2.1.26.

1.2.3.4. Applying the duality  \( (\_)^{op} \)  to the computation achieved in appendix B.1 of [AM20], we can give an explicit expression of  \( D_{n} \otimes [1] \) . As a polygraph, the generating arrows of  \( D_{n} \otimes [1] \)  are:

\[
e _ {k} ^ {\epsilon} \otimes \{0 \} \qquad e _ {k} ^ {\epsilon} \otimes \{1 \} \qquad e _ {k} ^ {\epsilon} \otimes [ 1 ]
\]

\[
a _ {0} ^ {-} \otimes e _ {k} ^ {\epsilon} \qquad a _ {0} ^ {+} \otimes e _ {k} ^ {\epsilon} \qquad a \otimes e _ {k} ^ {\epsilon}
\]

where \(\epsilon\) is either \(+\) or \(-\), \(k \leqslant n\) and \(e_n^+ = e_n^-\). Their source and target are given as follows:

\[
\pi^ {-} (e _ {k} ^ {\epsilon} \otimes \{0 \}) = e _ {k - 1} ^ {-} \otimes \{0 \} \qquad \qquad \pi^ {+} (e _ {k} ^ {\epsilon} \otimes \{0 \}) = e _ {k - 1} ^ {+} \otimes \{0 \}
\]

\[
\pi^ {-} (e _ {k} ^ {\epsilon} \otimes \{1 \}) = e _ {k - 1} ^ {-} \otimes \{1 \} \qquad \qquad \pi^ {+} (e _ {k} ^ {\epsilon} \otimes \{1 \}) = e _ {k - 1} ^ {+} \otimes \{1 \}
\]

\[
\pi^ {-} (e _ {2 k} ^ {\epsilon} \otimes [ 1 ]) = \ldots \circ_ {2} (e _ {0} ^ {+} \otimes [ 1 ]) \circ_ {0} (e _ {2 k} ^ {\epsilon} \otimes \{0 \}) \circ_ {1} (e _ {1} ^ {-} \otimes [ 1 ]) \circ_ {3} \ldots \circ_ {2 k - 1} (e _ {2 k - 1} ^ {-} \otimes [ 1 ])
\]

54

1.2. GRAY OPERATIONS

\[
\pi^ {+} (e _ {2 k} ^ {\epsilon} \otimes [ 1 ]) = (e _ {2 k - 1} ^ {+} \otimes [ 1 ]) \circ_ {2 k - 1} \dots \circ_ {3} (e _ {1} ^ {+} \otimes [ 1 ]) \circ_ {1} (e _ {2 k} ^ {\epsilon} \otimes \{1 \}) \circ_ {0} (e _ {0} ^ {-} \otimes [ 1 ]) \circ_ {2} \dots
\]

\[
\pi^ {-} (e _ {2 k + 1} ^ {\epsilon} \otimes [ 1 ]) = \ldots \circ_ {3} (e _ {1} ^ {+} \otimes [ 1 ]) \circ_ {1} (e _ {2 k + 1} ^ {\epsilon} \otimes \{1 \}) \circ_ {0} (e _ {0} ^ {-} \otimes [ 1 ]) \circ_ {2} \ldots \circ_ {2 k} (e _ {2 k} ^ {-} \otimes [ 1 ])
\]

\[
\pi^ {+} (e _ {2 k + 1} ^ {\epsilon} \otimes [ 1 ]) = (e _ {2 k} ^ {+} \otimes [ 1 ]) \circ_ {2 k} \dots \circ_ {2} (e _ {0} ^ {+} \otimes [ 1 ]) \circ_ {0} (e _ {2 k + 1} ^ {\epsilon} \otimes \{0 \}) \circ_ {1} (e _ {1} ^ {-} \otimes [ 1 ]) \circ_ {3} \dots
\]

We did not put parenthesis in the expression above, to keep them shorter, the default convention is to do the composition \(\circ_{i}\) in order of increasing values of \(i\).

Example 1.2.3.5. The \((0,\omega)\)-category \(\mathbf{D}_1\otimes [1]\) is the polygraph:

![img-35.jpeg](img-35.jpeg)

The \((0,\omega)\)-category \(\mathbf{D}_2\otimes [1]\) is the polygraph:

![img-36.jpeg](img-36.jpeg)

1.2.3.6. We define the Gray cone and the Gray o-cone:

\[
\begin{array}{c c c c c c} (0, \omega) \text {-cat} & \to & (0, \omega) \text {-cat.} & (0, \omega) \text {-cat} & \to & (0, \omega) \text {-cat.} \\ C & \mapsto & C \star 1 & C & \mapsto & 1 \stackrel {{c o}} {{\star}} C \end{array}
\]

where \(C\star 1\) and \(1\stackrel {co}{\star}C\) are defined as the following pushout:

![img-37.jpeg](img-37.jpeg)

Example 1.2.3.7. The \((0,\omega)\)-categories \(\mathbf{D}_1\star 1\) and \(1\stackrel {co}{\star}\mathbf{D}_1\) correspond respectively to the polygraphs:

![img-38.jpeg](img-38.jpeg)

The \((0,\omega)\)-categories \(\mathbf{D}_2\star 1\) and \(1\stackrel {co}{\star}\mathbf{D}_2\) correspond respectively to the polygraphs:

![img-39.jpeg](img-39.jpeg)

55

CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

**Proposition 1.2.3.8.** *Let C be an (0, ω)-category with an unitary and loop free basis. The canonical comparaisons*

$$(\lambda C) \star 1 \to \lambda(C \star 1) \qquad 1 \stackrel{co}{\star} (\lambda C) \to \lambda(1 \stackrel{co}{\star} C)$$

*are equivalences.*

*Let K be an augmented directed complex with a loop free and unitary basis. The canonical comparaisons*

$$(\nu K) \star 1 \to \nu(K \star 1) \qquad 1 \stackrel{co}{\star} (\nu K) \to \nu(1 \stackrel{co}{\star} K)$$

*are equivalences.*

*Proof.* The first assertion directly follows from the fact λ commutes with colimits. For the second one, we can easily check that all the morphisms appearing in the squares (1.2.2.6) are quasi-rigid. The results then follow from an application of theorem 1.2.1.26. □

**1.2.3.9.** We now give some technical results that we will use later.

**Lemma 1.2.3.10.** *Let S be the smallest set of (0, ω)-categories such that*

(1) S is stable by isomorphisms,
(2) the terminal (0, ω)-category belong to S,
(3) S is stable by _ * 1, 1 *co* _ , [_, 1], [_, 1] ∨ [1] and [1] ∨ [_, 1].

*Then, the (0, ω)-categories belonging to S have non non-trivial automorphisms.*

*Proof.* The set of (0, ω)-categories admitting an atomic and loop free basis fulfills the three condition. As a consequence, every (0, ω)-category in S has an atomic and loop free basis. Using theorem 1.2.1.23, it is then sufficient to show that any augmented directed complex in λ(S) has no non-trivial automorphisms. The result then follows from propositions 1.2.2.8, 1.2.2.12 and 1.2.2.15. □

**Proposition 1.2.3.11.** *Let n be an integer n. The (0, ω)-categories D_n and 1 * 1 * ... * 1 have no non-trivial automorphisms.*

*Proof.* This is a direct consequence of lemma 1.2.3.10 as these two (0, ω)-categories belong to S. □

56

1.2. GRAY OPERATIONS

**1.2.3.12.** The following propositions express the link between the Gray operations and the suspension. They will play a fundamental role in the rest of this work.

**Theorem 1.2.3.13.** *Let $C$ be an $(0, \omega)$-category. There is a natural identification between $[C, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [C, 1] \longleftarrow [C \otimes \{0\}, 1] \longrightarrow [C \otimes [1], 1] \longleftarrow [C \otimes \{1\}, 1] \longrightarrow [C, 1] \vee [1]$$

*Proof.* As all these functors preserve colimits, it is sufficient to construct the comparison when $C$ is a globular sum, and to show that it is an equivalence when $C$ is a globe. As globular sums have atomic and loop free bases, the comparison is induced by proposition 1.2.2.17. Using the explicit description of the $(0, \omega)$-category $\mathbf{D}_n \otimes [1]$ given in paragraph 1.2.3.4, it is straightforward to see that it induces an equivalence on globes. $\square$

The definitional cocartesian squares

$$\begin{array}{ccc} C \otimes \{1\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & C \star 1 \end{array} \qquad \begin{array}{ccc} C \otimes \{0\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{\text{co}}{\star} C \end{array}$$

imply the following proposition:

**Theorem 1.2.3.14.** *There is a natural identification between $1 \stackrel{\text{co}}{\star} [C, 1]$ and the colimit of the following diagram*

$$[1] \vee [C, 1] \longleftarrow [C, 1] \longrightarrow [C \star 1, 1]$$

*There is a natural identification between $[C, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\text{co}}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1]$$

**Proposition 1.2.3.15.** *Let $C$ be an $(0, \omega)$-category with an atomic and loop free basis. The two following canonical squares are cartesian:*

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \stackrel{\text{co}}{\star} C \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [C, 1] \end{array} \qquad \begin{array}{ccc} 1 & \longrightarrow & C \star 1 \\ \downarrow & & \downarrow \\ \{1\} & \longrightarrow & [C, 1] \end{array}$$

*The five squares appearing in the following canonical diagram are both cartesian and*

57

CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

cocartesian:

![img-40.jpeg](img-40.jpeg)

Proof. The five squares are cocartesian by construction. Since the proofs of the cartesianess of all squares are identical, we will only show the proof for the square

![img-41.jpeg](img-41.jpeg)

To this extend, remark that for any integer n, the following square is cartesian.

![img-42.jpeg](img-42.jpeg)

This then implies that the following square in the category ADC is cartesian.

![img-43.jpeg](img-43.jpeg)

As ν is a right adjoint, it preserves limits, and as it commutes with Gray operation, this concludes the proof.

Lemma 1.2.3.16. Let a, b, c and d be four globular sums. Suppose given a cartesian square:

![img-44.jpeg](img-44.jpeg)

where the two horizontal morphisms are globular. The two following squares are cartesian

![img-45.jpeg](img-45.jpeg)

58

1.2. GRAY OPERATIONS

Proof. We show only the cartesianess of the first square, as the cartesianess of the second one follows by applying the duality $(\_)^\circ$. A direct computation shows that for any integer $n$, the following square is cartesian

![img-46.jpeg](img-46.jpeg)

To conclude, one has to show that the canonical morphism

$$\nu(\lambda b) \coprod_{\nu(\lambda a)} \nu(\lambda a \star 1) \to \nu(\lambda b \coprod_{\lambda a} \lambda a \star 1)$$

is an equivalence. As $a \to b$ is globular, all the morphisms of the following cocartesian square are quasi-rigid.

![img-47.jpeg](img-47.jpeg)

The results then follow from an application of theorem 1.2.1.26.

1.2.3.17. The end of this section is devoted to proving the following theorem:

Theorem 1.2.3.18. Let $F$ be an endofunctor of $(0, \omega)$-cat such that the induced functor $(0, \omega)$-cat $\to (0, \omega)$-cat$_{F(\emptyset)/}$ is colimit preserving and $\psi$ an invertible natural transformation between $G \cup \{\emptyset\} \to (0, \omega)$-cat $\xrightarrow{F} (0, \omega)$-cat and $G \cup \{\emptyset\} \to (0, \omega)$-cat $\xrightarrow{G} (0, \omega)$-cat where $G$ is either the Gray cylinder, the Gray cone, the Gray $\circ$-cone or an iterated suspension.

Then, the natural transformation $\psi$ can be extended to an invertible natural transformation between $F$ and $G$.

The previous theorem implies that the equations given in theorem 1.2.3.13 and 1.2.3.14 characterize respectively the Gray cylinder, the Gray cone, and the Gray $\circ$-cone. We also have the following corollary:

Corollary 1.2.3.19. The colimit preserving endofunctor $F : (0, \omega)$-cat $\to (0, \omega)$-cat, sending $[a, n]$ to the colimit of the span

$$\coprod_{k \le n} \{k\} \leftarrow \coprod_{k \le n} a \otimes \{k\} \to a \otimes [n]$$

is equivalent to the identity.

59

CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

Proof. The theorem 1.2.3.13 implies that the restriction of F to globes is equivalent to the restriction of the identity to globes. As the identity is the 0-iterated suspension, we can apply theorem 1.2.3.18. □

Lemma 1.2.3.20. A sub category Θ' of Θ, stable by colimit and containing globular morphisms is equal to Θ iff

(1) for any integer n, i_n^- : D_n → D_{n+1} belongs to Θ'.
(2) For any integer n, the unit I_n : D_{n+1} → D_n belongs to Θ'.
(3) For any pair of integers k < n, the composition ∇_{k,n} : D_n → D_n ∐_k D_n belongs to Θ'.

Proof. Suppose that Θ' fulfills these conditions. As globular morphisms are compositions of pushouts along morphisms of shape i_n^-, they belong to Θ'. As algebraic morphisms are compositions of colimits of morphism of shape ∇_{k,n} or I_n, they belong to Θ'. The result then follows from [Ara10, proposition 3.3.10] that states that every morphism factors as an algebraic morphism followed by a globular morphism. □

Lemma 1.2.3.21. Let n be an integer, and G be either the Gray cylinder, the Gray cone, the Gray o-cone or an iterated suspension, and suppose given a square

![img-48.jpeg](img-48.jpeg)

Then, the morphism f is G(I_n).

Proof. As the proof for any possibilities of G are similar, we will show only the case G := _ ⊗ [1]. As for any integer n, D_n ⊗ [1] admits a loop free and atomic basis, we can then show the desired assertion after applying the functor λ. Remark first that the assumption implies that ∂f((e_{n+1} ⊗ {α}) = 0, and so f((e_{n+1} ⊗ {α}) = 0. We also have f(e_{n+1} ⊗ [1]) = 0 as (λ(D_n ⊗ [1])_{n+2} = 0. This implies that f is equal to λ(G(I_n)). □

Lemma 1.2.3.22. Let k < n be two integers, and G be either the Gray cylinder, the Gray

60

1.2. GRAY OPERATIONS

cone, the Gray o-cone or an iterated suspension, and suppose given a square

$$\begin{array}{c} G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \\ \searrow G(i_n^-) \searrow \searrow G(\mathbf{D}_n) \xrightarrow{f} G(\mathbf{D}_n \coprod_k \mathbf{D}_n) \\ \searrow G(i_n^+) \searrow \searrow G(i_n^+) \coprod_k G(i_n^+) \\ G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \end{array}$$

where we set $\nabla_{n,n} := id$. Then, the morphism $f$ is $G(\nabla_{n,k})$.

Proof. As the proof for any possibilities of $G$ are similar, we will show only the case $G := \_ \otimes [1]$. As for any integer $n$, $\mathbf{D}_n \otimes [1]$ admits a loop free and atomic basis, we can then show the desired assertion after applying the functor $\lambda$. Suppose first that $k < n-1$. By assumption, we have

$$\partial f(e_n \otimes \{\alpha\}) = \partial(e_n^0 \otimes \{\alpha\} + e_n^1 \otimes \{\alpha\})$$

$$\partial f(e_n \otimes [1]) = \partial(e_n^0 \otimes [1]) + \partial(e_n^1 \otimes [1])$$

This forces the equalities

$$f(e_n \otimes \{\alpha\}) = e_n^0 \otimes \{\alpha\} + e_n^1 \otimes \{\alpha\}$$

$$f(e_n \otimes [1]) = e_n^0 \otimes [1] + e_n^1 \otimes [1]$$

and $f$ is then equal to $\nabla_{n,k} \otimes [1]$. The case $k = n-1$ is similar.

Proof of theorem 1.2.3.18. As every globular sum is a colimit of globes, we can extend $\psi$ to a (a priori non natural) transformation, $\psi : F_{|\Theta} \to G_{|\Theta}$. Let $\Theta'$ be the maximal sub category of $\Theta$ such that $\psi_{\Theta'}$ is an equality. As $G(\mathbf{D}_n)$ does not have non trivial automorphisms, the assumption implies that $\Theta'$ fulfills the first condition of lemma 1.2.3.20. The lemma 1.2.3.21 implies that it fulfills the second condition, and an easy induction on $(n-k)$ using lemma 1.2.3.22 implies that it fulfills the last condition. Applying the lemma 1.2.3.20, this concludes the proof.

61

CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

62

# Part I

## On the side of models

63



# Chapter 2

## Study of the complicial model

### Contents

|  **2.1 Preliminaries** | **67**  |
| --- | --- |
|  2.1.1 Generalities on model categories | 67  |
|  2.1.2 Marked and stratified presheaves | 70  |
|  **2.2 The complicial model** | **73**  |
|  2.2.1 Model structure on marked simplicial sets | 73  |
|  2.2.2 Gray tensor product | 76  |
|  2.2.3 Gray cylinder, Gray cone and Gray o-cone | 84  |
|  2.2.4 Street nerve | 85  |
|  **2.3 Suspension and Gray operations** | **87**  |
|  2.3.1 Formula for the Gray cylinder | 87  |
|  2.3.2 Formulas for the Gray cone and the Gray o-cone | 90  |
|  **2.4 Globular equivalences** | **93**  |
|  2.4.1 Homotopy categories | 93  |
|  2.4.2 A criterion to be a weak equivalence | 97  |
|  2.4.3 A criterion to be a weakly invertible transformation | 101  |
|  2.4.4 Weak characterization of the identity | 103  |

This chapter is devoted to the study of Verity's complicial sets ([Ver08b]). One of the benefits of complicial sets is that they admit a simple definition of the Gray tensor product. Being strongly linked to $(0, \omega)$-categories by the Street nerve, they are also a

65

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

privileged framework for stating and proving strictification results, as done in [OR20a], [GOR21], [OR22] and [Mae23]. However, they do not interact a priori well with the globular language. The goal of this chapter is to show that, with some computation, it is possible to have a globular point of view in this model.

The first section is a recollection of usual results and definitions about complicial sets. In the second section, we aim to prove an analogue of the formula given in 1.2.3.13 to the complicial setting. We also have a suspension in this category, which is denoted by $X \mapsto \Sigma X$. Objects $[1] \vee \Sigma X$ and $\Sigma X \vee [1]$ are defined in 2.2.2.19, but for now, we can suppose that they are fibrant replacements of respectively $[1] \coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \vee [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:

$$\Sigma X \vee [1] \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \hookleftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \vee \Sigma X.$$

We also provide similar formulas for the Gray cone and Gray o-cone:

**Theorem 2.3.2.1.** There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \star [0]$ and the colimit of the following diagram:

$$\Sigma X \vee [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{co}{\star} X).$$

There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{co}{\star} \Sigma X$ and the colimit of the following diagram:

$$\Sigma(X \star [0]) \leftarrow \Sigma X \to [1] \vee \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[i_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[i_3^-]{i_3^+} \dots$$

**Theorem 2.4.4.14.** Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.

66

2.1. PRELIMINARIES

Proposition 15.10 of [BSP21] provides a similar result for models of  \( (\infty, n) \) -categories.

### 2.1 Preliminaries

#### 2.1.1 Generalities on model categories

For this chapter, we fix a model category C whose cofibrations are monomorphisms.

2.1.1.1. We give first some results on homotopy colimits. These results will be used freely throughout these first two chapters.

Proposition 2.1.1.2. Suppose given a square

![img-49.jpeg](img-49.jpeg)

such that the two horizontal morphisms are weak equivalences. Then this square is homotopy cocartesian.

Proof. This is [Cis19, proposition 2.3.26].

Proposition 2.1.1.3. Suppose given a cocartesian square

![img-50.jpeg](img-50.jpeg)

where the left vertical morphism is a cofibration. Then this square is homotopy cocartesian.

Proof. This is [Cis19, corollary 2.3.28].

Proposition 2.1.1.4. Let \( F: \alpha \to C \) be a diagram indexed by an ordinal. The transfinite composition \( \operatorname{colim}_{\alpha} F \) is the homotopy colimit of the diagram \( F \).

Proof. This is [Cis19, proposition 2.3.13].

Proposition 2.1.1.5. Suppose given a diagram

![img-51.jpeg](img-51.jpeg)

where all morphisms labelled by  \( \hookrightarrow \)  are cofibrations. The colimit of this diagram is also the homotopy colimit of this diagram.

67

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Proof. Let $I_n$ be the category indexing the previous diagram. We denote $i_0, j_0, \ldots, i_{n-1}, j_{n-1}, i_n$ it's objects. The projective model structure on $\operatorname{Fun}(I_n, C)$ is given by functor $G$ such that for any $k < n$, $F(j_k) \to F(i_k)$, $F(j_k) \to F(i_{k+1})$ are monomorphisms, and such that for any $0 < k < n$, $F(j_k) \coprod F(j_{k+1}) \to F(i_k)$ is a monomorphism. Remark that such presheaves verify the condition given in the statement of the proposition.

We will show on induction on $n$ that a natural transformation $\psi$ between two diagrams $F, G : I_n \to C$ that fulfills the desired condition induces a weak equivalence between their colimits. As we can always chose $F$ to be the cofibrant replacement of $G$ in the projective model structure on $\operatorname{Fun}(I_n, C)$, it will imply the desired result.

The case $n = 1$ is proposition 2.1.1.3. Suppose now the result is true at the stage $(n - 1)$ and let $\psi$ be a weakly invertible natural transformation between two diagram $F, G : I_n \to C$ that fulfills the desired condition. We denote by $\iota : I_{n-1} \to I_n$ the canonical inclusion that sends $i_k(\text{resp. } j_k)$ on $i_k(\text{resp. } j_k)$ for $k < n$ (resp. $k < n - 1$). We then have a diagram

$$\begin{array}{c} \operatorname{colim}_{I_{n-1}} F \circ \iota \longleftarrow F(j_{n-1}) \hookrightarrow F(i_n) \\ \sim \downarrow \qquad \qquad \qquad \sim \downarrow \qquad \qquad \sim \downarrow \\ \operatorname{colim}_{I_{n-1}} G \circ \iota \longleftarrow G(j_{n-1}) \hookrightarrow G(i_n) \end{array}$$

where all arrows labeled by $\sim$ are weak equivalences. Remark furthermore that the limit of the two lines are respectively $\operatorname{colim}_{I_n} F$ and $\operatorname{colim}_{I_n} G$. A last application of proposition 2.1.1.3 concludes the proof.

2.1.1.6. The definition of elegant Reedy category is given in paragraph 1.1.2.5. As all the presheaves categories that we will encounter through this text are presheaves on elegant Reedy categories, we will use freely the following theorem:

Theorem 2.1.1.7 (Hirschhorn). We suppose that $C$ is a simplicial model category. Let $A$ be a elegant Reedy category, and $F : A \to C$ a functor such that the induced morphism $\operatorname{colim}_{\partial a} F \to F(a)$ is a monomorphism for any object $a$. The object $\operatorname{colim}_A F$ is the homotopy colimit of $F$. In particular, if $C$ is $\operatorname{Psh}(A)$, every object $X$ is the homotopy colimit of the diagram $A_{/X} \to A \to \operatorname{Psh}(A)$.

Proof. Using the characterization of elegant Reedy category given by proposition 3.8 of [BR13b], and [Hir03, proposition 15.10.2], it's easy to see that they have fibrant constant in the sens of [Hir03, definition 15.10.1]. We can then apply the theorem 19.9.1 of [Hir03].

2.1.1.8. A model structure is nice if it is simplicial, combinatorial, cartesian and its cofibrations are monomorphisms.

68

2.1. PRELIMINARIES

**Notation 2.1.1.9.** Let $\_\Box\_: C \times D \rightarrow E$ be a bifunctor. If $f: a \rightarrow b$ and $g: x \rightarrow y$ are respectively morphisms of $C$ and $D$, we will note by $f \triangleq g$ the induced morphism $a\Box y \coprod_{a\Box x} b\Box x \rightarrow b\Box y$.

**Proposition 2.1.1.10** ([Lur09a, proposition A.3.7.3]). *Let $A$ be a nice model structure and $S$ a set of cofibrations. There exists a model structure $A_S$ on the same category, and a left Quillen adjoint $L: A \rightarrow A_S$, such that an object is fibrant in $A_S$ if and only if it is fibrant in $A$ and has the right lifting property against all morphisms of shape $i \hat{\times} f$ where $i$ is a cofibration and $f$ in $S$. Moreover, a left Quillen functor $F: A \rightarrow C$ lifts to $A_S$ if and only if for any cofibration $i$ and morphism $f \in S$, $F(i \hat{\times} f)$ is a weak equivalence.*

**Corollary 2.1.1.11.** *Let $A, C$ be two nice model categories, $F: A \rightarrow C$ a left Quillen functor, $S$ a set of cofibrations and $T$ a set of morphisms such that for any cofibrations $i$ and morphisms $f \in S$, the morphism $i \hat{\times} f$ is included in the smallest saturated class stable by two out of three, containing weak equivalences and $T$. Then a left Quillen functor $F: A \rightarrow C$ lifts to $A$ if and only if it sends morphisms of $T$ to weak equivalences.*

*Proof.* Let $U$ be the class of morphisms in $A$ that are sent to weak equivalences by $F$. This class is obviously stable by two out of three, retracts and contains weak equivalences. As the model structure on $C$ is combinatorial and left proper, it is saturated. The class $U$ then includes all morphisms of shape $i \hat{\times} f$ for $i$ a cofibration and $f \in S$, which implies that $F$ can be lifted to $A_S$. $\Box$

**2.1.1.12.** Let $i: A \rightarrow B$ and $i': A' \rightarrow B'$ be two cofibrations. A *zigzag of acyclic cofibration* between $i$ and $i'$, denoted $i \leftrightarrow i'$ is a zigzag in the category of arrows such that all the horizontal maps are acyclic cofibrations, and all the vertical maps are cofibrations.

**Lemma 2.1.1.13.** *Let $i$ and $j$ be two cofibrations, and $f: X \rightarrow Y$ a fibration between fibrant objects. Suppose that we have a morphism in the category of arrows $i \rightarrow j$ which is pointwise an acyclic cofibration. Then, if $j$ has the left lifting property against $f$, so has $i$.*

*Proof.* We consider a diagram of the following shape:

![img-52.jpeg](img-52.jpeg)

We construct, one after the other, the lifting $l_0, l_1$ and $l_2$. $\Box$

69

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Lemma 2.1.1.14. Let i and j be two cofibrations, and  \( f: X \to Y \)  a fibration between fibrant objects. Suppose that we have a morphism in the category of arrows  \( i \to j \)  which is pointwise an acyclic cofibration. Then, if i has the right lifting property against f, so has j.

Proof. We consider a diagram of the following shape:

![img-53.jpeg](img-53.jpeg)

We construct, one after the other, the lifting \( l_0 \), \( l_1 \).

Proposition 2.1.1.15. Let f be a fibration between fibrant objects and i and j two cofibrations such that there exists a zigzag of acyclic cofibrations  \( i \leftrightarrow j \) . Then f has the right lifting property against i if and only if it has the right lifting property against j.

Proof. This is a direct consequence of the last two lemmas.

#### 2.1.2 Marked and stratified presheaves

2.1.2.1. Let B be an elegant Reedy category and M a subset of the set of objects of B. A M-stratified presheaf on B, or just a stratified prehsheaf on B when the subset M will be non-ambiguous, is a pair  \( (X, tX) \)  where X is a presheaf on B and  \( tX := \coprod_{a \in M} tX_a \)  is the disjoint union of sets, such that for any  \( a \in M \) ,  \( tX_a \)  is a subset of  \( X_a \)  including degeneracies, i.e the image of morphisms  \( X_p : X_b \to X_a \)  for  \( p : b \to a \)  in  \( B_- \) .

A stratified morphism  \(  f : (X, tX) \to (Y, tY)  \)  is the data of a morphism on the underlying presheaf such that  \(  f(tX_n) \subset tY_n  \) . The category of stratified presheaves is denoted by  \(  \text{tPsh}_M(B)  \) .

A morphism between two stratified presheaves is entire if it is the identity on the underlying presheaves.

We then have an adjunction

\[
(\_) ^ {\flat}: \operatorname{Psh} (B) \xrightarrow [ \leftarrow ]{\perp} \operatorname{tPsh} _ {M} (B): (\_) ^ {\natural}
\]

where the left adjoint is a fully faithful inclusion that sends a presheaf X onto  \( (X, S) \)  where S is the smaller stratification on X, and where the right adjoint is the obvious forgetful functor. We will identify presheaves on B with their image by the functor  \( (\_)^{\flat} \) .

70

2.1. PRELIMINARIES

**2.1.2.2.** If $b$ is an object of $M$, we denote by $b_t$ the stratified presheaf $(b, S)$, where $S$ is the smaller stratification that includes $id : b \rightarrow b$.

We then define $t_M B$ as the full subcategory of $\mathrm{tPsh}_M(B)$ spanned by the objects of shape $a$ or $b_t$ with $a \in B$ and $b \in M$. We then have equalities:

$$\begin{aligned} \mathrm{Hom}_{t_M B}(a, b) &:= \mathrm{Hom}_B(a, b), \\ \mathrm{Hom}_{t_M B}(a, b_t) &:= \mathrm{Hom}_B(a, b), \\ \mathrm{Hom}_{t_M B}(a_t, b) &:= \mathrm{Hom}_B(a, b) \cap B_- \setminus \{id_a\}, \\ \mathrm{Hom}_{t_M B}(a_t, b_t) &:= \mathrm{Hom}_B(a, b) \cap B_-. \end{aligned}$$

The canonical functor $B \rightarrow t_M B$ is then fully faithful and we will identify object of $B$ with their image through this functor.

**Proposition 2.1.2.3.** *The category $t_M B$ admits a structure of elegant Reedy category, that makes the inclusion $B \rightarrow t_M B$ a morphism of Reedy category. There is no non trivial negative morphism whose codomain is of shape $b_t$ for $b \in M$. There is no non trivial positive morphism whose domain is of shape $b_t$ for $b \in M$.*

*Proof.* We define the degree degree function $ob(t_M B) \rightarrow \mathbb{N}$ by the assignment

$$d'(b) := 2d(b) \qquad d'(b_t) := 2d(b) + 1$$

The category $(t_M B)_+$ is the smallest that includes $B_+$ and morphisms of shape $a \rightarrow a_t$. The category $(t_M B)_-$ is the smallest that includes $B_-$ and morphisms of shape $b_t \rightarrow a$.

To prove the axioms of Reedy category, we can replicate the strategy used in proposition C.2 of [OR20b] with obvious modification to this more general framework.

We still have to show that $tB$ is elegant. Let $X$ be a presheaf on $t_M B$, $a$ an element of $t_M B$, $f : a \rightarrow a'$ and $g : a \rightarrow a'$ two negative morphisms, an element $x$ of $X(a)$, two non degenerate elements $y \in X(a')$ and $z \in X(a'')$ such that $f^*y = x$, $g^*z = x$.

Suppose first that $a$ is in $B$. In this case, $f$ and $g$ are also in $B$, and as this Reedy category is elegant by assumption, this implies $f = g$ and $y = z$. Suppose now that $a$ is of shape $b_t$ for $b \in B$. We denote $\alpha$ the canonical morphism $\alpha : b \rightarrow b_t$. By definition of negative morphism, the codomain of $f$ and $g$ are in $B$. The morphisms $\alpha f$ and $\alpha g$ then are in $B$. Moreover, these two morphisms are negative, and we have $(\alpha f)^*y = \alpha^*x$, $(\alpha g)^*z = \alpha^*x$. As $B$ is elegant, $\alpha f = \alpha g$ and $y = z$. Eventually, remark that the first equality implies that $f$ is equal to $g$. $\square$

A cellular model for $t_M B$ is given by $C \cup \{b \rightarrow b_t, b \in M\}$ where $C$ is a cellular model for $B$.

71

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

2.1.2.4. The category of $M$-stratified presheaves is then equivalent to the fully faithful subcategory of presheaves $X$ on $t_M B$ such that for any $b \in M$, $X(b_t) \to X(b)$ is a monomorphism. In particular, we have an adjunction

$$\pi : \mathrm{Psh}(t_M B) \xrightarrow{\perp} \mathrm{tPsh}_M(B) : \iota \tag{2.1.2.5}$$

Remark furthermore that the unit $X \to \iota\pi X$ is a trivial fibration. Indeed, the cellular model is given $C \cup \{b \to b_t, b \in M\}$, where $C$ is a cellular model for $B$, and the unit obviously has the right lifting property against it.

**Proposition 2.1.2.6.** *Suppose given a combinatorial on $\mathrm{Psh}(t_M B)$ whose cofibrations are monomorphisms. Then there exists a combinatorial model structure on $\mathrm{tPsh}_M(B)$ making the adjunction 2.1.2.5 a Quillen equivalence.*

*A morphism of $\mathrm{tPsh}_M(B)$ is a cofibration if and only if it is a monomorphism. A morphism is a fibration (resp. a weak equivalence) if and only if its image by $\iota$ is.*

*Proof.* We are willing to apply [Hir03, theorem 11.3.2]. As two adjoints of (2.1.2.5) preserve smallness, the first condition is obviously fulfilled. Using the fact that $\iota$ is fully faithful, the second condition of theorem *op cit* is equivalent to asking that for any acyclic cofibration $i$ of $\mathrm{Psh}(t_M B)$, the morphism $\iota\pi i$ is a weak equivalence. As the unit $id \to \iota\pi$ is pointwise a trivial fibration, this directly follows from the stability of weak equivalences by two out of three.

This provides the model structure. As the unit is pointwise a trivial fibration and the counit is the identity, the adjunction (2.1.2.5) induces a Quillen equivalence. $\square$

2.1.2.7. We now fix a Reedy category $B$, a subset $M$ of objects of $B$, and we suppose given a nice model structure on $\mathrm{tPsh}_M(B)$ (as defined in paragraph 2.1.1.8). A $M$-marked presheaf on $B$ is a stratified presheaf having the unique right lifting property against all entire acyclic cofibrations. In particular, any fibrant objects is marked.

We denote by $\mathrm{mPsh}_M(B)$ the full subcategory of marked presheaves on $B$. We then have an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}_M(B) \xrightarrow{\perp} \mathrm{mPsh}_M(B) : \iota \tag{2.1.2.8}$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified presheaf $(X, tX)$ to the marked presheaf $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$ a marked presheaf, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of presheaves, these two adjoints are the identity.

**Proposition 2.1.2.9.** *Let $X$ be a $M$-stratified presheaf on $B$. The canonical morphism $X \to \iota(X_{\mathrm{mk}})$ is an entire acyclic cofibration.*

72

2.2. THE COMPLICIAL MODEL

Proof. Let $\kappa$ be a regular cardinal such that $X$ is $\kappa$-small. Remark first the domain of a entire monomorphism is $\kappa$-small if and only if its codomain is.

Let $I$ be the set of entire acyclic cofibrations with $\kappa$-small codomains and domains. This set generates via the small object argument a weak factorization system, and we denote by $X \to X' \to 1$ the factorization of $X \to 1$. We are willing to show that $X'$ is $M$-marked. As $X \to X'$ is an entire acyclic cofibration by construction, this will directly imply that $X'$ is equal to $\iota(X_{\mathrm{mk}})$ and so demonstrate the desired result.

Suppose then given a diagram

![img-54.jpeg](img-54.jpeg)

with $i$ an entire acyclic cofibration. We have to show that it admits a lift. Remark that this square factors as:

![img-55.jpeg](img-55.jpeg)

The morphism $i'$ is an entire acyclic cofibration with $\kappa$-small codomain and domain and then belongs to $i$. The right square of the previous diagram then admits a lift. This induces a lift in the original square, and this concludes the proof.

Proposition 2.1.2.10. Suppose given a nice model structure on $\mathrm{tPsh}_M(B)$. This induces a nice model structure on $\mathrm{mPsh}_M(B)$, making the adjunction (2.1.2.8) a Quillen equivalence. A morphism between two marked presheaves is a cofibration (resp. a fibration) (resp. a weak equivalence) if it is a cofibration (resp. a fibration) (resp. a weak equivalence) when seen as a morphism of $\mathrm{tPsh}_M(B)$.

Proof. Let $f: X \to Y$ be a fibration between stratified presheaves. If $Y$ is marked, so is $X$. The two weak factorization systems on $\mathrm{mPsh}_M(B)$ are then induced by the one of $\mathrm{tPsh}_M(B)$. We leave it to the reader to check that this model structure is nice.

The unit is pointwise a weak equivalence according to proposition 2.1.2.9 and the counit is the identity. The adjunction (2.1.2.8) is then a Quillen equivalence.

## 2.2 The complicial model

### 2.2.1 Model structure on marked simplicial sets

This section is a recollection of the principal results of [OR20b]. We refer to [Rie16] for an introduction to complicial sets.

73

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

**2.2.1.1.** A *stratified simplicial set* is a pair $(X, tX)$ where $X$ is a simplicial set and $tX := \cup_{n>0} tX_n$ a graded set such that for any $n \geq 1$, $tX_n$ is a subset of $X_n$ that includes all degenerate simplices. A simplex in $tX$ is called *thin*.

A *stratified morphism* $f : (X, tX) \to (Y, tY)$ is the data of a morphism on the underlying simplicial set such that $f(tX_n) \subset tY_n$. The category of stratified simplicial sets is denoted by $\text{tPsh}(\Delta)$.

Given a functor $i : I \mapsto (F(i), tF(i))$ with value in stratified simplicial sets, its colimit is given by $(\text{colim } F(i), M)$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \text{colim } F(i)$ for any $i : I$.

We can extend the join to stratified simplicial sets as follows: If $(X, tX)$ and $(Y, tY)$ are two stratified simplicial sets, we define $tX \star tY$ as the set of simplices of $X \star Y$ of shape $x \star y$ where either $x$ or $y$ are thin. We then define

$$(X, tX) \star (Y, tY) := (X \star Y, tX \star tY).$$

**Definition 2.2.1.2.** A stratified monomorphism $f : X \to Y$ is

(1) *entire* if it is an identity on underlying simplicial sets.
(2) *regular* if for every $n \geq 1$ the following diagram is a pullback:

$$\begin{array}{ccc} tX_n & \longrightarrow & X_n \\ \downarrow & \downarrow & \downarrow \\ tY_n & \longrightarrow & Y_n. \end{array}$$

**Definition 2.2.1.3.** We define several stratified structures on $[n]$.

(1) $[n]_t$. The top $n$-simplex is thin. All degeneracies are thin.
(2) $[n]^k$. All simplices that include $\{k-1, k, k+1\} \cap [n]$ are thin. All degeneracies are thin.
(3) $([n]^k)'$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(4) $([n]^k)''$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face, the $k$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(5) $[3]^{eq}$. All simplices of dimension strictly higher than 2, together with $[0, 2]$ and $[1, 3]$ are thin. All degeneracies are thin.
(6) $[n]^2$. All simplices are thin.

**Definition 2.2.1.4.** An *elementary anodyne extension* is one of the following:

74

2.2. THE COMPLICIAL MODEL

(1) The *complicial horn inclusions* are the regular extensions:

$$\Lambda^k[n] \to [n]^k, \ n \ge 1, \ n \ge k \ge 0.$$

(2) The *complicial thinness extensions*:

$$([n]^k)' \to ([n]^k)'', \ n \ge 2, \ n \ge k \ge 0.$$

(3) The *saturation extensions*:

$$[n] \star [3]^{eq} \star [m] \to [n] \star [3]^\sharp \star [m], \ n, m \ge -1.$$

The set of complicial horn inclusions is $\Lambda$ and the reunion of *complicial thinness extensions* and of *saturation extensions* is $S$.

**Definition 2.2.1.5.** Let $n \in \mathbb{N} \cup \{\omega\}$. A $n$-*complicial set* is a stratified set having the right lifting property against all elementary anodyne extensions and against all morphisms $[k] \to [k]_t$ for $k > n$.

**Theorem 2.2.1.6** (Ozornova, Rovelli, Verity). *Let $n \in \mathbb{N} \cup \{\omega\}$. There exists a nice model structure on stratified simplicial sets, denoted by $\mathrm{tPsh}(\Delta)^n$, whose fibrant objects are $n$-complicial sets.*

*A left adjoint $F : \mathrm{tPsh}(\Delta) \to D$ to a model category is a left Quillen functor if it preserves cofibrations and sends all elementary anodyne extensions and morphisms $[k] \to [k]_t$, for $k > n$, to weak equivalences.*

*Proof.* This is [OR20b, theorem 1.25].

During this chapter, we will only be interested in the model structure for $\omega$-complicial sets, and we will therefore drop the index $\omega$. The $\omega$-complicial sets will then just be called *complicial sets* and we will denote by $\mathrm{tPsh}(\Delta)$ the model category $\mathrm{tPsh}(\Delta)^\omega$.

**2.2.1.7.** A *marked simplicial set* is a stratified simplicial set that has the right lifting property against entire acyclic cofibrations. In particular, all complicial sets are marked. The category of marked simplicial sets is denoted by $\mathrm{mPsh}(\Delta)$. There is an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow[\downarrow]{\perp} \mathrm{mPsh}(\Delta) : \iota \tag{2.2.1.8}$$

The left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified simplicial set $(X, tX)$ to the marked simplicial set $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$

75

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

a marked simplicial set. Moreover, the proposition 2.1.2.9 implies that the canonical morphism $X \to \iota(X)_{\mathrm{mk}}$ is an entire acyclic cofibration.

Given a functor $i: I \mapsto (F(i), tF(i))$ with value in marked simplicial sets, its colimit is given by $(\operatorname{colim} F(i), \overline{M})$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \operatorname{colim} F(i)$ for any $i: I$.

**Proposition 2.2.1.9.** *The category $\mathrm{mPsh}(\Delta)$ admits a nice model structure that makes the adjunction 2.2.1.8 a Quillen equivalence.*

*Proof.* This is a direct consequence of proposition 2.1.2.10 and theorem 2.2.1.6.

**2.2.1.10.** Let $n$ be an integer, and $(X, tX)$ a marked simplicial set. We define $\tau_n^i(tX)$ as the reunion of $tX$ and all simplices of dimension strictly superior to $n$. This induces a functor, called the *intelligent $n$-truncation*:

$$\begin{array}{rcl} \tau_n^i: & \mathrm{mPsh}(\Delta) & \mapsto \mathrm{mPsh}(\Delta) \\ & (X, tX) & \mapsto (X, \overline{\tau_n^i(tX)}). \end{array}$$

This functor preserves cofibrations. Given the explicit description of colimits in marked simplicial sets, it is easy to see that $\tau_n^i$ preserves colimits. For every elementary anodyne extension $i: K \to L$, we have a pushout

$$\begin{array}{ccc} K & \longrightarrow & L \\ \downarrow & & \downarrow \\ \tau_n^i(K) & \longrightarrow & \tau_n^i(L). \end{array}$$

The intelligent $n$-truncation is then a left Quillen functor.

It's associated right adjoint is called the *$n$-truncation* and is denoted by

$$\tau_n: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta).$$

### 2.2.2 Gray tensor product

**Construction 2.2.2.1** ([Ver08c, Notation 5]). For any $n, p, q \ge 0$ such that $n = p + q$, we define:

- the *degeneration partition operator*:

$$\begin{array}{rcl} \Pi_{p,q}^1: & [n] & \to & [p] \\ & k & \mapsto & k \quad \text{if } k \le p \\ & k & \mapsto & p \quad \text{if } k > p \end{array} \qquad \qquad \begin{array}{rcl} \Pi_{p,q}^2: & [n] & \to & [q] \\ & k & \mapsto & 0 \quad \text{if } k \le p \\ & k & \mapsto & k - p \quad \text{if } k > p. \end{array}$$

76

2.2. THE COMPLICIAL MODEL

- the *face partition operator*:

$$\begin{array}{rcl} \Pi^1_{p,q} : & [p] & \to & [n] \\ & k & \mapsto & k \end{array} \qquad \begin{array}{rcl} \Pi^2_{p,q} : & [q] & \to & [n] \\ & k & \mapsto & k+p. \end{array}$$

**Definition 2.2.2.2** ([Ver08c, Definition 128]). Let $(X, tX)$ and $(Y, tY)$ be two stratified simplicial sets. We define the *Gray tensor product* of $(X, tX)$ and $(Y, tY)$ as the stratified simplicial set

$$(X, tX) \otimes (Y, tY) := (X \times Y, tX \otimes tY)$$

where $tX \otimes tY$ is the set of pairs $(x, y)$ such that for any partitions $(p, q)$ of $n$ either $\Pi^1_{p,q}x$ or $\Pi^2_{p,q}y$ is thin.

**Remark 2.2.2.3.** Let $X, Y$ be two stratified simplicial sets such that all simplices of $X$ are thin. The morphism $X \otimes Y \to X \times Y$ is then an isomorphism.

**2.2.2.4.** In [Ver08c], it is shown that the Gray tensor is associative. The problem of this operation comes from the fact that it doesn't commute with colimits. Verity then defines an other binary operation, which is cocontinuous, the *Gray pretensor* ([Ver08c, definition 135]) $(X, tX) \boxtimes (Y, tY) := (X \times Y, tX \boxtimes tY)$, together with a natural transformation:

$$\_ \boxtimes \_ \to \_ \otimes \_$$

that is pointwise an entire acyclic cofibration ([Ver08b, lemma 149]). Moreover, in [ORV20], it is shown that this pretensor is a Quillen bifunctor for the model structure on $\text{tPsh}(\Delta)$.

**Definition 2.2.2.5** (Gray tensor product for marked simplicial sets). Let $X$ and $Y$ be two marked simplicial sets. We define the *Gray tensor product* of $X$ and $Y$ as the marked simplicial set

$$X \otimes Y := (\iota(X) \otimes \iota(Y))_{\text{mk}}$$

where $((\_)_{\text{mk}}, \iota)$ is the adjunction 2.2.1.8. As $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration, we have an equality:

$$X \otimes Y := (\iota(X) \boxtimes \iota(Y))_{\text{mk}}.$$

**Proposition 2.2.2.6.** *We have equalities*

$$(\_ \boxtimes \_)_{\text{mk}} = (\_ \otimes \_)_{\text{mk}} = (\_)_{\text{mk}} \otimes (\_)_{\text{mk}}.$$

77

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Proof. The first equality is a consequence of the fact that $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration.

For the second one, we have to show that $(X \otimes Y)_{\mathrm{mk}} = (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. The unit of the adjunction $(\iota, (\_)_{\mathrm{mk}})$ induces a morphism $h : (X \otimes Y)_{\mathrm{mk}} \to (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. This morphism is an entire acyclic cofibration according to proposition 2.1.2.9, and the corollary 2.2 of [ORV20] and the fact that $(\_)_{\mathrm{mk}}$ is a left Quillen functor.

We then have lifts in the following diagram:

$$\begin{array}{ccc} (X \otimes Y)_{\mathrm{mk}} & \xrightarrow{id} & (X \otimes Y)_{\mathrm{mk}} \\ \downarrow \quad \searrow \quad \searrow \\ (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}} & & \end{array}$$

As both $k$ and $h$ are the identity on the underlying simplicial sets, this implies that the stratifications of $(X \otimes Y)_{\mathrm{mk}}$ and $(X \otimes Y)_{\mathrm{mk}}$ coincide, and this two objects are then equal. $\square$

We can then deduce the following proposition:

**Proposition 2.2.2.7.** *The Gray tensor product is associative, and is a left Quillen bifunctor in $\mathrm{mPsh}(\Delta)$.*

Proof. The first assertion is a consequence of proposition 2.2.2.6 and the fact that the binary operation $\otimes$ on $\mathrm{tPsh}(\Delta)$ is associative. The second one is a consequence of proposition 2.2.2.6 and [ORV20, Theorem 2.1]. $\square$

We now give a lemma investigating the interaction between the truncation, the intelligent truncation and the Gray tensor product.

**Lemma 2.2.2.8.** *Let $C$ and $D$ be two stratified simplicial sets.*

(1) *The following canonical square is cocartesian*

$$\begin{array}{ccc} \coprod_n \tau_n C \otimes \tau_n D & \longrightarrow & C \otimes D \\ \downarrow & & \downarrow \\ \coprod_n \tau_n^i (\tau_n C \otimes \tau_n D) & \longrightarrow & C \times D \end{array}$$

(2) *If $D$ is invariant under $\tau_2^i$, the following canonical square is cocartesian*

$$\begin{array}{ccc} \coprod_n \tau_n C \otimes D & \longrightarrow & C \otimes D \\ \downarrow & & \downarrow \\ \coprod_n \tau_{n+1}^i (\tau_n C \otimes D) & \longrightarrow & C \otimes \tau_1^i D \end{array}$$

78

2.2. THE COMPLICIAL MODEL

Proof. Let $C^{\natural}$ and $D^{\natural}$ be the underlying simplicial sets of $C$ and $D$. Remark first that the two vertical morphisms of the first square are the identity. The induced morphism

$$\coprod_{n} \tau_{n}^{i}(\tau_{n}C \otimes \tau_{n}D) \coprod_{\coprod_{n} \tau_{n}C \otimes \tau_{n}D} C \otimes D \to C \times D \tag{2.2.2.9}$$

is then the identity of $C^{\natural} \times D^{\natural}$ at the level of underlying simplicial sets. To conclude, one has to show that every simplex $C^{\natural} \times D^{\natural}$ that is marked in the right term of (2.2.2.9) is also marked in the left term. For this, let $n$ be a non negative integer, $x \in C_{k}^{\natural}$ and $y \in D_{k}^{\natural}$, such that $x$ is marked in $C$ and $y$ is marked in $D$. The $k$-simplex $(x, y)$ then is in the image of $\tau_{k-1}^{i}(\tau_{k-1}C \otimes \tau_{k-1}D)$ and is then marked in the left term of (2.2.2.9). This concludes the proof of the first assertion.

The two vertical morphisms of the second square also are the identity and the induced morphism

$$\coprod_{n} \tau_{n+1}^{i}(\tau_{n}C \otimes D) \coprod_{\coprod_{n} \tau_{n}C \otimes D} C \otimes D \to C \otimes \tau_{1}^{i}D \tag{2.2.2.10}$$

is then once again the identity of $C^{\natural} \times D^{\natural}$ at the level of underlying simplicial sets. Unfolding the definition, the marking of the left term is the smaller one that includes the one of $C \otimes D$ and every $k$-simplex $(x, y)$ such that both $x$ and $d^{k}x$ are marked in $C$.

Let $(x, y)$ be a $k$-simplex of $C^{\natural} \times D^{\natural}$. Suppose first that it is marked in $C \otimes D$. Remark that $(x, y)$ is then marked in $\tau_{k}C \otimes D$, and so is in the left term of (2.2.2.10). Suppose now that both $x$ and $d^{k}x$ are marked in $C$. This implies that $s^{k-1}d^{k}x$ is in the image of $\tau_{k-1}C$. The simplex $(s^{k-1}d^{k}x, y)$ is then in the image of $\tau_{k}^{i}(\tau_{k-1}C \otimes D)$ and is then marked in the left term of (2.2.2.10).

Now remark that we have

$$d^{k-1}(s^{k-1}x, s^{k}y) = (x, s^{k-1}d^{k-1}y) \qquad d^{k}(s^{k-1}x, s^{k}y) = (x, y)$$

$$d^{k+1}(s^{k-1}x, s^{k}y) = (s^{k-1}d^{k}x, y)$$

and both the $(k-1)$ and $(k+1)$ faces of $(s^{k-1}x, s^{k}y)$ are marked. We leave it to the reader to check that by definition every sub $l$-simplex $z$ of $(s^{k-1}x, s^{k}y)$ containing the points $k-1$, $k$ and $k+1$ is marked in $C \otimes D$, and so in $\tau_{k}C \otimes D$, and, therefore, in the left term of (2.2.2.10). As the marking is stable by complicial thinness extension, this implies that $(x, y)$ is also marked in the left term of (2.2.2.10).

The marking of the right term of (2.2.2.10) is then included in the marking of the left term. They then coincide, which concludes the proof. $\square$

Remark 2.2.2.11. The reason for including the assumption that $D$ is invariant under $\tau_{2}^{i}$ is solely because it will be the only relevant case. If we remove this assumption, the statement remains true, but the proof becomes a little bit more technical.

79

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

**2.2.2.12.** Let $X$ be a marked simplicial set. We define the *suspension* of $X$, noted by $\Sigma X$, as the following pushout:

![img-56.jpeg](img-56.jpeg)

This assignation defines a cocontinuous functor $\Sigma : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{\partial[1]}$. For every acyclic cofibration $K \to L$, we have cartesian squares

![img-57.jpeg](img-57.jpeg)

The suspension then preserves acyclic cofibration and is then a left Quillen functor.

This functor admits a right adjoint, that sends a pair $(a, b, C)$ to $C(a, b)$ where $a, b$ are two 0-simplices of $C$. If $p : C \to D$ is a morphism between complicial sets, and $a, b$ two 0-simplices of $C$, we denote by

$$p(a, b) : C(a, b) \to D(pa, pb)$$

the induced morphism.

**2.2.2.13.** We introduce an other operation, the *diamond product*, that makes the link between the Gray tensor product and the join. Let $X$ and $Y$ be two marked simplicial sets. We define $X \diamond Y$ as the colimit of the diagram:

$$X \longleftarrow X \otimes \{0\} \otimes Y \longrightarrow X \otimes [1] \otimes Y \longleftarrow X \otimes \{1\} \otimes Y \longrightarrow Y$$

The functors

$$\_ \diamond X : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X} \quad \text{and} \quad X \diamond \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X}$$

are colimit preserving. Furthermore, for every acyclic cofibration $K \to L$, the morphism $K \diamond X \to L \diamond X$ is the horizontal colimit of the diagram:

![img-58.jpeg](img-58.jpeg)

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that $\_ \diamond X$ is a left Quillen functor. We show analogously that $X \diamond \_$ is a left Quillen functor.

80

2.2. THE COMPLICIAL MODEL

**Lemma 2.2.2.14.** *There exists a unique natural transformation $\gamma_{X,Y} : X \diamond Y \rightarrow X \star Y$ that fits in the following diagram:*

![img-59.jpeg](img-59.jpeg)

*Proof.* We begin by defining this morphism on simplicial sets, and for this we can suppose that both $X$ and $Y$ are representables, ie $X := [n]$, $Y := [m]$. On object, this morphism is induced by the assignation:

$$p(k, 0, l) := k \quad p(k, 1, l) := l.$$

We need to verify that this morphism preserves thin cells. Suppose now that $(x, v, y)$ is a thin $n$-simplex of $X \diamond Y$. There are several cases to consider. **Case** $v_n = 0$. The simplex $x$ is then thin, and is sent to $x \star \emptyset$ which is also thin. **Case** $v_0 = 1$. Similar. **Case** $v_0 = 0$ **and** $v_n = 1$. Let $p$ be the smaller integer such that $v_p = 1$. Either $\Pi_{p-1, n-p+1}^1(x)$ or $\Pi_{p, n-p}^2(y)$ is thin. This implies that $\phi_{X,Y}(x, v, y) = \Pi_{p-1, n-p+1}^1(x) \star \Pi_{p, n-p}^2(y)$ is thin. $\square$

**Proposition 2.2.2.15.** *For any $X, Y$, the morphism $\gamma_{X,Y}$ is a weak equivalence.*

*Proof.* The set of couples $(X, Y)$ such that $\gamma_{X,Y}$ is a weak equivalence is saturated by monomorphisms. It is then enough to show the result for any couples of representables.

Let's start by the case $(X, Y) = ([n], [m])$. Let $s : X \star Y \rightarrow X \diamond Y$ be the morphism defined on objects by the formula:

$$s(k \star \emptyset) := (k, 0, 0) \quad s(\emptyset \star l) := (n, 1, l)$$

We have

$$\gamma_{X,Y} s = id \quad s\gamma_{X,Y}(k, \epsilon, l) = (k + \epsilon(n - k), \epsilon, \epsilon l).$$

Let $\eta : [n] \diamond [m] \rightarrow [n] \diamond [m]$ be induced by the application

$$(k, \epsilon, l) \mapsto (k, \epsilon, \epsilon l).$$

We are now going to construct two morphisms

$$\epsilon_0 : ([n] \diamond [m]) \times [1]_t \rightarrow [n] \diamond [m] \quad \text{and} \quad \epsilon_1 : ([n] \diamond [m]) \times [1]_t \rightarrow [n] \diamond [m]$$

such that

$$\begin{aligned} \epsilon_0(\_, 0) &= \eta & \epsilon_0(\_, 1) &= s\gamma_{X,Y} \\ \epsilon_1(\_, 0) &= \eta & \epsilon_1(\_, 1) &= id \end{aligned}$$

81

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

The first one is induced on the level of simplicial sets by

$$(k, \epsilon, l, \alpha) \mapsto (k + \alpha \epsilon (n - k), \epsilon, \epsilon l),$$

and the second one by

$$(k, \epsilon, l, \alpha) \mapsto (k, \epsilon, (\epsilon \vee \alpha) l),$$

where $\epsilon \vee \alpha := \epsilon + \alpha - \epsilon \alpha$. These two morphisms extend to marked simplicial sets.

We proceed in a similar way with cases $(X, Y) = ([n]_t, [m]), ([n], [m]_t)$ or $([n]_t, [m]_t)$.

As we already now that functors $\_ \diamond X$ and $X \diamond \_$ preserve weak equivalences, the previous proposition implies that for any marked simplicial sets $X$, functors $\_ \star X$ and $X \star \_$ preserves weak equivalences and are then left Quillen functors.

**2.2.2.16.** Let $X$ be a marked simplicial set. We now describe an variation on the suspension. We define $\Sigma^{\star} X$, as the following pushout:

![img-60.jpeg](img-60.jpeg)

This assignation defines a cocontinuous functor $\Sigma^{\star} : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{\partial[1]}$. Using proposition 2.2.2.15, all the vertical morphisms of the following diagram are weak equivalences:

![img-61.jpeg](img-61.jpeg)

Remark furthermore that the colimits of these lines are also homotopy colimits. Taking the horizontal colimit, this induces a weak equivalence

$$\Sigma X \to \Sigma^{\star} X \tag{2.2.2.17}$$

natural in $X$.

**2.2.2.18.** We define the *co-join* of $X$ and $Y$, denoted by $X \stackrel{co}{\star} Y$, as the colimit of the following diagram:

$$Y \longleftarrow Y \otimes \{1\} \otimes X \longrightarrow Y \otimes [1] \otimes X \longleftarrow Y \otimes \{0\} \otimes X \longrightarrow X$$

The functors

$$\_ \stackrel{co}{\star} X : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X} \quad \text{and} \quad X \stackrel{co}{\star} \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X}$$

82

2.2. THE COMPLICIAL MODEL

are colimit preserving. Furthermore, for every acyclic cofibration $K \to L$, the morphism $K \stackrel{co}{\star} X \to L \stackrel{co}{\star} X$ is the horizontal colimit of the diagram:

$$\begin{array}{c} K \amalg X \longleftarrow X \otimes \partial[1] \otimes K \longrightarrow X \otimes [1] \otimes K \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ L \amalg X \longleftarrow X \otimes \partial[1] \otimes L \longrightarrow X \otimes [1] \otimes K \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that $\_ \stackrel{co}{\star} X$ is a left Quillen functor. We show analogously that $X \stackrel{co}{\star} \_ \_ \_$ is a left Quillen functor.

**2.2.2.19.** Let $X$ be a simplicial set. We define the *wedge* of $\Sigma X$ and $[1]$, noted by $\Sigma X \vee [1]$, as the colimit of the following diagram:

$$\begin{array}{c} X \otimes [0, 1] \longrightarrow X \otimes [2]_t \longleftarrow X \otimes [1, 2] \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ \Sigma X \longrightarrow X \vee [1] \longleftarrow [1, 2] \end{array}$$

This assignation defines a cocontinuous functor $\_ \vee [1] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0]\amalg[1]/}$. For every acyclic cofibration $K \to L$, the morphism $K \vee [1] \to L \vee [1]$ is the horizontal colimit of the diagram:

$$\begin{array}{c} [0] \coprod[1] \longleftarrow K \otimes ([0] \coprod[1, 2]) \longrightarrow K \otimes [2]_t \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ K \otimes [2]_t \longleftarrow L \otimes [2]_t \longrightarrow L \otimes [2]_t \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that this functor is a left Quillen functor. We denote by

$$\nabla : \Sigma X \to \Sigma X \vee [1]$$

the morphism induced by the inclusion $X \otimes [0, 2] \subset X \otimes [2]_t$ and

$$\Sigma X \hookrightarrow \Sigma X \vee [1]$$

the morphism induced by the inclusion $X \otimes [1, 2] \subset X \otimes [2]_t$. We define similarly the left Quillen functor

$$[1] \vee \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[1]\amalg[0]/}$$

and the morphisms

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \Sigma X \hookrightarrow [1] \vee \Sigma X.$$

83

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

**Proposition 2.2.2.20.** *Morphisms*

$$\Sigma X \coprod_{[0]} [1] \rightarrow \Sigma X \vee [1] \quad \text{and} \quad [1] \coprod_{[0]} \Sigma X \rightarrow [1] \vee \Sigma X$$

*are acyclic cofibrations.*

*Proof.* We have cartesian squares:

$$\begin{array}{ccc} X \otimes ([0] \coprod [1, 2]) & \longrightarrow & X \otimes \Lambda^1[2] \longrightarrow X \otimes [2]_t \\ \downarrow & & \downarrow \\ [0] \coprod [1] & \longrightarrow & \Sigma X \coprod_{[0]} [1] \longrightarrow \Sigma X \vee [1]. \end{array}$$

The upper right horizontal morphism is an acyclic cofibration, and so is the downer right horizontal one. We proceed similarly for the other morphism. □

### 2.2.3 Gray cylinder, Gray cone and Gray o-cone

#### 2.2.3.1. The Gray tensor product induced a left Quillen functor

$$\_ \otimes [1] : \text{mPsh}(\Delta) \rightarrow \text{mPsh}(\Delta)$$

called the *Gray cylinder*. The join and the co-join also induce two left Quillen functors

$$\_ \star [0] : \text{mPsh}(\Delta) \rightarrow \text{mPsh}(\Delta)_{[0]}/ \quad [0] \stackrel{co}{\star} \_ : \text{mPsh}(\Delta) \rightarrow \text{mPsh}(\Delta)_{[0]}/$$

called the *Gray cone* and the *Gray o-cone*. We denote by

$$\begin{array}{ccc} \text{mPsh}(\Delta). & \rightarrow & \text{mPsh}(\Delta) \\ (X, x) & \mapsto & X_{/x} \end{array} \qquad \begin{array}{ccc} \text{mPsh}(\Delta). & \rightarrow & \text{mPsh}(\Delta) \\ (X, x) & \mapsto & X_{x/} \end{array}$$

respectively called the *slice of X over x* and the *slice of X under x*, the right adjoints of the Gray cone and the Gray o-cone.

Remark furthermore that we have canonical natural transformation $X_{x/} \rightarrow X$ and $X_{/x} \rightarrow X$, induced by the natural transformation $X \rightarrow X \star [0]$ and $X \rightarrow [0] \stackrel{co}{\star} X$.

**2.2.3.2.** The category of endomorphisms of marked simplicial sets has a monoidal structure given by the composition. The endomorphism $[0] \stackrel{co}{\star} \_ $ admits a monoid structure, where the multiplication is the natural transformation: $[0] \stackrel{co}{\star} ([0] \stackrel{co}{\star} X) \rightarrow [0] \stackrel{co}{\star} X$, induced by the pairing:

$$\begin{array}{ccc} X \otimes [1] \otimes [1] & \rightarrow & X \otimes [1] \\ (x, i, j) & \mapsto & (x, i \wedge j). \end{array}$$

84

2.2. THE COMPLICIAL MODEL

This defines a cosimplicial object in $\operatorname{End}(\mathrm{mPsh}(\Delta))$, which evaluated on $\emptyset$, provides a cosimplicial object in $\mathrm{mPsh}(\Delta)$:

$$
\begin{array}{l}
\Delta \rightarrow \mathrm{mPsh}(\Delta) \\
n \mapsto [n]_{\circ} := [0] \stackrel{co}{\star} (...([0] \stackrel{co}{\star} [0])).
\end{array}
$$

Eventually, we set $([n]_t)_{\circ} := \tau_{n-1}^i ([n]_{\circ})$. We then have defined a functor:

$$
(\_)_{\circ} : t\Delta \rightarrow \mathrm{mPsh}(\Delta).
$$

## 2.2.4 Street nerve

We recall that $(0, \omega)$-categories are defined in section 1.1.1. The Gray operations on $(0, \omega)$-categories - $_\otimes [1]$, $_\star 1$, $1 \stackrel{co}{\star} \_-$ are defined in section 1.2.3.

In [Str87], Street defines a cosimplicial object in $(0, \omega)$-cat, that associates to $n$, the $n^{th}$ *oriental* $O_n$. The original construction of this object is complicated, but Ara and Maltsiniotis have shown that it can be easily defined using Gray operations. Indeed, in [AM20, Corollaire 7.10], these authors construct an isomorphism

$$
O_n \cong \overbrace{1 \star \ldots \star 1}^{n+1}
$$

natural in $n$.

We can extend the functor $O_ : \Delta \rightarrow (0, \omega)$-cat to $t\Delta$ by defining

$$
(O_n)_t := \tau_{n-1}^i (O_n).
$$

By extention by colimit, this induces a functor

$$
\mathrm{R} : \mathrm{tPsh}(\Delta) \rightarrow (0, \omega)\text{-cat}.
$$

As explained in example 11 of [Ver06], R preserves the Gray tensor product, and so also the suspension, the wedge, the Gray cone and the Gray o-cone. Moreover, [Ver08a, Theorem 249] states that this functor sends complicial horn inclusions and complicial thinness extensions to isomorphisms. It obviously also sends saturation extensions to isomorphisms. This functor then sends every weak equivalences to isomorphisms, and then lifts to a colimit preserving functor $\mathrm{R} : \mathrm{mPsh}(\Delta) \rightarrow (0, \omega)$-cat and induces an adjoint pair:

$$
\mathrm{R} : \mathrm{mPsh}(\Delta) \xleftrightarrow{\perp} (0, \omega)\text{-cat} : \mathrm{N}
$$

We now recall two fundamental results of strictification:

85

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Theorem 2.2.4.1 (Gagna, Ozornova, Rovelli). Let n be an integer. The canonical morphism

\[
[ n ] \to \mathrm{N} (\mathrm{R} ([ n ]))
\]

is an acyclic cofibration.

Proof. This is [GOR21, corollary 5.4].

Theorem 2.2.4.2 (Ozornova, Rovelli). Let \(C\) be an \((0,\omega)\)-category. The canonical morphism

\[
\Sigma \mathrm{N} C \rightarrow \mathrm{N} ([ C, 1 ])
\]

is an acyclic cofibration.

Proof. The morphism (2.2.2.17) provides a weak equivalence \(\Sigma \mathrm{N}C\to \Sigma^{\star}\mathrm{N}C\). As this morphism is sent to an isomorphism by \(R\), it induces a commutative triangle

![img-62.jpeg](img-62.jpeg)

The theorem 3.22 of [OR22] stipulates that \(\Sigma^{\star}\mathrm{N}C\to \mathrm{N}([C,1])\) is a weak equivalence, which concludes the proof.

Definition 2.2.4.3. We define the Street endofunctor  \( i_{str} \)  to be the colimit preserving functor defined on representables by:

\[
i _ {s t r} ([ n ]) := \mathrm{N} (\mathrm{R} ([ n ])) \quad \mathrm{and} \quad i _ {s t r} ([ n ] _ {t}) := \tau_ {n - 1} ^ {i} (i _ {s t r} ([ n ]))
\]

Proposition 2.2.4.4. The functor \( i_{srt} \) is left Quillen and the natural transformation

\[
i d \rightarrow i _ {s r t}
\]

is weakly invertible.

Proof. As noticed earlier, for any integer n, the map  \( [n] \to i_{srt}([n]) \)  is a weak equivalence. We recall that the intelligent truncation functor  \( \tau_{n-1}^{i}: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta) \)  is a left Quillen functor, and so preserves weak equivalences between cofibrant objects. The morphism  \( [n]_{t} \to i_{str}([n]_{t}) \)  is then a weak equivalence. The set of objects X such that the morphism  \( X \to i_{srt}X \)  is a weak equivalence is closed by homotopy colimits and includes all representables. As  \( i_{srt} \)  preserves monomorphisms, it then consists of all marked simplicial sets. Now let  \( K \to L \)  be an acyclic cofibration. We have a commutative square:

![img-63.jpeg](img-63.jpeg)

86

2.3. SUSPENSION AND GRAY OPERATIONS

By two out of three, $i_{str}(K) \to i_{str}(L)$ is then an acyclic cofibration. The functor $i_{srt}$ is then left Quillen. $\square$

## 2.3 Suspension and Gray operations

### 2.3.1 Formula for the Gray cylinder

The aim of this subsection is to demonstrate the following theorem:

**Theorem 2.3.1.1.** *There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram*

$$[1] \vee \Sigma X \stackrel{\vee}{\leftarrow} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \stackrel{\vee}{\rightarrow} \Sigma X \vee [1]$$

and $(\Sigma X) \otimes [1]$.

**Construction 2.3.1.2.** Let $C$ be the following colimit:

$$\begin{array}{c} [3] \times \{0\} \coprod [3] \times \{1\} \longrightarrow [3] \times [1] \\ s^0 s^0 \coprod s^2 s^3 \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \coprod [1] \longrightarrow C. \end{array}$$

We define several marked simplicial sets whose underlying simplicial sets are sub objects of C:

$$\begin{array}{c c c} A_0 := & \begin{array}{c} 00 \longrightarrow 01 \\ \parallel \searrow \searrow \searrow \downarrow \\ 10 \longrightarrow 11 \end{array} & A_3 := & \begin{array}{c} 00 \longrightarrow 01 \\ \parallel \searrow \searrow \searrow \downarrow \\ 20 \longrightarrow 21 \end{array} \\ A_1 := & \begin{array}{c} \parallel \searrow \searrow \searrow \parallel \\ 20 \longrightarrow 21 \end{array} & \\ A_2 := & \begin{array}{c} 20 \longrightarrow 21 \\ \downarrow \searrow \searrow \parallel \\ 30 \longrightarrow 31 \end{array} & A_4 := & \begin{array}{c} 00 \longrightarrow 01 \\ \downarrow \searrow \searrow \searrow \downarrow \\ 30 \longrightarrow 31 \end{array} \end{array} \end{array}$$

where arrows labeled by $=$ are degenerate and simplices labeled by $\sim$ are thin.

Let $B_0$ be the sub object corresponding to the image of $[0, 1, 2] \times [0, 1]$ where the marking includes all cells of dimension $\le 2$, except $[10, 20, 21]$ and $[00, 20, 21]$.

Let $B_1$ be the sub object corresponding to the image of $[0, 2, 3] \times [0, 1]$ where the marking includes all cells of dimension $\le 2$, except $[00, 20, 21]$, $[00, 30, 31]$ and $[00, 20, 31]$.

Let $B$ be the reunion of $[0, 1, 2] \times [0, 1]$ and $[0, 2, 3] \times [0, 1]$ where the marking is the reunion of $B_0$ and $B_1$.

**Lemma 2.3.1.3.** *Morphisms $A_0 \cup A_1 \to B_0$ and $A_3 \to B_0$ are acyclic cofibrations.*

87

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Proof. The cofibration $A_0 \cup A_1 \to B_0$ fits in the following pushout square:

$$\begin{array}{c} \Lambda^1[2] \otimes [1] \cup [2]_t \otimes \partial[1] \longrightarrow A_1 \cup A_2 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [2]_t \otimes [1] \xrightarrow{[0,1,2] \times [0,1]} B_0 \end{array}$$

The cofibration $A_3 \to B_0$ is a sequence of inclusions:

$$A_3 =: (D_0, M_0) \subset (D_1, M_1) \subset (D_2, M_2) \subset (D_3, M_3) \subset (D_4, M_4) \subset (D_5, M_5) \subset (D_6, M_6) := B_0,$$

where

- $D_1 = D_0 \cup [00, 01, 11]$ ;
- $D_2 = D_1 \cup [00, 10, 11]$ ;
- $D_2 = D_1 \cup [00, 10, 21]$ ;
- $D_4 = D_3 \cup [00, 01, 11, 21]$;
- $D_5 = D_4 \cup [00, 10, 11, 21]$;
- $D_6 = D_5 \cup [00, 10, 20, 21]$;

and

- $(D_0, M_0) \to (D_1, M_1)$ is a pushout of $\Lambda^1[2] \to [2]^1$;
- $(D_1, M_1) \to (D_2, M_2)$ is a pushout of $\Lambda^0[2] \to [2]^0$;
- $(D_2, M_2) \to (D_3, M_3)$ is a pushout of $\Lambda^0[2] \to [2]^0$;
- $(D_3, M_3) \to (D_4, M_4)$ is a pushout of $\Lambda^1[3] \to [3]^1$;
- $(D_4, M_4) \to (D_5, M_5)$ is a pushout of $\Lambda^0[3] \to [3]^0$;
- $(D_5, M_5) \to (D_6, M_6)$ is a pushout of $\Lambda^0[3] \to [3]^0$.

Lemma 2.3.1.4. Morphisms $A_2 \cup A_3 \to B_1$ and $A_4 \to B_1$ are acyclic cofibrations.

Proof. The cofibration $A_2 \cup A_3 \to B_1$ fits in the pushout square:

$$\begin{array}{c} \Lambda^1[2] \otimes [1] \cup [2]_t \otimes \partial[1] \longrightarrow A_2 \cup A_3 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [2]_t \otimes [1] \xrightarrow{[0,2,3] \times [0,1]} B_1 \end{array}$$

The cofibration $A_4 \to B_1$ is a sequence of inclusions:

$$A_4 =: (D_0, M_0) \subset (D_1, M_1) \subset (D_2, M_2) \subset (D_3, M_3) \subset (D_4, M_4) \subset (D_5, M_5) \subset (D_6, M_6) := B_1$$

where

- $D_1 = D_0 \cup [00, 21, 31]$ ;

88

2.3. SUSPENSION AND GRAY OPERATIONS

- $D_2 = D_1 \cup [20, 30, 31]$ ;
- $D_3 = D_2 \cup [20, 21, 31]$;
- $D_4 = D_3 \cup [00, 01, 21, 31]$;
- $D_5 = D_4 \cup [00, 20, 30, 31]$ ;
- $D_6 = D_5 \cup [00, 20, 21, 31]$ ;

and

- $(D_0, M_0) \to (D_1, M_1)$ is a pushout of $\Lambda^2[2] \to [2]^2$;
- $(D_1, M_1) \to (D_2, M_2)$ is a pushout of $\Lambda^1[2] \to [2]^1$;
- $(D_2, M_2) \to (D_3, M_3)$ is a pushout of $\Lambda^2[2] \to [2]^2$;
- $(D_3, M_3) \to (D_4, M_4)$ is a pushout of $\Lambda^3[3] \to [3]^3$;
- $(D_4, M_4) \to (D_5, M_5)$ is a pushout of $\Lambda^2[3] \to [3]^2$;
- $(D_5, M_5) \to (D_6, M_6)$ is a pushout of $\Lambda^3[3] \to [3]^3$.

□

**Lemma 2.3.1.5.** *The maps $A_0 \cup A_1 \cup A_2 \to B$ and $A_4 \to B$ are acyclic cofibrations.*

*Proof.* This is a direct consequence of the last two lemmas.

□

**Construction 2.3.1.6.** The marked simplicial set $\overline{X \otimes B}$ is the pushout:

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes B}. \end{array}$$

Let $\overline{X \otimes A_i}$ and $\overline{X \otimes B_i}$ be the sub-objects of $\overline{X \otimes B}$ corresponding to image of $X \otimes A_i$ and $X \otimes B_i$.

**Lemma 2.3.1.7.** *The inclusion $\overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \to \overline{X \otimes B}$ and $\overline{X \otimes A_4} \to \overline{X \otimes B}$ are acyclic cofibrations.*

*Proof.* Remark that we have cocartesian squares

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes A_0 \cup X \otimes A_1 \cup X \otimes A_2 \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \longrightarrow \overline{X \otimes B} \end{array}$$

and

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes A_4 \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes A_4} \longrightarrow \overline{X \otimes B} \end{array}$$

The result then follows from lemma 2.3.1.5.

□

89

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Lemma 2.3.1.8. The morphisms \(\overline{X\otimes A_0}\to [1]\vee \Sigma X\) and \(\overline{X\otimes A_2}\to \Sigma X\vee [1]\), induced by the morphism \(A_0\to [00,01,11]_t\) and \(A_{2}\rightarrow [20,30,31]_{t}\), are acyclic cofibrations.

Proof. We have cocartesian squares

![img-64.jpeg](img-64.jpeg)

That shows that \([1] \coprod_{[0]} \Sigma X \to \overline{X \otimes A_0}\) is an acyclic cofibration. We then have a commutative diagram:

![img-65.jpeg](img-65.jpeg)

and by two out of three, this shows that  \( \overline{X\otimes A_{0}}\to[1]\vee\Sigma X \)  is an acyclic cofibration. We proceed similarly for the second morphism. ☐

Lemma 2.3.1.9. Marked simplicial sets \(\overline{X\otimes A_1}\) and \(\overline{X\otimes A_4}\) are respectively equal to \(\Sigma (X\otimes [1])\) and \((\Sigma X)\otimes [1]\).

Proof. This is true by the definition of these objects.

Proof of theorem 2.3.1.1. According to lemma 2.3.1.9 we have a cocartesian square

![img-66.jpeg](img-66.jpeg)

The left vertical morphism is a weak equivalence according to lemma 2.3.1.8, and the horizontal morphisms are cofibrations. By left properness, the right vertical morphism is a weak equivalence. Combined with lemmas 2.3.1.7 and 2.3.1.9, this provides a zigzag of weak equivalences between \([1] \vee \Sigma X \coprod_{\Sigma(X \otimes \{0\})} \Sigma(X \otimes [1]) \coprod_{\Sigma(X \otimes \{1\})} \Sigma X \vee [1]\) and \((\Sigma X) \otimes [1]\).

#### 2.3.2 Formulas for the Gray cone and the Gray o-cone

Theorem 2.3.2.1. There is a zigzag of acyclic cofibrations, natural in \( X \), between the colimit of the diagram

\[
\Sigma X \vee [ 1 ] \leftarrow \Sigma X \rightarrow \Sigma ([ 0 ] ^ {\infty} \star X)
\]

90

2.3. SUSPENSION AND GRAY OPERATIONS

and $\Sigma X \star [0]$.

There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram

$$\Sigma(X \star [0]) \leftarrow \Sigma X \rightarrow [1] \vee \Sigma X$$

and $[0] \stackrel{co}{\star} \Sigma X$.

Proof. We consider the diagram:

$$\begin{array}{ccc} [1] & \longleftarrow & [1] \coprod_{[0]} \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \\ \downarrow{id} & & \sim \downarrow & \downarrow{id} \\ [1] & \longleftarrow & [1] \vee \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \end{array}$$

All vertical morphisms are weak equivalences. We denote by $A$ the colimit of the first line. The theorem 2.3.1.1 implies that there is a zigzag of acyclic cofibrations between $A$ and $X \diamond [0]$. Colimits of the two lines are homotopy colimits, and the comparison morphism is then an acyclic cofibration. We then have a zigzag of acyclic cofibrations:

$$X \star [0] \leftarrow X \diamond [0] \rightsquigarrow A \rightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma([0] \stackrel{co}{\star} X)$$

The second assertion is demonstrated similarly. $\square$

**Corollary 2.3.2.2.** Let $f : C \rightarrow D$ be a fibration between complicial sets, and $K \rightarrow L$ a cofibration. If $f$ has the right lifting property against

$$\Sigma([0] \stackrel{co}{\star} K \cup \emptyset \star L) \rightarrow \Sigma([0] \stackrel{co}{\star} L),$$

then $f$ has the right lifting property against

$$(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \rightarrow \Sigma K \star [0].$$

If $f$ has the right lifting property against $\Sigma[1] \rightarrow \Sigma[1]_t$, then $f$ has the right lifting property against

$$[1]_t \star \emptyset \cup [1] \star [0] \rightarrow [1]_t \star [0]$$

Proof. Suppose that $f$ fulfills the condition. The class of cofibration having the right lifting property against $f$ is closed by pushouts and, according to 2.1.1.15, by zigzag of acyclic cofibration. The morphism

$$\alpha : \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K \coprod_{\emptyset \star K} \emptyset \star L) \rightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} L)$$

91

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

is then in this class. Remark that we have a cocartesian square

$$\begin{array}{c} \Sigma L \cup [ 1 ] \coprod_ {\Sigma K \cup [ 1 ]} \Sigma K \vee [ 1 ] \longrightarrow \Sigma L \cup [ 1 ] \coprod_ {\Sigma K \cup [ 1 ]} \Sigma K \vee [ 1 ] \coprod_ {\Sigma L} \Sigma ([ 0 ] ^ {c o} \star K) \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Biggl \downarrow \\ \Sigma L \vee [ 1 ] \longrightarrow \Sigma L \vee [ 1 ] \coprod_ {\Sigma L} \Sigma ([ 0 ] ^ {c o} \star K \coprod_ {\emptyset \star K} \emptyset \star L) \end{array}$$

where the left vertical morphism, and so also the right vertical morphism, is an acyclic cofibration. This induces a zigzag of acyclic cofibration between $\alpha$ and $\beta$ where $\beta$ is

$$\Sigma L \cup [ 1 ] \coprod_ {\Sigma K \cup [ 1 ]} \Sigma K \vee [ 1 ] \coprod_ {\Sigma L} \Sigma ([ 0 ] ^ {c o} \star K) \to \Sigma L \vee [ 1 ] \coprod_ {\Sigma L} \Sigma ([ 0 ] ^ {c o} \star L)$$

Eventually, the theorem 2.3.2.1 induces a zigzag of acyclic cofibration between $\beta$ and $(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \to \Sigma K \star [0]$ which concludes the proof of the first assertion.

For the second assertion, remark that $[1]_t \star [0]$ is $\tau_1^i ([1]_t \star \emptyset \cup [1] \star [0])$. As $\tau_1^i$ is a left Quillen functor, the theorem 2.3.2.1 induces a zigzag of acyclic cofibration between $[1]_t \star \emptyset \cup [1] \star [0] \to [1]_t \star [0]$ and

$$[ 1 ] _ {t} \vee [ 1 ] \coprod_ {[ 1 ]} \Sigma [ 1 ] \to [ 1 ] _ {t} \vee [ 1 ] \coprod_ {[ 1 ]} \Sigma [ 1 ] _ {t}.$$

As this cofibration is a pushout of $\Sigma[1] \to \Sigma[1]_t$, this concludes the proof.

**Corollary 2.3.2.3.** *Let $f : C \to D$ be a fibration between complicial sets, and $K \to L$ a cofibration. If $f$ has the right lifting property against*

$$\Sigma (L \star \emptyset \cup K \star [ 0 ]) \to \Sigma (L \star [ 0 ]),$$

*then $f$ has the right lifting property against*

$$[ 0 ] ^ {c o} \star \Sigma K \cup \emptyset \star \Sigma L \to [ 0 ] ^ {c o} \star \Sigma L.$$

*If $f$ has the right lifting property against $\Sigma[1] \to \Sigma[1]_t$, then $f$ has the right lifting property against*

$$[ 0 ] ^ {c o} \star [ 1 ] \cup \emptyset \star [ 1 ] _ {t} \to [ 0 ] ^ {c o} \star [ 1 ] _ {t}$$

*Proof.* The proof is similar to the one of corollary 2.3.2.2.

92

2.4. GLOBULAR EQUIVALENCES

## 2.4 Globular equivalences

### 2.4.1 Homotopy categories

2.4.1.1. The $n$-globe is the marked simplicial set $\mathbf{D}_n := \Sigma^n[0]$. We then have $\mathbf{D}_0 := [0]$ and $\mathbf{D}_{n+1} := \Sigma\mathbf{D}_n$. This defines a globular object in $\mathrm{mPsh}(\Delta)$:

$$\mathbf{D}_0 \xrightarrow[i_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[i_3^-]{i_3^+} \dots$$

and we have equalities:

$$i_{n+1}^- i_n^+ = i_{n+1}^+ i_n^- \quad i_{n+1}^+ i_n^- = i_{n+1}^+ i_n^+.$$

We also set $(\mathbf{D}_n)_t := \tau_{n-1}^i(\mathbf{D}_n)$ for $n > 0$ and $\partial\mathbf{D}_n := \Sigma^n\emptyset$. We then have a canonical inclusions

$$\partial\mathbf{D}_0 \to \mathbf{D}_0$$

and for any $n > 0$, we have canonical inclusions

$$\partial\mathbf{D}_n \to \mathbf{D}_n \to (\mathbf{D}_n)_t.$$

Let $C$ be a complicial set. A $n$-cell $a$ of $C$ is a morphism $a : \mathbf{D}_n \to C$. If $n$ is non null, the *source* of $a$ (resp. the *target* of $a$) is the $(n-1)$-cell $a \circ i_{n-1}^-$ (resp. $a \circ i_{n-1}^+$). The cell $a$ is thin if the corresponding morphism $\mathbf{D}_n \to C$ factorizes via $(\mathbf{D}_n)_t$.

2.4.1.2. From now on, and until the end of this section, we fix a complicial set $C$. All considered cells are cells of $C$.

Let $n$ be a non null integer, and $a, b$ two $n$-cells. Cells $a$ and $b$ are *parallel* if they share the same source and the same target. They are *composable* if the source of $a$ is the target of $b$.

Let $a$ and $b$ be two parallel cells. The cell $a$ is *equivalent* to the cell $b$ if there exists a thin $(n+1)$-cell $d : a \to b$, or equivalently, if there exists a homotopy $\mathbf{D}_n \times [1]_t$ between $a$ and $b$, and constant on $\partial\mathbf{D}_n \times [1]_t$. This relation is denoted by $\sim$.

**Lemma 2.4.1.3.** *The relation $\sim$ is reflexive, symmetric and transitive.*

*Proof.* This comes from usual properties of fibrant objects.

**Lemma 2.4.1.4.** *Let $a, b$ be two equivalent cells. If $a$ is thin, so is $b$.*

*Proof.* As $\{0\} \to [1]_t$ is a weak equivalence, so is $\mathbf{D}_n \times [1]_t \cup (\mathbf{D}_n)_t \times \{0\} \to (\mathbf{D}_n)_t \times [1]_t$. As $C$ is fibrant, this directly implies the result.

93

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Construction 2.4.1.5. Let \( a, b \) be two composable \( n \)-cells. A composition of \( a \) and \( b \) is a \( n \)-cell \( a \circ b \) that fits in a diagram:

![img-67.jpeg](img-67.jpeg)

As \(C\) is a fibrant object, if \((a\circ b)'\) is any other composition, \((a\circ b)'\sim a\circ b\).

Lemma 2.4.1.6. Let \( a, b, c \) be three composable cells. There exists compositions such that \( (a \circ b) \circ c = a \circ (b \circ c) \).

Proof. Let \( M \) be the marking on [3] that includes all simplices of dimension superior or equal to 2. We define \( \mathrm{Sp}_{[3]} \) as the simplicial set \( [1] \coprod_{[0]} [1] \coprod_{[0]} [1] \). Remark that the cofibration \( \mathrm{Sp}_{[3]} \to ([3], M) \) is acyclic. We then have a lift \( f \) in the following diagram

![img-68.jpeg](img-68.jpeg)

The morphism \( f \) provides all the desired compositions.

Definition 2.4.1.7. We define the category \(\pi_0(C)\) whose objects are 0-cells \(x: s \to t\), and edges between \(x, y: s \to t\) are equivalence classes of the set of 1-cells \(f: x \to y\) quotiented by the relation \(\sim\). The composition is given by construction 2.4.1.5 which is associative according to lemma 2.4.1.6.

Let n > 0 be an integer, and s, t two parallel  \( (n - 1) \) -cells. We define the category  \( \pi_{n}(s, t, C) \)  whose objects are n-cells  \( x : s \to t \) , and edges between  \( x, y : s \to t \)  are equivalence classes of the set of  \( (n + 1) \) -cells  \( f : x \to y \)  quotiented by the relation  \( \sim \) . The composition is given by construction 2.4.1.5 which is associative according to lemma 2.4.1.6.

Proposition 2.4.1.8. Let \( x, y: s \to t \) be two parallel \( n \)-cells, and \( f: x \to y \) a \( n + 1 \)-cell. The cell \( f \) is thin if and only if \( [f]: x \to y \) is an isomorphism in \( \pi_n(s, t, C) \).

Proof. Suppose first that \( f \) is thin. There are liftings in the following diagrams:

![img-69.jpeg](img-69.jpeg)

![img-70.jpeg](img-70.jpeg)

94

2.4. GLOBULAR EQUIVALENCES

Let $g : y \to z$ be the restriction of $h$ to $\Sigma^n[1, 2]$ and $l : y \to z$ be the restriction of $k$ to $\Sigma^n[0, 1]$. We then have $[f][g] = id$, and $[h][f] = id$, and $[f]$ is then an isomorphism.

For the other direction, suppose that $[f]$ is an isomorphism. Let $M$ be the marking on $[3]$ that includes all simplices of dimension superior or equal to 2. As $\mathrm{Sp}_{[3]} \to ([3], M)$ is a weak equivalence, there is a lifting in the following diagram:

$$\begin{array}{c} \Sigma^n([0, 1] \coprod_{\{1\}} [1, 2] \coprod_{\{2\}} [2, 3]) \xrightarrow{f^{-1} \amalg f^{-1} \amalg f^{-1}} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Sigma^n([3], M) \end{array}$$

Now $h(\Sigma^n[0, 3])$ and $h(\Sigma^n[0, 2])$ are respectively compositions of $(f, f^{-1})$ and $(f^{-1}, f)$. Hypotheses imply that these compositions are equivalent to identities, and so are thin. The morphism then lifts to $\Sigma^n[3]^{eq}$. The object $C$ being fibrant, $h$ lifts to $\Sigma^n[3]^{\sharp}$, and $f$ is then thin.

**Lemma 2.4.1.9.** *Let $s, t$ and $s', t'$ be two pairs of parallel cells, and $\psi : \partial\mathbf{D}_n \times [1]_t \to C$ a homotopy between $s \cup t : \partial\mathbf{D}_n \to C$ and $s' \cup t' : \partial\mathbf{D}_n \to C$. Then*

$$\pi_n(s, t, C) \cong \pi_n(s', t', C)$$

*Proof.* For each $x : s \to t$, there exists a lifting $h_x$ in the following diagram:

$$\begin{array}{c} \mathbf{D}_n \times \{0\} \cup \partial\mathbf{D}_n \times [1]_t \xrightarrow{x \cup \psi} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf{D}_n \times [1]_t \end{array}$$

and we define $F(x)$ as the restriction of $h_x$ to $\mathbf{D}_n \times \{1\}$. For a $(n + 1)$-cell $f : x \to y$, there exists a lifting $h_f$ in the following diagram:

$$\begin{array}{c} \mathbf{D}_{n+1} \times \{0\} \cup \partial\mathbf{D}_{n+1} \times [1]_t \xrightarrow{f \cup h_x \cup h_y} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf{D}_{n+1} \times [1]_t \end{array}$$

and we define $F(f)$ as the restriction of $h_f$ to $\mathbf{D}_{n+1} \times \{1\}$. Furthermore, the unicity up to homotopy of lifting implies that $[F(f)]$ is independent of the choice of the lifting, and that $f \sim g$ implies $[F(f)] = [F(g)]$. If $g : y \to z$ is an other morphism, and $\psi : \Sigma^n[2]_t \to C$ corresponds to the composition of $f$ and $g$, there is a lift in the following diagram:

$$\begin{array}{c} \Sigma^n[2]_t \cup (\Sigma^n \partial[2]) \times [1]_t \xrightarrow{\phi \cup h_f \cup h_g \cup h_{f \circ g}} C \\ \downarrow \\ \Sigma^n[2]_t \times [1]_t \end{array}$$

95

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Restricted to $\Sigma^n[2]_t \times \{1\}$ this shows that $F$ commutes with compositions. We then have defined a functor

$$F : \pi_n(s, t, C) \to \pi_n(s', t', C).$$

Using exactly the same procedure, where we just invert 0 and 1, we define a functor:

$$G : \pi_n(s', t', C) \to \pi_n(s, t, C).$$

Now, we have a lift in the following diagram:

$$\begin{array}{c} \mathbf{D}_n \times \Lambda^2[2]^\sharp \cup \partial\mathbf{D}_n \times [2]^\sharp \xrightarrow{h_x \cup h_{F(x)} \cup \psi(id \times s^0)} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad k_x \\ \mathbf{D}_n \times [2]^\sharp \end{array}$$

The restriction of $k_x$ to $\mathbf{D}_n \times [0, 1]_t$ provides a thin cell $x \to G(F(x))$, which corresponds to an isomorphism in $\pi_n(s, t, C)$ according to proposition 2.4.1.8. If $f : x \to y$ is a $(n + 1)$-cell, there is a lifting in the following diagram:

$$\begin{array}{c} \mathbf{D}_{n+1} \times \Lambda^2[2]^\sharp \cup \partial\mathbf{D}_{n+1} \times [2]^\sharp \xrightarrow{h_f \cup h_{F(f)} \cup k_x \cup k_y} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad k_f \\ \mathbf{D}_{n+1} \times [2]^\sharp \end{array}$$

The restriction of $k_f$ to $\mathbf{D}_{n+1} \times [0, 1]_t$ induces in $\pi_n(s, t, C)$ a commutative diagram:

$$\begin{array}{c} x \longrightarrow G F x \\ [f] \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad y \longrightarrow G F y. \end{array}$$

We then have an invertible natural transformation $\psi : id \to GF$. Similarly we can construct an other natural transformation $id \to GF$, which shows the desired equivalence of categories.

**2.4.1.10.** Let $a$ be an element of $\mathrm{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, C)$. We define

$$\pi_n(a, C) := \pi_n(s, t, C) \tag{2.4.1.11}$$

where $s, t$ is a pair of parallel arrows such that $s \cup t$ represents $a$. The previous proposition shows that this is well defined.

96

2.4. GLOBULAR EQUIVALENCES

#### 2.4.2 A criterion to be a weak equivalence

2.4.2.1. A morphism  \( p: C \to D \)  between complicial sets is a D-equivalence if

\[
\pi_ {0} (C) \to \pi_ {0} (D)
\]

is an equivalence of categories, and for any n > 0 and pair of parallel arrow s, t, the induced functor

\[
\pi_ {n} (s, t, C) \rightarrow \pi_ {n} (p s, p t, D)
\]

is an equivalence of categories.

A D-trivial fibration is a fibration having the right lifting property against  \( \partial D_{n} \rightarrow D_{n} \)  and  \( \mathbf{D}_{n} \rightarrow (\mathbf{D}_{n})_{t} \) .

Lemma 2.4.2.2. Let \(\alpha \in \{-, +\}\). The morphism \(i_{n+1}^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t\) is an acyclic cofibration.

Proof. We have a pushout diagram

\[
\begin{array}{c} \mathbf {D} _ {n} \times \{\alpha \} \cup \partial \mathbf {D} _ {n} \times [ 1 ] _ {t} \xrightarrow {i d \cup \partial \times s ^ {0}} \mathbf {D} _ {n} \times \{\alpha \} \\ \Biggl \downarrow \\ \mathbf {D} _ {n} \times [ 1 ] _ {t} \xrightarrow {} (\mathbf {D} _ {n}) _ {t} \end{array}
\]

The left hand morphism being an acyclic cofibration, this concludes the proof.

Lemma 2.4.2.3. Acyclic cofibrations between complicial sets are D-equivalences.

Proof. Let \( i: A \to B \) be an acyclic cofibration. The morphism \( i \) admits a retraction \( r: B \to A \):

\[
\begin{array}{c} A \xrightarrow {i d} A \\ i \Big \downarrow \quad \nearrow \\ B. \end{array}
\]

and a homotopy  \( \psi \)  between  \( id_{B} \)  and ir which is constant on the image of i, obtained as the lift in the following diagram:

\[
\begin{array}{c} B \times \{0 \} \coprod_ {A \times \{0 \}} A \times [ 1 ] _ {t} \longrightarrow B \\ \Big \downarrow \\ B \times [ 1 ] _ {t} \end{array}
\]

Let \( n > 0 \) be an integer, and \( s, t \) be two \( (n - 1) \)-cells of \( C \). The retraction implies that \( i_{!} \) is an injection on morphisms. For any \( n \)-cell \( y: i(s) \to i(t) \) in \( B \), the homotopy \( \psi \) induces

97

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

a thin cell $y \to ir(y)$ which corresponds to an isomorphism in $\pi_n(is, it, B)$ according to proposition 2.4.1.8. The functor $i_!$ is then essentially surjective. For any $(n + 1)$-cell $f : i(x) \to i(y)$, the homotopy $\psi$ induces an equivalence $[ir(f)] \sim [f]$. The morphism $i_!$ is a surjection on morphisms. All put together, $i_!$ is fully faithfull and essentially surjective, and is then an equivalence. We proceed similarly to show that $i_! : \pi_0(A) \to \pi_0(B)$ is an equivalence.

**Lemma 2.4.2.4.** *Suppose given a commutative triangle between complicial sets*

![img-71.jpeg](img-71.jpeg)

*If $i$ is an acyclic cofibration, and $g$ is a $\mathbf{D}$-equivalence, then $f$ is a $\mathbf{D}$-equivalence.*

*Proof.* Let $s, t$ be any pair of parallel arrows in $B$. There exists a pair of parallel arrows $s', t'$ in $A$ such that $s \cup t$ and $is' \cup it'$ correspond to the same element in $[\partial \mathbf{D}_n, B]$. We then have a diagram:

$$\begin{array}{c} \pi(s, t, B) \longrightarrow \pi(fs, ft, C) \\ \downarrow \sim \qquad \qquad \qquad \downarrow \sim \\ \pi(s, t, B) \xrightarrow{\sim} \pi(is, it, B) \longrightarrow \pi(gs, gt, C). \\ \sim \end{array}$$

where arrows labeled by $\sim$ are isomorphisms according to lemmas 2.4.1.9 and 2.4.2.3. By two out of three, this shows that $\pi(s, t, B) \to \pi(fs, ft, C)$ is an isomorphism, and $f$ is then a $\mathbf{D}$ equivalence.

**Proposition 2.4.2.5.** *Let $p : C \to D$ be a fibration between complicial sets. The morphism $p$ is a $\mathbf{D}$-trivial fibration if and only if it is a $\mathbf{D}$-equivalence.*

*Proof.* If $p$ is a $\mathbf{D}$-trivial fibration, it is obvious that it is a $\mathbf{D}$-equivalence. For the converse, suppose $p$ is a fibration and a $\mathbf{D}$-equivalence, and consider a diagram

$$\begin{array}{c} \partial \mathbf{D}_n \longrightarrow C \\ \downarrow \qquad \qquad \qquad \downarrow_p \\ \mathbf{D}_n \xrightarrow{x} D \end{array}$$

As $p$ is a $\mathbf{D}$-equivalence this implies that there exists a cell $\overline{x} : \mathbf{D}_n \to C$ together with a thin $(n + 1)$-cell $y : p(\overline{x}) \to y$. All this data corresponds to a diagram:

$$\begin{array}{c} \mathbf{D}_n \xrightarrow{\overline{x}} C \\ \delta_{n+1}^0 \downarrow \qquad \qquad \qquad \downarrow_p \\ (\mathbf{D}_{n+1})_t \xrightarrow{y} D \end{array}$$

98

2.4. GLOBULAR EQUIVALENCES

The left hand morphism being an acyclic cofibration according to 2.4.2.2, this diagram admits a lift $h : (\mathbf{D}_{n+1})_t \to C$. The restriction of $h$ to $i_{n+1}^+$ provides a lift in the first diagram. Now, we consider a diagram of shape:

$$\begin{array}{c} \mathbf{D}_n \xrightarrow{g} C \\ \downarrow \qquad \qquad \qquad \downarrow_p \\ (\mathbf{D}_n)_t \longrightarrow D \end{array}$$

with $n > 1$. Let $s, t$ be respectively the $(n - 1)$-source and the $(n - 1)$-target of $g$. Hypotheses imply that $[p(g)]$ is an isomorphism in $\pi_n(s, t, D)$ and because $p$ is a $\mathbf{D}$-equivalence, so is $[g]$. According to lemma 2.4.1.8, this implies that $g$ is thin. There exists then a lifting in the previous diagram. The case $n = 1$ is similar. The morphism $f$ is then a $\mathbf{D}$-trivial fibration.

**Lemma 2.4.2.6.** *Let $p : X \to Y$ be a $\mathbf{D}$-trivial fibration between complicial sets. Then for any $x \in X_0$, the induced fibrations*

$$X_{/x} \to X \times_Y Y_{/p(x)} \quad \text{and} \quad X_{x/} \to X \times_Y Y_{p(x)/}$$

*are $\mathbf{D}$-trivial fibrations.*

*Proof.* We define $\mathbb{P}(p, n)$ to be the statement that $p$ has the right lifting property against

$$\mathbf{D}_n \cup \partial \mathbf{D}_n \star [0] \to \mathbf{D}_{n+1} \star [0] \text{ and } (\mathbf{D}_n)_t \cup \mathbf{D}_n \star [0] \to (\mathbf{D}_n)_t \star [0]$$

and against

$$[0] \stackrel{co}{\star} \partial \mathbf{D}_n \cup \mathbf{D}_n \to [0] \stackrel{co}{\star} \mathbf{D}_{n+1} \text{ and } [0] \star \mathbf{D}_n \cup (\mathbf{D}_n)_t \to [0] \stackrel{co}{\star} (\mathbf{D}_n)_t$$

We then have to show that for any $n$, $\mathbb{P}(p, n)$ holds.

First, it is obvious that each $\mathbf{D}$-equivalence $p$ satisfies $\mathbb{P}(p, 0)$. As $p$ is a fibration, the corollaries 2.3.2.2 and 2.3.2.3 then imply that $\mathbb{P}(p, n + 1)$ is equivalent to $\mathbb{P}(p(a, b), n)$ for any $a, b \in X_0$, where $p(a, b)$ is the induced morphism: $X(a, b) \to Y(p(a), p(b))$.

Using the fact that $p(a, b)$ is a $\mathbf{D}$-trivial fibration as soon as $p$ is, this shows the desired result.

**Lemma 2.4.2.7.** *$\mathbf{D}$-Trivial fibrations between complicial sets have the right lifting property against $\partial[n] \to [n]$.*

*Proof.* Let $C$ be the class of cofibrations having the right lifting property against $\mathbf{D}$-equivalences. The lemma 2.4.2.6 implies that for any $K \to L$ in $C$, the induced morphism:

$$L \cup K \star [0] \to L \star [0]$$

is in $C$. The class $C$ is then closed under Leibniz join. Furthermore, it includes $\partial[1] \to [1]$, and then, by induction, it includes $\partial[n] \to [n]$ for any integer $n$.

99

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

**Lemma 2.4.2.8.** **D**-Trivial fibrations between complicial sets have the right lifting property against $[n] \to [n]_t$.

*Proof.* Let $p$ be **D**-trivial fibrations between complicial sets, and $C_{n,p}$ be the set of objects $A$ such that $p$ has the right lifting property against:

$$A \to \tau_{n-1}^i(A).$$

This set is then closed under colimits, and by zigzags of acyclic cofibrations. Let $k \le n$ be two integers. We define $\mathbb{P}(k, n, p)$ to be the statement that

$$\Sigma[n-k]_\circ \star [k-1] \quad \text{and} \quad [k-1]_\circ \stackrel{co}{\star} \Sigma[n-k]$$

are in $C_{n+1,p}$. The statement $\mathbb{P}(0, 0, f)$ corresponds to the belonging of $\mathbf{D}_1$ to $C_{1,p}$, which is obviously true. Suppose that $0 < k$ and $\mathbb{P}(k-1, n, p)$. According to theorem 2.3.2.1, the object $\Sigma[n-k]_\circ \star [k-1]$ is linked by a zigzag of acyclic cofibrations to the colimit of

$$(\Sigma[n-k]_\circ \forall [1]) \star [k-2] \leftarrow (\Sigma[n-k]_\circ) \star [k-2] \rightarrow (\Sigma[n-k+1]_\circ) \star [k-2]$$

The center object and the left hand object are in $C_{n+1,p}$ because there are invariant under $\tau_n^i$, and the right hand object is in $C_{n+1,p}$ by induction hypothesis. The object $\Sigma[n-k]_\circ \star [k-1]$ is then in $C_{n+1,p}$. We demonstrate similarly that $[k-1]_\circ \stackrel{co}{\star} \Sigma[n-k]$ is in $C_{n+1,p}$.

This then implies $\mathbb{P}(k, n, p)$. Eventually, $\mathbb{P}(0, n+1, p)$ is equivalent to $\mathbb{P}(n, n, p(a, b))$ for any pair of objects $(a, b) \in X_0$. The statement $\mathbb{P}(k, n, p)$ is then true for any $k, n$ and **D**-trivial fibrations between complicial sets $p$. This implies that $p$ has the right lifting property against $[n] \to [n]_t$.

**Theorem 2.4.2.9.** *Let $p$ be a map between complicial sets. Then $p$ is a weak equivalence if and only if it is a **D**-equivalence.*

*Proof.* According to lemmas 2.4.2.3 and 2.4.2.4 we can restrict ourselves to the case where $p$ is a fibration. If it is a weak equivalence, $p$ is then a trivial fibration and is then a **D**-equivalence. Suppose now that $p$ is a **D**-equivalence. According to proposition 2.4.2.5, $p$ is then a **D**-trivial fibration. Lemmas 2.4.2.7 and 2.4.2.8 imply that $p$ is a trivial fibration.

**Definition 2.4.2.10.** Let $p : X \to Y$ be a morphism between complicial sets. The morphism $p$ is *essentially surjective* if for any $x \in Y_0$, there exists $\bar{x} \in X_0$ together with a thin cell $\bar{x} \to x$. The morphism $f$ is *fully faithful* if the induced morphisms:

$$X(a, b) \to Y(pa, pb)$$

are weak equivalences for any $a, b \in X_0$.

100

2.4. GLOBULAR EQUIVALENCES

Corollary 2.4.2.11. Let p be a map between complicial sets. Then p is a weak equivalence if and only if it is fully faithfull and essentially surjective.

Proof. If p is a weak equivalence, it is then fully faithfull and essentially surjective. Conversely, suppose p is fully faithfull and essentially surjective. The morphism π₀(X) → π₀(Y) is fully faithfull and essentially surjective, and then an equivalence of category. For (a, b) a pair of 0-cells, we have equalities:

$$\pi_1(a, b, X) \xlongequal{\quad} \pi_0(X(a, b))$$

$$\pi_1 p \downarrow \qquad \qquad \qquad \qquad \downarrow \pi_0 p(a, b)$$

$$\pi_1(pa, pb, Y) \xlongequal{\quad} \pi_0(Y(pa, pb)).$$

The morphism π₁(a, b, p) is then an equivalence of categories. For (s, t) a pair of parallel arrows of dimension > 1, if we denote by a and b the 0-source and the 0-target of s and t, we have a diagram:

$$\pi_n(s, t, X) \xlongequal{\quad} \pi_{n-1}(s, t, X(a, b))$$

$$\pi_n p \downarrow \qquad \qquad \qquad \qquad \downarrow \pi_{n-1}(s, t, p(a, b))$$

$$\pi_n(pa, pb, Y) \xlongequal{\quad} \pi_{n-1}(s, t, Y(pa, pb)).$$

The morphism πₙ(a, b, p) is then an equivalence of categories. The morphism p is then a D-equivalence, and according to 2.4.2.9, a weak equivalence. □

### 2.4.3 A criterion to be a weakly invertible transformation

The purpose of this section is to show the following proposition:

Proposition 2.4.3.1. Let i : mPsh(Δ) → mPsh(Δ) and j : mPsh(Δ) → mPsh(Δ) be two left Quillen functors and ψ : i → j a natural transformation. If ψ(Dₙ) : i(Dₙ) → j(Dₙ) is a weak equivalence for any n, then ψ(X) : i(X) → j(X) is a weak equivalence for any X.

For the remaining of this section, we fix two left Quillen functors i, j and a natural transformation ψ : i → j satisfying the previous hypothesis. We denote by Nᵢ and Nⱼ the right adjoints of i and j.

Lemma 2.4.3.2. Morphisms ψ(∂Dₙ) : i(∂Dₙ) → j(∂Dₙ) are weak equivalences.

Proof. We proceed by induction on n. The case n = 0 is trivial. Suppose then the result true at the stage n − 1. Remark then that ∂Dₙ is the colimit and the homotopy colimit of the span

$$\mathbf{D}_{n-1} \leftarrow \partial \mathbf{D}_{n-1} \rightarrow \mathbf{D}_{n-1}$$

101

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

As $i$ and $j$ are left Quillen functors, the induction hypothesis implies that $\psi(\partial\mathbf{D}_n): i(\partial\mathbf{D}_n) \to j(\partial\mathbf{D}_n)$ is a weak equivalence. $\square$

**Lemma 2.4.3.3.** *Morphisms $\psi((\mathbf{D}_n)_t): i((\mathbf{D}_n)_t) \to j((\mathbf{D}_n)_t)$ are weak equivalences.*

*Proof.* There is a diagram:

$$
\begin{array}{c}
i_{!}\mathbf{D}_{n-1} \xrightarrow[\sim]{\psi(\mathbf{D}_n)} j_{!}\mathbf{D}_{n-1} \\
i_{!}(i_{n}^{-}) \Big\downarrow \sim \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\
i_{!}(\mathbf{D}_n)_t \xrightarrow[\psi((\mathbf{D}_n)_t)]{} j_{!}(\mathbf{D}_n)_t
\end{array}
$$

By two out of three, this shows that $\psi((\mathbf{D}_n)_t)$ is a weak equivalence. $\square$

**Lemma 2.4.3.4.** *For any complicial set $Y$, the canonical morphism $N_j Y \to N_i Y$ is a weak equivalence.*

*Proof.* Let $Y$ be a complicial set. For any integer $n$, we have by adjunction a bijection

$$
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_i Y)
$$

and according to lemmas 2.4.3.2 and 2.4.3.3, we have bijections

$$
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, N_i Y)
$$

$$
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_i Y).
$$

Let $a$ be an element of $\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial\mathbf{D}_n, N_j Y)$. We recall that the category $\pi_n(a, N_j Y)$ is defined in 2.4.1.11. The previous equivalences implies that we have an isomorphism of category

$$
\pi_n(a, N_j Y) \cong \pi_n(a, N_j Y).
$$

which concludes the proof according to theorem 2.4.2.9. $\square$

*Proof of the proposition 2.4.3.1.* Let $X$ be any marked simplicial set and $Y$ a complicial set. We have equalities:

$$
\begin{array}{ccc}
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(j_{!}X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, j^*Y) \\
\downarrow & & \downarrow \\
\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(i_{!}X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, i^*Y)
\end{array}
$$

Lemma 2.4.3.4 implies that the right hand morphism is a bijection, and so is the left hand morphism. For any $X$, $\psi(X)$ is then a weak equivalence. $\square$

102

2.4. GLOBULAR EQUIVALENCES

#### 2.4.4 Weak characterization of the identity

For the rest of this section, we fix a left Quillen functor  \( i : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta) \)  such that there exists a zigzag of weakly invertible natural transformations:

\[
i (\mathbf {D} _ {-}) \leftrightarrow \mathbf {D} _ {-}.
\]

Lemma 2.4.4.1. Let \( n \) be any integer, the following natural transformations are pointwise acyclic cofibrations:

\[
i \tau_ {n} ^ {i} \rightarrow \tau_ {n} ^ {i} i \tau_ {n} ^ {i} \gets \tau_ {n} ^ {i} i.
\]

Proof. These are natural transformations between left Quillen functors. The hypothesis implies that they induce weak equivalences on globes of dimension inferior or equal to n. Remark that for any k > n, as  \( i_{k-1}^{-}: D_{k-1} \to (D_k)_t \)  is an acyclic cofibration and  \( \tau_n^i \)  preserves them,  \( \tau_n^i D_{k-1} \to \tau_n^i D_k \)  is an acyclic cofibration. A direct induction implies that  \( D_n = \tau_n^i D_n \to \tau_n^i D_k \)  is an acyclic cofibration. We then have a commutative diagram:

![img-72.jpeg](img-72.jpeg)

where all morphisms labelled by  \( \sim \)  are weak equivalences.

By two out of three, this implies that theses natural transformations induce weak equivalences on all globes, and proposition 2.4.3.1 concludes the proof. \(\square\)

Proposition 2.4.4.2. There exists a zigzag of weakly invertible natural transformations

\[
i \leftrightarrow j
\]

where \(j\) is a left Quillen functor such that \(j([n]) = i([n])\) and \(j([n]_t) = \tau_{n-1}^i i([n])\), and such that the image of \([n] \to [n]_t\) by \(j\) is induced by the canonical morphism \(id \to \tau_{n-1}^i(id)\).

Proof. We define  \( \tilde{i} \)  (resp. j) to be the colimit preserving functor defined on representables by  \( \tilde{i}([n]) := i([n]) \)  and  \( \tilde{i} := ([n]_{t}) = \tau_{n-1}^{i} i([n]_{t}) \)  (resp.  \( j([n]) := i([n]) \)  and  \( j([n]_{t}) := \tau_{n-1}^{i} i([n]) \) ). We then have a zigzag of natural transformations

\[
i \stackrel {\sim} {\to} \tilde {i} \stackrel {\sim} {\leftarrow} j.
\]

that are pointwise acyclic cofibrations according to 2.4.4.1. This implies that both \(\tilde{i}\) and \(j\) are left Quillen functors.

103

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

2.4.4.3. In the following lemmas, we use the Steiner theory recalled in section 1.2.1.

Lemma 2.4.4.4. Let m be an integer and X and Y be two  \( (0,\omega) \) -categories admitting a loop free and atomic basis. We denote by 0, 1 and t the three points of  \( \Sigma X \vee [1] \) . Let

\[
f: \Sigma^ {m} ([ X, 1 ] \star Y) \to \Sigma^ {m} (([ X, 1 ] \vee [ 1 ]) \star Y)
\]

be a morphism fitting in the following diagram:

![img-73.jpeg](img-73.jpeg)

where \( g \) sends 0 on 0, and sends 1 on \( t \) and the right vertical morphism induced by the retraction \( [X,1] \vee [1] \to [X,1] \).

Then \(f\) is \(\Sigma^{m}(\nabla \star Y)\).

Proof. All these categories admit loop free and atomic basis. We can then show this lemma in the category of augmented directed complexes. Furthermore, in this category, the suspension only makes an index shift, so we can assume without loss of generality that m = 0.

The commutativity of the diagram implies that

\[
f (0 \star x) = 0 \star x
\]

\[
f (1 \star x) = t \star x
\]

\[
f ([ x, 1 ] \star y) = [ x, 1 ] \star y + r _ {x, y}
\]

where \( r_{x,y} \) is a positive sum of elements of \( (B_{[1]\star Y})_{|x| + |y| + 1} \). We show by induction on \( |x| + |y| \) that:

\[
r _ {x, y} = [ 1 ] \star y \quad \text { if } | x | = 0
\]

\[
= 0 \quad \text { if } | x | > 0.
\]

Suppose the result true when the sum of dimensions of x and y is  \( (k-1) \) . Let x, y be two cells such that  \( |x| + |y| = k \) . Case  \( |x| = 0 \) . The commutativity of f with  \( \partial \)  and the induction hypothesis imply that

\[
\begin{array}{l} \partial r _ {x, y} = f (\partial ([ x, 1 ] \star y)) - \partial ([ x, 1 ] \star y) \\ = \{t \} \star y - \{0 \} \star y + f ([ x, 1 ] \star \partial y) - \{1 \} \star y + \{0 \} \star y - [ x, 1 ] \star \partial y \\ = \{t \} \star y - \{1 \} \star y + [ 1 ] \star \partial y \\ \end{array}
\]

and \( r_{x,y} \) is then equal to \( [1] \star y \). Case \( |x| > 0 \). The commutativity of \( f \) with \( \partial \) implies that

\[
\partial r _ {x, y} = 0
\]

and \(r_{x,y}\) is then equal to 0.

□

104

2.4. GLOBULAR EQUIVALENCES

Lemma 2.4.4.5. Let m be an integer and X and Y be two  \( (0,\omega) \) -categories admitting a loop free and atomic basis. We denote by 0, 1 and t the three points of  \( \Sigma X \vee [1] \) . Let

\[
f: \Sigma^ {m} ([ X, 1 ] \star Y) \to \Sigma^ {m} (([ X, 1 ] \vee [ 1 ]) \star Y)
\]

be a morphism fitting in the following diagram:

![img-74.jpeg](img-74.jpeg)

Then \( f \) is the morphism induced by the retraction \( [X,1] \vee [1] \to [X,1] \).

Proof. The proof is an easy computation using Steiner theory, similar to the one done in lemma 2.4.4.4, and left to the reader. \(\square\)

##### 2.4.4.6. Let C be the subcategory of marked simplicial sets whose

- objects are the marked simplicial sets \( X \) such that \( \mathrm{R}(X) \) has no non-trivial automorphisms, and such that there exists a (necessary unique) isomorphism

\[
\phi_ {X}: \mathrm{R} (i X) \to \mathrm{R} (X),
\]

- morphisms are the maps \( f: X \to Y \) making the induced diagram

\[
\begin{array}{c} \operatorname{R} (i (X)) \xrightarrow {\phi_ {X}} \operatorname{R} (X) \\ \operatorname{R} (i (f)) \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{R} (i (Y)) \xrightarrow {\phi_ {Y}} \operatorname{R} (Y) \end{array}
\]

commutative.

Remark 2.4.4.7. As R sends acyclic cofibrations to isomorphisms, C is stable by zigzags of acyclic cofibrations. Moreover, as R and i preserve colimits, for any diagram  \( F: I \to C \)  such that the  \( (0, \omega) \) -category  \( \mathrm{R}(\mathrm{colim}_{I} F) \)  has no non-trivial automorphisms,  \( colim_{I} F \)  is in C. Eventually, the colimit of any natural transformation between two such diagrams is in C.

Lemma 2.4.4.8. Let \((k,n)\) be a couple of integers such that \(k\leq n\). We set the convention \([-1]:= \emptyset\). For any integer \(m\), the following assertion holds:

105

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

(1) $\Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ and $\Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$ are in $C$.
(2) For any $-1 \le l \le k-1$ and $0 \le p \le n-k$, and any monomorphisms $[l] \to [k-1]$ and $[p] \to [n-k]$, the morphisms

$$\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([l]_\circ \overset{co}{\star} \Sigma[p]) \to \Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$$

are in $C$.

(3) For any $\epsilon \in \{0, 1\}$, the morphisms

$$\Sigma^m(\{\epsilon\} \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([k-1]_\circ \overset{co}{\star} \{\epsilon\}) \to \Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$$

are in $C$.

(4) If $k > 0$, the morphisms

$$\Sigma^m(\emptyset \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([k-1]_\circ \overset{co}{\star} \emptyset) \to \Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$$

are in $C$.

Proof. We will proceed by induction on $(k, n)$.

- The case $(0, 0)$ corresponds to the belonging of globes to $C$, which is true by the assumptions we made on the functor $i$ and by the proposition 1.2.3.11 that assert that the globes have no non-trivial automorphisms.
- We now suppose that the case $(n-1, n-1)$ holds and we are willing to show the case $(0, n)$. The assertions (1) and (2) are direct consequences of the case $(n-1, n-1)$ after remarking the isomorphisms:

$$\Sigma^m \Sigma[n] \cong \Sigma^{m+1}((\Sigma[0]_\circ) \star [n-2]) \qquad \Sigma^m \Sigma[n]_\circ \cong \Sigma^{m+1}([n-2]_\circ \overset{co}{\star} (\Sigma[0]))$$

It remains to show the third assertion. Let $m$ be any integer and $\epsilon \in \{0, 1\}$. By induction hypothesis and by the belonging of globes to $C$, the following morphism

$$\Sigma^m(\{\epsilon\}) \to \Sigma^m(\Sigma\{0\}) \cong \Sigma^{m+1}\{0\} \to \Sigma^{m+1}((\Sigma[0]_\circ) \star [n-2]) \cong \Sigma^m \Sigma[n]$$

is in $C$. As the morphism $\Sigma^m(\{\epsilon\}) \to \Sigma^m \Sigma[n]$ is their composite, it belongs to $C$. We proceed similarly to show that $\Sigma^m(\{\epsilon\}) \to \Sigma^m \Sigma[n]_\circ$ belongs to $C$. This concludes the proof of the case $(0, n)$.

- Suppose the result true for the couples $(k-1, n)$, $(k-1, n-1)$ and $(k-1, k-1)$ for an integer $k$ strictly superior to 0 and inferior or equal to $n$. We are willing to show the case $(k, n)$. Let $m$ be any integer.

As $R$ commutes with Gray operations and pushouts, the lemma 1.2.3.10 implies that $\Sigma^m((\Sigma[n-k]_\circ \coprod_{[0]}[1]) \star [k-2])$ together with all the objects appearing in the statement

106

2.4. GLOBULAR EQUIVALENCES

of this lemma are sent by R to  \( (0,\omega) \) -categories with loop free and atomic basis and with no non-trivial automorphisms. Remark 2.4.4.7 implies that for one of these objects (resp. a morphism between them) to belong to C, it is sufficient to show that it is linked by a zigzag of acyclic cofibrations to the colimit, computed in  \( \mathrm{mPsh}(\Delta) \) , of a diagram with value in C (resp. in the arrow category of C).

As \(\Sigma[0]_{\circ} = [1]\), the case \((k - 1, k - 1)\) implies that the morphism

\[
\Sigma^ {m} (\{0 \} \star [ k - 1 ]) \to \Sigma^ {m} ([ 1 ] \star [ k - 1 ])
\]

is in \(C\). Combined with the case \((k - 1, n - 1)\), this implies that the diagram

![img-75.jpeg](img-75.jpeg)

is in \(C\), and so is it's vertical colimits. As the codomain is weakly equivalent to \(\Sigma^m((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2])\), this implies that \(C\) includes the canonical morphism

\[
\Sigma^ {m} ((\Sigma [ n - k ] _ {\circ}) \star [ k - 2 ]) \hookrightarrow \Sigma^ {m} ((\Sigma [ n - k ] _ {\circ} \vee [ 1 ]) \star [ k - 2 ]). \tag {2.4.4.9}
\]

We can show similarly that the canonical morphism

\[
\Sigma^ {m} ([ 1 ] \star [ k - 2 ]) \hookrightarrow \Sigma^ {m} ((\Sigma [ n - k ] _ {\circ} \vee [ 1 ]) \star [ k - 2 ]). \tag {2.4.4.10}
\]

is in \(C\).

The image by R of the canonical morphism

\[
\Sigma^ {m} ((\Sigma [ n - k ] _ {\circ} \vee [ 1 ]) \star [ k - 2 ]) \to \Sigma^ {m} ((\Sigma [ n - k ] _ {\circ}) \star [ k - 2 ])
\]

induced by the retraction \(\Sigma[n - k]_{\circ} \vee [1] \to \Sigma[n - k]_{\circ}\) fulfills the condition of lemma 2.4.4.5 and then belongs to \(C\). The lemma 2.4.4.4 then implies that the morphism

\[
\Sigma^ {m} (\nabla \star [ k - 2 ]): \Sigma^ {m} ((\Sigma [ n - k ] _ {\circ}) \star [ k - 2 ]) \to \Sigma^ {m} ((\Sigma [ n - k ] _ {\circ} \vee [ 1 ]) \star [ k - 2 ]) (2. 4. 4. 1 1)
\]

is in \( C \). We will use freely in the rest of the proof that morphisms (2.4.4.9), (2.4.4.10) and (2.4.4.11) are in \( C \).

Theorem 2.3.2.1 implies that the object \(\Sigma^m (\Sigma [n - k]_{\circ}\star [k - 1])\) is linked by a zigzag of acyclic cofibrations to the colimit of

\[
\Sigma^ {m} ((\Sigma [ n - k ] _ {\circ} \vee [ 1 ]) \star [ k - 2 ]) \gets \Sigma^ {m} (\Sigma [ n - k ] _ {\circ} \star [ k - 2 ]) \to \Sigma^ {m} (\Sigma [ n - k + 1 ] _ {\circ} \star [ k - 2 ])
\]

107

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

and the induction hypothesis implies that it belongs to $C$. We proceed similarly to show that $\Sigma^m([k-1]_\circ \stackrel{co}{\star} \Sigma[n-k])$ belongs to $C$.

Let $0 \leq l \leq k-1$ and $-1 \leq p \leq n-k$ be two integers, and $f : [l] \to [k-1]$ and $g : [p] \to [n-k]$ be two monomorphisms. Suppose first that $f$ is of shape $[0] \star f'$ for $f' : [l-1] \to [k-2]$. In this case, $\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

![img-76.jpeg](img-76.jpeg)

and the induction hypothesis implies that it belongs to $C$. Suppose now that $f$ avoids the initial object of $[k-1]$. In this case, the morphism $\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

![img-77.jpeg](img-77.jpeg)

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^m([l]_\circ \stackrel{co}{\star} \Sigma[p]) \to \Sigma^m([k-1]_\circ \stackrel{co}{\star} \Sigma[n-k])$$

belongs to $C$.

The morphism $\Sigma^m(\{0\} \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

![img-78.jpeg](img-78.jpeg)

and the induction hypothesis implies that it belongs to $C$. The morphism $\Sigma^m(\{1\} \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ is linked by a zigzag of acyclic cofibrations to the vertical

108

2.4. GLOBULAR EQUIVALENCES

colimit of the diagram

$$\begin{array}{c} \Sigma^{m}(\{1\} \star [k-1]) \cong \Sigma^{m}([1] \star [k-2]) \longmapsto \Sigma^{m}((\Sigma[n-k]_{\circ} \vee [1]) \star [k-2]) \\ \uparrow \\ \Sigma^{m}(\Sigma[n-k]_{\circ} \star [k-2]) \\ \downarrow \\ \Sigma^{m}(\Sigma[n-k+1]_{\circ} \star [k-2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that for any $\epsilon \in \{0, 1\}$,

$$\Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \{\epsilon\}) \to \Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \Sigma[n-k])$$

belongs to $C$.

Eventually, the morphism $\Sigma^{m}(\emptyset \star [k-1]) \to \Sigma^{m}(\Sigma[n-k]_{\circ} \star [k-1])$ is is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^{m}(\{1\} \star [k-2]) \longrightarrow \Sigma^{m}([1] \star [k-2]) \longmapsto \Sigma^{m}((\Sigma[n-k]_{\circ} \vee [1]) \star [k-2]) \\ \uparrow \\ \Sigma^{m}(\Sigma[n-k]_{\circ} \star [k-2]) \\ \downarrow \\ \Sigma^{m}(\Sigma[n-k+1]_{\circ} \star [k-2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \emptyset) \to \Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \Sigma[n-k])$$

belongs to $C$.

We have then proven the case $(k, n)$, and this concludes the proof.

**Lemma 2.4.4.12.** Let $F : \Delta \to (0, \omega)$-cat be a functor and $\phi : F \to \mathbb{R}$ be a invertible transformation such that for any monomorphism $i : [k] \to [n]$, the induced square

$$\begin{array}{c} F([k]) \xrightarrow{\phi_{[k]}} \mathbb{R}([k]) \\ F(i) \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow R(i) \\ F([n]) \xrightarrow{\phi_{[n]}} \mathbb{R}([n]) \end{array}$$

commutes. Then $\phi$ is an invertible natural transformation between $F$ and $\mathbb{R}$.

Proof. We can suppose without loss of generality that for all integer $n$, $F([n]) = \mathbb{R}([n])$. The hypotheses implies that for any monomorphism $i : [n] \to [m]$, $F(i) = \mathbb{R}(i)$ and it then remains to show that for any degeneracy $p : [n] \to [m]$, $F(p) = \mathbb{R}(p)$.

109

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

We proceed by induction and we then suppose that for any $0 < k \leq n$ and any degeneracy $s : [k] \rightarrow [k - 1]$, $F(s) = \mathrm{R}(s)$. As any morphism of $\Delta$ factors as a degeneracy followed by a monomorphism, the induction hypothesis implies that for any $f : [k] \rightarrow [n]$ with $k \leq n$, $F(f) = \mathrm{R}(f)$.

Let $s : [n + 1] \rightarrow [n]$ be a degeneracy. We have a *a priori* non commutative diagram:

![img-79.jpeg](img-79.jpeg)

The induction hypothesis implies that the outer and the upper square commute. As $R$ commutes with colimits, $\operatorname{colim}_{[k] \rightarrow \partial[n]} \mathrm{R}([k])$ is equivalent to $\mathrm{R}(\partial[n])$. Moreover, the inclusion $\mathrm{R}(\partial[n]) \rightarrow \mathrm{R}([n])$ induces an isomorphisms on cells of dimension lower or equal to $n$. For the lower square to commutes, we then only have to check that the top cell of $\mathrm{R}([n + 1])$ is sent on the same element on $\mathrm{R}([n])$. That is the case because the two paths send it to an unity as there is no non trivial $(n + 1)$-cells in $\mathrm{R}([n])$.

We then have $F(s) = \mathrm{R}(s)$, which concludes the induction and then the proof. $\square$

**Proposition 2.4.4.13.** *There exists an invertible natural transformation $\mathrm{R}i \rightarrow \mathrm{R}$.*

*Proof.* As $\Sigma[0]_\circ$ is isomorphic to $[1]$, the case $(n, n)$ for any integer $n$ of the lemma 2.4.4.8 imply that there exists an invertible transformation $\phi : (\mathrm{R}i)_{|\Delta} \rightarrow \mathrm{R}_{|\Delta}$ which is natural when restricted to the full subcategory of $\Delta$ whose morphisms are the monomorphisms.

The lemma 2.4.4.12 then implies that $\phi : (\mathrm{R}i)_{|\Delta} \rightarrow \mathrm{R}_{|\Delta}$ is natural. We can extend it to a natural transformation $\phi' : (\mathrm{R}i)_{|t\Delta} \rightarrow \mathrm{R}_{|t\Delta}$ thanks to the proposition 2.4.4.2.

Eventually, as both $\mathrm{R}i$ and $\mathrm{R}$ preserves colimits, we can extend $\phi'$ to a invertible natural transformation between $\mathrm{R}i$ and $\mathrm{R}$. $\square$

**Theorem 2.4.4.14.** *Let $i : \mathrm{mPsh}(\Delta) \rightarrow \mathrm{mPsh}(\Delta)$ be a left Quillen functor. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$. In particular, $i$ is a left Quillen equivalence.*

*Proof.* The proposition 2.4.4.13 implies that we have a natural transformation $\psi : i \rightarrow i_{str}$. Furthermore, hypotheses imply that this natural transformation is a weak equivalence on

110

2.4. GLOBULAR EQUIVALENCES

globes. According to proposition 2.4.3.1, $\psi$ is then a weakly invertible natural transformation. We then have a zigzag of weakly invertible natural transformations:

$$i \stackrel{\sim}{\to} i_{str} \stackrel{\sim}{\leftarrow} id.$$

**Corollary 2.4.4.15.** *Let $i : \mathrm{tPsh}(\Delta) \to \mathrm{tPsh}(\Delta)$ be a left Quillen functor. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$. In particular, $i$ is a left Quillen equivalence.*

*Proof.* We recall that the adjunction between stratified and marked simplicial sets is denoted by:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow{\perp} \mathrm{mPsh}(\Delta) : \iota$$

The proposition 2.1.2.6 states that this adjunction is a Quillen equivalence and that the functor $\iota$ preserves acyclic cofibrations.

Remark now that the functor $(\_)_{\mathrm{mk}} \circ i \circ \iota : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ verifies the hypothesis of theorem 2.4.4.14 and we then have a zigzag of of weakly invertible natural transformations:

$$(\_)_{\mathrm{mk}} \circ i \circ \iota \rightsquigarrow id$$

This induces a zigzag of of weakly invertible natural transformations:

$$i \to \iota \circ (\_)_{\mathrm{mk}} \circ i \circ \iota \circ (\_)_{\mathrm{mk}} \rightsquigarrow \iota \circ (\_)_{\mathrm{mk}} \leftarrow id$$

111

CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

112

# Chapter 3

## Complicial sets as a model of
$(\infty, \omega)$-categories

### Contents

|  **3.1 Preliminaries** | **115**  |
| --- | --- |
|  3.1.1 Segal *A*-precategories | 115  |
|  3.1.2 Stratified Segal *A*-precategories | 118  |
|  3.1.3 Gray module | 123  |
|  **3.2 Gray constructions for stratified Segal *A*-categories** | **126**  |
|  3.2.1 Gray cylinder | 126  |
|  3.2.2 Gray cone | 128  |
|  3.2.3 Link between the Gray cylinder and Gray cone | 131  |
|  3.2.4 Gray constructions are left Quillen | 133  |
|  **3.3 Quillen Adjunction with tPsh($\Delta$)** | **136**  |
|  3.3.1 Cosimplicial object | 137  |
|  3.3.2 Complicial horn inclusions | 143  |
|  3.3.3 Complicial thinness extensions | 150  |
|  3.3.4 Saturation extensions | 161  |
|  **3.4 The case $A := \text{tPsh}(\Delta)^n$** | **162**  |
|  3.4.1 Comparison with $(0, \omega)$-cat | 162  |
|  3.4.2 The other adjunction | 166  |
|  3.4.3 Complicial sets as a model of $(\infty, \omega)$-categories | 168  |

113

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF $(\infty, \omega)$-CATEGORIES

Let $n \in \mathbb{N} \cup \{\omega\}$. Following the terminology of Barwick and Schommer-Pries ([BSP21]), we call model of $(\infty, n)$-categories any model category whose corresponding $(\infty, 1)$-category is $(\infty, n)$-cat.

With the definition of $(\infty, n)$-categories given in the introduction, we have a natural model for the $(\infty, 1)$-category $(\infty, n)$-cat, given by Rezk's complete Segal $\Theta_n$-spaces, i.e. space valued presheaves on $\Theta_n$ satisfying the (homotopical) Segal conditions and (homotopical) completeness conditions. However, there are many other models, see for instance [Ara14], [BR13a], [BR20], [BR13b] (we refer to [BSP21] for a comprehensive presentation of these models and their equivalence). For example, one can mention $n$-fold Segal spaces and Simpson's and Tamsamani's Segal $n$-categories among others.

It was conjectured ([Str87], [Ver17], [BSP21]) that Verity's $n$-complicial sets were also a model of $(\infty, n)$-categories. This would imply that Campion-Kapulkin-Maehara's $n$-comical sets also are, as they are shown to be Quillen equivalent to $n$-complicial sets in [DKM21].

Results of Bergner, Gagna, Harpaz, Joyal, Lanari, Lurie, Rezk and Tierney ([BR13a],[BR20], [Rez10], [Lur09a],[Lur09b], [GHL22], [JT07]) imply that 2-complicial sets are a model of $(\infty, 2)$-categories (see [GHL22] to understand how to use all this source to obtained the desired result and [BOR21] for a direct comparison between complete Segal $\Theta_2$-spaces and 2-complicial sets). The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

To this extend, we first address the more general problem of finding sufficient conditions on a model category $A$ to build a Gray cylinder $C \mapsto I \otimes C$ and a Gray cone $C \mapsto e \star C$ on Segal precategories enriched in $A$. These two operations should be linked by the following homotopy cocartesian square

$$\begin{array}{c} \{0\} \otimes C \longrightarrow I \otimes C \\ \downarrow \qquad \qquad \qquad \downarrow \\ e \longrightarrow e \star C \end{array}$$

where $e$ is the terminal object. The conditions that $A$ has to fulfill are encapsulated in the notion of Gray module (paragraph 3.1.3.3). Thanks to the Gray cylinder and cone, we can show the following theorem:

**Theorem 3.3.4.2.** If $A$ is a Gray module, there is a Quillen adjunction between the Ozornova-Rovelli model structure for $\omega$-complicial sets on stratified simplicial sets and stratified Segal precategories enriched in $A$ where the left adjoint sends $[n]$ to $e \star e \star \ldots \star e \star \emptyset$

114

3.1. PRELIMINARIES

We will apply this theorem to the case where $A$ is the category of stratified simplicial sets endowed with the model structure for $\omega$-complicial sets, and after tedious work, we get

**Theorem 3.4.3.2.** *Let $n \in \mathbb{N}$. The model structure for $n$-complicial sets is a model of $(\infty, n)$-categories.*

As a corollary we have

**Theorem 3.4.3.14.** *The adjunction between the model structure for complete Segal $\Theta$-spaces and $\omega$-complicial set constructed in [OR22] is a Quillen equivalence.*

## 3.1 Preliminaries

### 3.1.1 Segal $A$-precategories

Let $A$ be a category of stratified presheaves on a elegant Reedy category (as defined in paragraph 1.1.2.5 and section 2.1.2), endowed with a nice model structure (as defined in paragraph 2.1.1.8). We suppose furthermore that the terminal element of $A$, denoted by $e$, is representable. We then have an adjunction

$$\iota : \text{Set} \xrightarrow{\perp} A : ob \tag{3.1.1.1}$$

where the left adjoint sends a set $S$ onto $\coprod_S e$ and the right adjoint is the evaluation at $e$. The objects lying in the image of $\iota$ are called *discrete objects*.

An object $C$ of $\text{Fun}(\Delta^{op}, A)$ is a *Segal $A$-precategory* if $C_0$ is discrete. We denote by $\text{Seg}(A)$ the full subcategory of $\text{Fun}(\Delta^{op}, A)$ spanned by the Segal $A$-precategories.

**3.1.1.2.** We consider the functor $A \times \Delta \to \text{Fun}(\Delta^{op}, A)$ defined by the assignation $a \times [n] \to |[a, n]|$ where $|[a, n]|([m]) := a \times \iota(\text{Hom}_\Delta([m], [n]))$. We define the Segal $A$-precategory $[a, n]$ as the pushout:

$$\bigcup_{k \le n} |[a, \{k\}]| \longrightarrow |[a, n]|$$
$$\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad |[e, 0]| \longrightarrow [a, n]$$

The object $[e, 0]$ is simply denoted by $[0]$. Remark that this object is the terminal Segal $A$-precategory.

115

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

The assignation \((a, n) \mapsto [a, n]\) induces by left Kan extension a colimit preserving functor

\[
[ \_, \_ ]: A \times \mathrm{Psh} (\Delta) \to \mathrm{Seg} (A).
\]

The image of this functor is dense in \(\operatorname{Seg}(A)\).

For \(\{n_i\}_{i\leq k}\) and \(\{a\to a_i\}_{i\leq k}\) two finite sequences, we denote by \([a_0,n_0]\vee [a_1,n_1]\vee \ldots \vee [a_k,n_k]\) the Segal \(A\) -precategory fitting in the following pushout:

![img-80.jpeg](img-80.jpeg)

The case we will use the most is the one of the Segal \(A\)-precategories \([e,1] \vee [a,n]\) and \([a,n] \vee [e,1]\) corresponding to the sequence \(((1,n),(a \to e,a \to a))\) and \(((n,1),(a \to a,a \to e))\).

3.1.1.3. Let B be the Reedy category and M the subset of objects of B such that A is the category of M-stratified presheaves on B. We define the category  \( \Delta[B] \)  as the fully faithful subcategory of  \( \operatorname{Seg}(A) \)  whose objects are of shape  \( [b,n] \)  for  \( b\in B \)  and n an integer. Eventually, we define  \( \Delta[M] \)  as the set of objects of shape  \( [b,n] \)  for  \( b\in M \)  and n>0. We can easily check that the category  \( \operatorname{Seg}(A) \)  is the category of  \( \Delta[M] \) -stratified presheaves on  \( \Delta[B] \) .

A cellular model for  \( \operatorname{tSeg}(A) \)  is given by the set of morphisms  \( [b,\partial n]\cup[a,n]\to[b,n] \)  for n an integer, and  \( a\to b \)  a generating cofibration of A.

Eventually, for any Segal \(A\)-precategory \(C\), we have an isomorphism

\[
C \cong \underset {\Delta [ t B ] / C} {\mathrm{colim}} [ b, n ].
\]

Following the definition of section 2.1.2, a morphism between Segal precategories is entire if it is the identity on the underlying  \( \Delta[B] \) -presheaves.

Proposition 3.1.1.4. The category \(\Delta[B]\) as a structure of elegant Reedy category.

Proof. Remark first that \(\mathrm{Hom}_{\Delta [B]}([a,n],[b,m])\) fits in the following cocartesian square:

![img-81.jpeg](img-81.jpeg)

116

3.1. PRELIMINARIES

We then define the degree functor $ob(\Delta[B]) \to \mathbb{N}$ by the formula $d([b, n]) = d(b)d(n)$. The subcategory $(\Delta[B])_+$ is the image of $\Delta_+ \times B_+$, and the subcategory $(\Delta[B])_-$ is the image of $\Delta_- \times B_-$.

We recall that we suppose that the Reedy category $B$ is elegant. Let $X$ be a presheaf on $\Delta[B]$, $[a, n]$ an element of $\Delta[A]$, $[f, g] : [a, n] \to [a', n']$ and $[h, i] : [a, n] \to [a', n']$ two negative morphisms, an element $x$ of $X([a, n])$, two non degenerate elements $y \in X([a', n'])$ and $z \in X([a'', n''])$ such that $[f, g]^*y = x$, $[h, i]^*z = x$.

We suppose first that $n \neq 0$. We denote $\pi : B \times \Delta \to \Delta[B]$ the canonical projection and

$$\pi^* : \mathrm{Psh}(\Delta[B]) \to \mathrm{Psh}(\Delta \times B)$$

the functor obtained by precomposing. Remark that for any $a, n$, $(\pi^*X)(a, n) = X([a, n])$. Furthermore, we have again equalities $(f, g)^*y = x$, $(h, i)^*z = x$. As $\Delta \times B$ is Reedy elegant, this implies that $f = h$, $g = i$ and $y = z$.

If $n = 0$, then $[f, g]$ and $[h, i]$ are the identity, and we directly have $y = z$. The Reedy category $\Delta[B]$ is then elegant.

**Definition 3.1.1.5.** We define the simplicial set $E^{\cong}$ as the colimit of the diagram:

$$[e, 0] \leftarrow [e, 1] \xrightarrow{[e, d^1 d^3]} [e, 3] \xleftarrow{[e, d^0 d^2]} [e, 1] \to [e, 0].$$

An *elementary anodyne extension* is one of the following:

(1) The *generating Reedy cofibrations*:

$$[a, n] \cup [b, \partial[n]] \to [b, n], \text{ for } a \to b \text{ a generating acyclic cofibration of A.}$$

(2) The *Segal extensions*:

$$[a, 1] \cup [a, 1] \cup \ldots \cup [a, 1] \to [a, n], \text{ for } a \text{ an object of } A \text{ and } n > 0.$$

(3) The *completeness extensions*:

$$\{0\} \to E^{\cong}.$$

**3.1.1.6.** A *Segal A-category* is a Segal $A$-precategory having the right lifting property against all elementary anodyne extensions.

Let $C$ be a Segal $A$-categories. We define the presheaf $ho(C) : \Delta^{op} \to \mathbf{Set}$ sending $[n]$ to $\mathrm{Hom}_{ho(A)}(e, C_n)$. As explained in [Sim11, § 14.5], this simplicial set has the unique right lifting property against Segal's maps, and is then the nerve of a category that we also note by $ho(C)$. An arrow $x : [e, 1] \to C$ is an *isomorphism* if its image in $ho(C)$ is.

117

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

We can give an other characterization of isomorphisms in Segal A-categories. An arrow  \( x : [e, 1] \to C \)  is an isomorphism if and only if there exists a lifting in the following diagram:

![img-82.jpeg](img-82.jpeg)

A morphism  \( f : C \to D \)  between Segal A-categories is an equivalence of Segal A-categories if  \( C_{1} \to D_{1} \)  is a weak equivalence in A, and for any element  \( x \in ob(D) \) , there exists  \( y \in ob(C) \)  and an isomorphism in D between  \( f(y) \)  and x.

Theorem 3.1.1.7 ([Sim11, 21.2.1]). There exists a nice model structure on \(\operatorname{Seg}(A)\) where fibrant objects are Segal \(A\)-categories and weak equivalences between Segal \(A\)-categories are equivalences of Segal \(A\)-categories.

A left adjoint from  \( \operatorname{Seg}(A) \)  to a model category C is a left Quillen functor if it preserves cofibrations, and sends elementary anodyne extensions to weak equivalences.

Proposition 3.1.1.8. Any Segal A-precategory is a homotopy colimit of objects of shape  \( [a, n] \) .

Proof. Let \( C \) be a Segal \( A \)-precategory. We have \( C \cong \operatorname{colim}_{\Delta[tB]_C -} \). The result then follows from propositions 1.1.2.6, 2.1.2.3 and 3.1.1.4.

#### 3.1.2 Stratified Segal A-precategories

3.1.2.1. A stratified Segal \(A\)-precatagory is a pair \((C, tC)\) where \(tC\) is a subset of \(ob(C_1)\) that factors \(s^0: C_0 \to ob(C_1)\). A morphism of stratified Segal \(A\)-precatagory \((C, tC) \to (D, tD)\) is the data of a morphism \(f: C \to D\) such that \(f(tC) \subset tD\). The category of stratified Segal \(A\)-precategories is denoted by \(\mathrm{tSeg}(A)\).

We have an adjunction

\[
(\_) ^ {\flat}: \operatorname{Seg} (A) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tSeg} (A): (\_) ^ {\natural} \tag {3.1.2.2}
\]

where the left adjoint is a fully faithful inclusion that sends C to  \( C^{\flat} := (C, Im(s^{0})) \) . The right adjoint is the obvious forgetful functor. We will identify Segal A-precategories with their images in stratified Segal A-precategories under the left adjoint.

3.1.2.3. We define  \( [e,1]_{t} := ([e,1], [e,1]_{1}) \) . The subcategory of objects of shape  \( [a,n] \)  or  \( [e,1]_{t} \)  is then dense in  \( \operatorname{tSeg}(A) \) .

Let \( B \) be the Reedy category and \( M \) the subset of objects of \( B \) such that \( A \) is the category of \( M \)-stratified presheaves on \( B \). We recall that we defined the category \( \Delta[B] \)

118

3.1. PRELIMINARIES

and the set of morphism $\Delta[M]$ in paragraph 3.1.1.3. We set $t\Delta[M]$ as the reunion of $\Delta[M]$ and the singleton $\{[e, 1]_t\}$. We can easily check that the category $\text{tSeg}(A)$ is the category of $t\Delta[M]$-stratified presheaves on $\Delta[B]$. The set of generating cofibrations for $\text{tSeg}(A)$ then consists of morphisms of shape $[e, 1] \rightarrow [e, 1]_t$ or $[a, n] \cup [b, \partial n] \rightarrow [b, n]$ where $a \rightarrow b$ is a generating cofibration of $A$. For any stratified Segal $A$-precategory $C$, we then have an isomorphism

$$C \cong \operatorname{colim}_{t\Delta[tB]/C} \neg$$

where $t\Delta[tB]$ is the full subcategory of $\text{tSeg}(A)$ whose objects are of in $\Delta[B]$ or $t\Delta[M]$.

Following the definition of section 2.1.2, a morphism between stratified Segal precategories is *entire* if it is the identity on the underlying $\Delta[B]$-presheaves.

**3.1.2.4.** A *marked Segal $A$-category* is a pair $(C, C^{\cong})$ where $C$ is a Segal $A$-category and $C^{\cong}$ is the subset of $ob(C_1)$ consisting of all isomorphisms. A morphism $f : (C, C^{\cong}) \rightarrow (D, D^{\cong})$ between marked Segal $A$-categories is an *equivalence of marked Segal $A$-categories* if $C_1 \rightarrow D_1$ is a weak equivalence in $A$, and for any element $x \in ob(D)$, there exists $y \in ob(C)$ and $v : f(y) \rightarrow x \in D^{\cong}$.

**3.1.2.5.** We are now willing to endow $\text{tSeg}(A)$ with a nice model structure whose fibrant objects are marked Segal $A$-category and weak equivalences between fibrant objects are equivalences of marked Segal $A$-categories. We define the stratified Segal $A$-precategories $(E^{\cong})'$ as the following pushout:

$$\begin{array}{ccc} [e, 1] & \xrightarrow{d^0 d^3} & E^{\cong} \\ \downarrow & & \downarrow \\ [e, 1]_t & \longrightarrow & (E^{\cong})' \end{array}$$

We define the set of map $J$ as the reunion of the set of generating acyclic cofibration of $\text{Seg}(A)$ and of $\{[e, 1]_t \rightarrow (E^{\cong})'\}$ and $\{E^{\cong} \rightarrow (E^{\cong})'\}$. We suppose furthermore that $J$ includes the acyclic cofibrations $\{0\} \rightarrow E^{\cong}$ and $\{1\} \rightarrow E^{\cong}$.

**Lemma 3.1.2.6.** A morphism $f$ has the right lifting property against $J$ if and only if $f^{\cong}$ is a fibration and $f$ has the right lifting property against $[e, 1]_t \rightarrow (E^{\cong})'$ and $E^{\cong} \rightarrow (E^{\cong})'$. An object $X$ has the right lifting property against $J$ if and only if it is a marked Segal $A$-category.

*Proof.* Straightforward. $\square$

119

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Lemma 3.1.2.7. Let \( i: K \to L \) be a cofibration that induces an isomorphism on objects. The morphism

\[
K \times E ^ {\cong} \coprod_ {K \times [ e, 1 ]} L \times [ e, 1 ] \to L \times E ^ {\cong}
\]

is an acyclic cofibration of the model strucure on \(\operatorname{Seg}(A)\).

Proof. By two out of three, and some diagram chasing, is it sufficient to demonstrate the result for \( K \) being \( L_0 \). We then have to show that the square

![img-83.jpeg](img-83.jpeg)

is homotopy coccartesian. As the model structure is cartesian, and as \( E^{\cong} \to 1 \) is a weak equivalence, this is sufficient to show that the following square is homotopy cocartesian:

![img-84.jpeg](img-84.jpeg)

As \(\_ \times [e,1]\) and \(\_ \times E^{\cong}\) are left Quillen functors, we can reduce to the case where \(L\) is \([a,n]\) and using Segal extension, to the case where \(L\) is \([a,1]\). We then have to show that the following square is homotopy cocartesian

![img-85.jpeg](img-85.jpeg)

Remark then that  \( [a,1]\times[e,1] \)  is the colimit of the following span:

\[
[ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ]
\]

The pushout of the span of (3.1.2.8) is then the (homotopy) colimit of

\[
[ 0 ] \coprod_ {[ e, 1 ]} [ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ] \coprod_ {[ e, 1 ]} [ 0 ]
\]

By two out of three, and using Segal extensions, the two morphisms

\[
[ 0 ] \coprod_ {[ e, 1 ]} [ e, 1 ] \vee [ a, 1 ] \to [ a, 1 ] \qquad \text {and} \qquad [ a, 1 ] \vee [ e, 1 ] \coprod_ {[ e, 1 ]} [ 0 ] \to [ a, 1 ]
\]

120

3.1. PRELIMINARIES

induced by $[a, d^0]$ and $[a, d^2]$ are weak equivalences. In particular, this implies that the canonical morphism from the pushout of the span of (3.1.2.8) to $[a, 1]$ is a weak equivalence. As the upper horizontal vertical morphisms of (3.1.2.8) is a cofibration, this implies that this square is homotopy cocartesian which concludes the proof. □

**Lemma 3.1.2.9.** *Let $i: K \to L$ be a monomorphism and $f: X \to Y$ a morphism having the right lifting property against $J$. The induced morphism*

$$f^i: X^L \to X^K \times_{Y^K} Y^L$$

*has the right lifting property against $J$.*

*Proof.* As the model structure on $\operatorname{Seg}(A)$ is cartesian, $(f^i)^\natural$ is a fibration. We then have to show that this morphism has the right lifting property against $[e, 1]_t \to (E^\cong)'$ and $E^\cong \to (E^\cong)'$. We can reduce to the case where $i$ is a generating acyclic cofibration. If $i$ is $\emptyset \to [0]$, this is obvious. We then suppose that $i$ is $[e, 1] \to [e, 1]_t$ or $[a, \partial n] \cup [b, n] \to [b, n]$ for $a \to b$ a generating acyclic cofibration of $A$. In both case, $i$ induces an equivalence on objects. The morphism $i \hat{\times} (E^\cong \to (E^\cong)')$ is then the identity. Moreover, $i \hat{\times} ([e, 1]_t \to (E^\cong)')$ fits in the following cocartesian square

$$\begin{array}{ccc} L^\natural \times [e, 1] \coprod_{K^\natural \times [e, 1]} K^\natural \times (E^\cong) & \longrightarrow & L \times [e, 1]_t \coprod_{K \times [e, 1]_t} K \times (E^\cong)' \\ \downarrow & & \downarrow \\ L^\natural \times E^\cong & \longrightarrow & L \times (E^\cong)' \end{array}$$

The lemma 3.1.2.7 implies $f$ has the right lifting property against the left vertical morphism, and so also against the right vertical one. By adjunction, this implies that $f^i$ has the desired lifting property. □

**Proposition 3.1.2.10.** *There exists a nice model structure on $\operatorname{tSeg}(A)$ where fibrant objects are stratified Segal $A$-categories and weak equivalences between marked Segal $A$-categories are stratified equivalences. The adjunction*

$$(\_)^\flat: \operatorname{Seg}(A) \xrightarrow{\perp} \operatorname{tSeg}(A): (\_)^\natural$$

*induces a Quillen equivalence.*

*A left adjoint from $\operatorname{tSeg}(A)$ to a model category $C$ is a left Quillen functor if it preserves cofibrations, and sends elementary anodyne extensions and morphisms $[e, 1]_t \to 1$, $E^\cong \to (E^\cong)'$ to weak equivalences.*

*Proof.* We recall that we define $J$ as the reunion of the set of generating acyclic cofibrations of $\operatorname{Seg}(A)$ and of $\{[e, 1]_t \to (E^\cong)'\}$ and $\{E^\cong \to (E^\cong)'\}$ and we suppose that it includes

121

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

the trivial cofibrations \(\{0\} \to E^{\cong}\) and \(\{1\} \to E^{\cong}\). We denote \(I\) a cellular model for \(\mathrm{Psh}(t\Delta[tB])\).

As \(\mathrm{tSeg}(A)\) is the category of \(t\Delta [M]\) stratified presheaves on \(\Delta [B]\), we have an adjunction

\[
\pi : \mathrm{Psh} (t \Delta [ t B ]) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tSeg} (A): \iota
\]

where the right adjoint is fully faithfull.

The set \( l(r(\iota(\mathrm{J})\hat{\times}I)) \) is a class of anodyne extension relative to the interval \( _- \times E^{\cong} \) as defined in [Cis06, paragraph 1.3.12]. We then consider \( \mathrm{Psh}(t\Delta[tB]) \) endowed with the model structure induced by [Cis06, théorème 1.3.22]. An object is fibrant if and only if it has the right lifting property against \( \iota(\mathrm{J})\hat{\times}I \). A morphism between fibrant objects is a fibration if and only if it has the right lifting property against \( \iota(\mathrm{J})\hat{\times}I \).

According to proposition 2.1.2.6, this induces a model structure on  \( \operatorname{tSeg}(A) \) . By adjunction and using lemma 3.1.2.9, an object is fibrant if and only if it has the right lifting property against J and a morphism between fibrant objects is a fibration if and only if it has the right lifting property against J. According to lemma 3.1.2.6, the fibrant objects correspond to marked Segal A-categories.

The theorem 3.1.1.7 implies that the adjunction (3.1.2.2) is a Quillen adjunction. It's unit is the identity, and lemma 3.1.2.6 implies that the counit, computed on a fibrant object \((C,C^{\cong})\), is the canonical inclusion \((C,C^{\flat})\to (C,C^{\cong})\). As this morphism is a transfinite composite of \(E^{\cong}\rightarrow (E^{\cong})'\), it is a weak equivalence. The Quillen pair 3.1.2.6 is then a Quillen equivalence. As a consequence, the model structure on \(\mathrm{tSeg}(A)\) is cartesian and simplicial, and weak equivalences between fibrant objects are stratified equivalences.

It then remains to prove the last assertion. Suppose given a left adjoint \( F: \mathrm{tSeg}(A) \to C \) that preserves cofibrations, and sends elementary anodyne extensions and morphisms \( [e,1]_t \to 1 \), \( E^{\cong} \to (E^{\cong})' \) to weak equivalences. The theorem 3.1.1.7 implies that the restriction of \( F \) to \( \operatorname{Seg}(A) \) is a left Quillen functor, and this functors then sends any acyclic cofibration of \( \operatorname{Seg}(A) \) to a weak equivalence. As we have a commutative diagram,

![img-86.jpeg](img-86.jpeg)

we deduce by two out of three that \( F \) sends \( [1]_t \to (E^{\cong})' \) to a weak equivalence. The functor \( F \) then sends any morphism of \( J \) to a weak equivalence.

As fibrant objects and fibrations between fibrant objects are detected by right lifting property against J, the right adjoint of F preserves them. The corollary A.2 of [Dug01] implies that F is a left Quillen functor. □

122

3.1. PRELIMINARIES

**Proposition 3.1.2.11.** *Any stratified Segal A-precategory is a homotopy colimit of objects of shape $[a, n]$ or $[e, 1]_t$.*

*Proof.* Let $C$ be a stratified Segal $A$-precategory. We have $C \cong \operatorname{colim}_{t\Delta[tB]/C} \_$. The result then follows from propositions 1.1.2.6, 2.1.2.3 and 3.1.1.4. $\square$

**3.1.2.12.** We now present the main way of constructing functors whose codomain is $\operatorname{tSeg}(A)$.

**Construction 3.1.2.13.** Suppose given a colimit preserving functor $G : A \times \Delta \to D$ in a complete category, an object $G(e, 1)'$ and a morphism $p : G(e, 1) \to G(e, 1)'$ such that for any object $d$ of $D$, $\operatorname{Hom}(p, d)$ is a monomorphism. We define the functor $\overline{G} : \operatorname{tSeg}(A) \to D$ as the unique colimit preserving functor such that $\overline{G}([e, 1]_t) := G(e, 1)'$ and for any $a, n$, $\overline{G}([a, n])$ fits in the following cocartesian square:

$$
\begin{array}{ccc}
\coprod_{i \in [n]} G(a, \{i\}) & \longrightarrow & G(a, [n]) \\
\downarrow & & \downarrow \\
\coprod_{i \in [n]} G(e, \{i\}) & \longrightarrow & \overline{G}([a, n])
\end{array}
$$

Remark that if the top horizontal morphism is a cofibration, the previous square is homotopy cocartesian.

**3.1.2.14.** In this model structure, the morphism $[e, 1]_t \to 1$ is a weak equivalence. For any $a \in A$ and $n \in \mathbb{N}$, we define $[e, 1]_t \vee [a, n]$ as the pushout:

$$
\begin{array}{ccc}
[e, 1] & \longrightarrow & [e, 1] \vee [a, n] \\
\downarrow & & \downarrow \\
[e, 1]_t & \longrightarrow & [e, 1]_t \vee [a, n]
\end{array}
$$

The canonical morphism $[e, 1]_t \cup [a, 1] \cup \ldots \cup [a, 1] \to [e, 1]_t \vee [a, n]$ is then a weak equivalence. By two out of three, and using the weak equivalence $[e, 1]_t \to 1$, this implies that $[e, 1]_t \vee [a, n] \to [a, n]$ is a weak equivalence.

We define similarly the object $[a, n] \vee [e, 1]_t$ that comes along with a weak equivalence $[a, n] \vee [e, 1]_t \to [a, n]$.

### 3.1.3 Gray module

**3.1.3.1.** Let $A$ be a category of stratified presheaves on an elegant Reedy category (as defined in paragraph 1.1.2.5 and section 2.1.2), endowed with a nice model structure

123

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

(as defined in paragraph 2.1.1.8). We suppose furthermore that the terminal element of \( A \), denoted by \( e \), is representable. We also suppose that \( A \) is endowed with intelligent \( n \)-truncation for any \( n \in \mathbb{N} \cup \{\omega\} \), i.e a family of left Quillen functors \( \tau_{-}^{i}: (\mathbb{N} \cup \{\omega\})^{op} \to \operatorname{End}(A) \) such that

- \(\tau_{\omega}^{i} = id,\)
- for any \(n \leq m\), \(\tau_{n}^{i}\tau_{m}^{i} = \tau_{n}^{i}\),
- for any \(n \leq m\), the natural transformation \(\tau_{m}^{i} \to \tau_{n}^{i}\) is an entire monomorphism,

and a left Quillen bifunctor \(\_ \otimes \_ : \mathrm{tPsh}(\Delta)^1 \times A \to A\) such that

- for \( K \) and \( L \) two stratified simplicial sets, and \( a \in A \), there is a morphism \( K \otimes (L \otimes a) \to (K \times L) \otimes a \) natural in \( K, L \) and \( a \), such that the following square commutes

![img-87.jpeg](img-87.jpeg)

for any stratified simplicial sets \(M\).

- The functor \([0] \otimes \_ : A \to A\) is the identity.
- For any integer \( n \), for any object \( a \) invariant under \( \tau_n^i \), and for any stratified simplicial set \( K \), the object \( K \otimes a \) is invariant under \( \tau_{n+1}^i \).

Here, the model category  \( \mathrm{tPsh}(\Delta)^{1} \)  corresponds to the model structure for 1-complicial sets on stratified simplicial sets given in theorem 2.2.1.6.

##### 3.1.3.2. We define \( e \star a \) as the pushout:

![img-88.jpeg](img-88.jpeg)

We consider the natural transformations  \( s^{0} \star a : e \star e \star a \to e \star a \)  and  \( d^{0} \star a : a \to e \star a \) , induced respectively by the morphism

\[
\begin{array}{l} [ 1 ] \otimes [ 1 ] \otimes a \rightarrow ([ 1 ] \times [ 1 ]) \otimes a \rightarrow [ 1 ] \otimes a \\ (\{i \} \times \{j \}) \otimes a \mapsto \{i \wedge j \} \otimes a. \\ \end{array}
\]

and the morphism

\[
\{1 \} \otimes a \rightarrow [ 1 ] \otimes a.
\]

124

3.1. PRELIMINARIES

These natural transformations induce commutative diagrams:

![img-89.jpeg](img-89.jpeg)

![img-90.jpeg](img-90.jpeg)

The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of $A$ and the natural transformation $s^0 : e \star e \star \_ \to e \star \_$ defines a structure of monoid for $e \star \_$ . This induces a functor $\Delta \times A \to A$ sending $([n], a)$ to $e \star e \star \ldots \star a$. We extend this to a functor $\Delta_t \times A \to A$ in defining $[n]_t \star a$ as the pushout:

![img-91.jpeg](img-91.jpeg)

where $\tau_{-1}^{i}$ is the constant functor with value $\emptyset$.

3.1.3.3. Such model category $A$ is a Gray module if for any $a$, the induced functor $\_ \star a : \Delta_t \to A_{a/}$ lifts to a left Quillen functor $\_ \star a : \mathrm{tPsh}(\Delta)^\omega \to A_{a/}$.

We recall that $\mathrm{tPsh}(\Delta)^\omega$ denotes the model structure for $\omega$-complicial sets given in theorem 2.2.1.6.

For the rest of this chapter, we fix a Gray module $A$. For a stratified simplicial set $K \in \mathrm{tPsh}(\Delta)$, the object $K \star \emptyset \in A$ is simply noted by $K$.

Remark 3.1.3.4. In general, $[n] \otimes e$ and $[n] \star \emptyset$ are two very different objects. Indeed $[n] \otimes e$ has to be invariant up to homotopy under $\tau_1^i$ which is not the case for $[n] \star \emptyset$. Analogously $[k] \otimes ([l] \otimes [a])$ and $([k] \otimes [l]) \otimes [a]$ have a priori no links. When we write $[n_0] \otimes [n_1] \otimes ..[n_k] \otimes a$, we will always mean $[n_0] \otimes ([n_1] \otimes ..([n_k] \otimes a))$.

Example 3.1.3.5. For any $d \in \mathbb{N} \cup \{\omega\}$, the model category $\mathrm{tPsh}(\Delta)^d$, corresponding to the model structure for $d$-complicial sets on stratified simplicial sets, and where $K \otimes L := \tau_1^i(K) \boxtimes L$, is an example of Gray module.

Indeed, if $n$ is any integer, we define $[n]^\diamond := [0] \diamond [0] \diamond \ldots \diamond [0]$ and $[n]_t^\diamond := \tau_n^i([n]^\diamond)$. This induces a colimit preserving functor $K \mapsto K^\diamond$. The join coming from $\tau_1^i(\_) \boxtimes \_$ then corresponds to the functor $(K, L) \mapsto K^\diamond \diamond L$. The proposition 2.2.2.15 provides a natural transformation $K^\diamond \diamond L \to K \star L$, wich implies that the first functor is left Quillen.

125

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

### 3.2 Gray constructions for stratified Segal A-categories

We now construct a Gray cylinder and a Gray cone on  \( \operatorname{tSeg}(A) \) , using the structure of Gray module that A has. We denote by  \( \Delta_{+} \) the augmented simplex category and  \( d^{0} \)  the unique morphism  \( \emptyset \to [0] \) .

#### 3.2.1 Gray cylinder

##### 3.2.1.1. We define the functor

\[
\Delta^ {3} \times A \quad \rightarrow \operatorname{Seg} (A)
\]

\[
[ n _ {0} ], [ n _ {1} ], [ n _ {2} ], a \mapsto [ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ]
\]

where \([a, n_0] \vee [[n_1] \otimes a, 1] \vee [a, n_2]\) fits in the following pushout:

![img-92.jpeg](img-92.jpeg)

If \(n\) is an integer, \(\Delta_{/[n]}^{3}\) is the pullback:

![img-93.jpeg](img-93.jpeg)

where the right hand functor sends \(\left([n_0],[n_1],[n_2]\right)\) to \([n_0]\star [n_1]^{op}\star [n_2]\).

Proposition 3.2.1.2. The category \(\Delta_{/[n]}^{3}\) is an elegant Reedy category.

Proof. We denote \(X\) the trisimplicial set whose value on \([n_0], [n_1], [n_2]\) is \(\mathrm{Hom}_{\Delta}([n_0] \star [n_1]^{op} \star [n_2], [n])\). The category \(\Delta_{/[n]}^3\) fits in the pullback

![img-94.jpeg](img-94.jpeg)

and is then an elegant Reedy category according to proposition 1.1.2.6.

□

126

3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

##### 3.2.1.3. We define the functor

\[
A \times \Delta \rightarrow \operatorname{Seg} (A)
\]

\[
[ n ], a \mapsto F (a, n)
\]

by the formula \( F(a, n) := \underset{\Delta_{\gamma[n]}^3}{\text{colim}} [a, n_0] \vee [[n_1] \otimes a, 1] \vee [a, n_2] \).

In order to extend this functor to stratified Segal \(A\)-precategories with construction 3.1.2.13, we will need to define the value on \([e,1]_t\), i.e. to choose an object \(F(e,1)'\) and an entire cofibration \(F(e,1) \to F(e,1)'\). It will be useful to have a more explicit description of this object.

Example 3.2.1.4. The sub-category of \(\Delta_{\gamma[1]}^3\) composed of non degenerate objects can be pictured by the graph:

![img-95.jpeg](img-95.jpeg)

The Segal A-precategory  \( F(e,1) \)  is then the colimit of the following diagram:

\[
[ e, 2 ] \xleftarrow {[ e , d ^ {1} ]} [ e, 1 ] \xrightarrow {[ d ^ {0} , 1 ]} [ [ 1 ], 1 ] \xleftarrow {[ d ^ {1} , 1 ]} [ e, 1 ] \xrightarrow {[ e , d ^ {1} ]} [ e, 2 ]
\]

##### 3.2.1.5. We define the functor

\[
I \otimes \_ : \mathrm{tSeg} (A) \to \mathrm{tSeg} (A)
\]

induced, as in the construction 3.1.2.13, by \( F \) and with \( F(e,1)' \) as the colimit of the following diagram:

\[
[ e, 1 ] _ {t} \longleftarrow [ e, 1 ] \stackrel {[ e, d ^ {2} ]} {\longrightarrow} [ e, 2 ] \stackrel {[ e, d ^ {1} ]} {\longleftarrow} [ e, 1 ] \stackrel {[ d ^ {0}, 1 ]} {\longrightarrow} [ [ 1 ] _ {t}, 1 ] \stackrel {[ d ^ {1}, 1 ]} {\longleftarrow} [ e, 1 ] \stackrel {[ e, d ^ {1} ]} {\longrightarrow} [ e, 2 ] \stackrel {[ e, d ^ {0} ]} {\longleftarrow} [ e, 1 ] \longrightarrow [ e, 1 ] _ {t}
\]

The two objects of \(\Delta_{[n]}^3\), \(s^n s^{n+1} : [n] \star [0]^{op} \star [0] \to [n]\) and \(s^0 s^0 : [0] \star [0]^{op} \star [n] \to [n]\), induce two morphisms: \(d^1 \otimes [a, n] : \{0\} \otimes [a, n] := [a, n] \hookrightarrow [a, n] \vee [e, 1] \to I \otimes [a, n]\) and \(d^0 \otimes [a, n] : \{1\} \otimes [a, n] := [a, n] \hookrightarrow [e, 1] \vee [a, n] \to I \otimes [a, n]\). By extending them by colimits we get two maps

\[
d ^ {1} \otimes C: \{0 \} \otimes C := C \to I \otimes C \quad \text { and } \quad d ^ {0} \otimes C: \{1 \} \otimes C := C \to I \otimes C.
\]

127

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proposition 3.2.1.6. The Segal \(A\)-precategory \(I \otimes [a,1]\) is the colimit and the homotopy colimit of the diagram:

\[
[ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ e , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ d ^ {0} , 1 ]} [ [ 1 ] \otimes a, 1 ] \xleftarrow {[ d ^ {1} , 1 ]} [ a, 1 ] \xrightarrow {[ e , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ]
\]

Proof. The description of \(\Delta_{[1]}^{3}\) is given in the example 3.2.1.4. The stratified Segal \(A\)-precategory \(F(a,1)\) is then the colimit of the following diagram:

\[
[ a, 2 ] \xleftarrow {[ e , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ d ^ {0} , 1 ]} [ [ 1 ] \otimes a, 1 ] \xleftarrow {[ d ^ {1} , 1 ]} [ a, 1 ] \xrightarrow {[ e , d ^ {1} ]} [ a, 2 ]
\]

and the Segal \(A\)-precategory \(I \otimes [a,1]\) is the colimit of the given diagram. As all the morphisms are cofibrations, this colimit is a homotopy colimit.

Remark 3.2.1.7. To justify why this definition of the Gray interval is the good one, let's study the case of \((0,\omega)\)-categories. We denote by \(I\) the \((0,\omega)\)-category generated by the graph \(0\to 1\). If \(C\) is an \((0,\omega)\)-category, we denote by \([C,1]\) the \((0,\omega)\)-category with two objects - denoted by 0 and 1 - and verifying:

\[
\operatorname{Hom} _ {[ C, 1 ]} (0, 1) := C, \quad \operatorname{Hom} _ {[ C, 1 ]} (1, 0) := \emptyset , \quad \operatorname{Hom} _ {[ C, 1 ]} (0, 0) = \operatorname{Hom} _ {[ C, 1 ]} (1, 1) := \{i d \}.
\]

We denote by \( e \) the terminal \( (0, \omega) \)-category. For example \( [e, 1] = I \). Applying the duality \( (\_)^{op} \) to the formula given in theorem 1.2.3.13, the \( (0, \omega) \)-category \( I \otimes [C, 1] \) is the colimit of the following diagram:

\[
[ e, 1 ] \vee [ C, 1 ] \xleftarrow {\nabla} [ C, 1 ] \xrightarrow {[ d ^ {0} \otimes C , 1 ]} [ [ 1 ] \otimes C, 1 ] \xleftarrow {[ d ^ {1} \otimes C , 1 ]} [ C, 1 ] \xrightarrow {\nabla} [ C, 1 ] \vee [ e, 1 ]
\]

where  \( \nabla \)  denotes the whiskerings.

#### 3.2.2 Gray cone

3.2.2.1. We define the functor

\[
\begin{array}{l} \Delta^ {2} \times A \quad \rightarrow \quad \operatorname{Seg} (A) \\ [ n _ {0} ], [ n _ {1} ], a \mapsto [ [ n _ {0} ] \otimes a, 1 ] \vee [ a, n _ {1} ] \\ \end{array}
\]

where \(\left[\left[n_{0}\right]\otimes a,1\right]\vee\left[a,n_{1}\right]\) fits in the following pushouts:

\[
\begin{array}{c} \left[ \left[ n _ {0} \right] \otimes a, n _ {1} \right] \longrightarrow \left[ \left[ n _ {0} \right] \otimes a, 1 + n _ {1} \right] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ a, n _ {1} ] \longrightarrow \left[ \left[ n _ {0} \right] \otimes a, 1 \right] \vee [ a, n _ {1} ] \end{array}
\]

128

3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

If $n$ is an integer, $\Delta_{/[n]}^2$ is the pullback:

![img-96.jpeg](img-96.jpeg)

where the right hand functor sends $([n_0], [n_1])$ to $[n_0]^{op} \star [n_1]$.

**Proposition 3.2.2.2.** *The category $\Delta_{/[n]}^2$ is an elegant Reedy category.*

*Proof.* The proof is analogue to the one of proposition 3.2.1.2.

### 3.2.2.3. We define the functor

$$A \times \Delta \rightarrow \operatorname{Seg}(A)$$

$$[n], a \mapsto H(a, n)$$

by the formula $H(a, n) := \operatorname{colim}_{\Delta_{/[n]}^2} [[n_0] \otimes a, 1] \vee [a, n_1]$.

In order to extend this functor to stratified Segal $A$-precategories with construction 3.1.2.13, we will need to define the value on $[e, 1]_t$, i.e. to choose an object $H(e, 1)'$ and an entire cofibration $H(e, 1) \to H(e, 1)'$. It will be useful to have a more explicit description of this object.

**Example 3.2.2.4.** The sub-category of $\Delta_{/[1]}^2$ composed of non degenerate objects can be pictured by the graph:

![img-97.jpeg](img-97.jpeg)

The Segal $A$-precategory $H(e, 1)$ is then the colimit of the following diagram:

$$[e, 2] \xleftarrow{[e, d^1]} [e, 1] \xrightarrow{[d^0, 1]} [[1], 1]$$

### 3.2.2.5. We define the functor

$$e \star \_ : \operatorname{tSeg}(A) \to \operatorname{tSeg}(A)$$

129

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

induced, as in the construction 3.1.2.13 by \( H \) and with \( H(e,1)' \) as the colimit of the following diagram:

\[
[ e, 1 ] _ {t} \longleftarrow [ e, 1 ] \xrightarrow {[ e , d ^ {0} ]} [ e, 2 ] \xleftarrow {[ e , d ^ {1} ]} [ e, 1 ] \xrightarrow {[ d ^ {0} , 1 ]} [ [ 1 ] _ {t}, 1 ]
\]

The object  \( s^{0}:[0]^{op}\star[n]\to[n] \)  induces a composite morphism  \( d^{0}\star[a,n]:\emptyset\star[a,n]:=[a,n]\hookrightarrow[1,1]\vee[a,n]\to e\star[a,n] \) , which induces by extension by colimit a natural transformation

\[
d ^ {0} \star C: \emptyset \star C := C \to e \star C.
\]

Proposition 3.2.2.6. The Segal A-precategory  \( e \star [a,1] \)  is the colimit and the homotopy colimit of the following diagram:

\[
[ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ e , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ]
\]

Proof. We have already given the description of \(\Delta_{/[1]}^2\) in the example 3.2.2.4. The Segal \(A\)-precategory \(H(a,1)\) is the colimit of the following diagram:

\[
[ a, 2 ] \xleftarrow {[ e , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ d ^ {0} \otimes a , 1 ]} [ [ 1 ] \otimes a, 1 ]
\]

and  \( e \star [a,1] \)  is the colimit of the given diagram. As all the morphisms are cofibrations, this colimit is a homotopy colimit. ☐

Remark 3.2.2.7. Using again notations of remark 3.2.1.7, if C is an  \( (0,\omega) \) -category, the  \( (0,\omega) \) -category  \( e\star C \)  is the colimit of the following diagram:

\[
[ e, 1 ] \vee [ C, 1 ] \xleftarrow {\nabla} [ C, 1 ] \xrightarrow {[ d ^ {0} \star C , 1 ]} [ e \star C, 1 ]
\]

where  \( \nabla \)  is the whiskering. Our definition of the join is therefore analogous to that of the strict world.

Proposition 3.2.2.8. The Segal A-precategory  \( [1] \star [a,1] \)  is the colimit of the following diagram:

![img-98.jpeg](img-98.jpeg)

130

3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

where \([2] \bar{\otimes} a\) and \([(1), 1] \vee [a, 1]\) are the pushouts:

\[
\begin{array}{c} [ 1 ] \otimes a \amalg [ 1 ] \otimes a \xrightarrow {d ^ {1} \otimes a \amalg d ^ {2} \otimes a} [ 2 ] \otimes a \\ \Big \downarrow \\ e \star a \amalg e \star a \xrightarrow [ d ^ {1} \bar {\otimes} a \amalg d ^ {2} \bar {\otimes} a ]{} [ 2 ] \bar {\otimes} a \end{array}
\]

\[
\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \amalg [ [ 1 ] \otimes a, 2 ] \xrightarrow {[ [ 1 ] \otimes a , d ^ {2} \amalg d ^ {1} ]} [ [ 1 ] \otimes a, 2 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ [ 1 ], 1 ] \amalg [ a, 1 ] \xrightarrow {} [ [ 1 ], 1 ] \vee [ a, 1 ] \end{array}
\]

Proof. Let's start by studying the object \( H(a,2) \). Here is a final subcategory of \( \Delta_{/[2]}^2 \):

\[
\begin{array}{c} [ 1 ] ^ {o p} \star [ 0 ] \xrightarrow {d ^ {2}} [ 1 ] ^ {o p} \star [ 1 ] \xleftarrow {d ^ {1}} [ 0 ] ^ {o p} \star [ 1 ] \\ d ^ {2} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ 2 ] ^ {o p} \star [ 0 ] \xrightarrow [ s ^ {2} ]{} [ 2 ] \xleftarrow [ s ^ {0} ]{} [ 0 ] ^ {o p} \star [ 2 ] \end{array}
\]

The Segal \(A\)-precategory \(H(a,2)\) is then the colimit of the following diagram:

\[
[ [ 2 ] \otimes a, 1 ] \stackrel {[ d ^ {0} \otimes a, 1 ]} {\longleftrightarrow} [ [ 1 ] \otimes a, 1 ] \stackrel {[ [ 1 ] \otimes a, d ^ {1} ]} {\longrightarrow} [ [ 1 ] \otimes a, 1 ] \vee [ a, 1 ] \stackrel {[ d ^ {0} \otimes a, 2 ]} {\longleftrightarrow} [ a, 2 ] \stackrel {[ a, d ^ {1} ]} {\longrightarrow} [ a, 3 ]
\]

The Segal \(A\)-precategory \(e \star ([e, 1] \vee [a, 1])\) is then the colimit of the following diagram:

\[
[ [ 2 ] \bar {\otimes} a, 1 ] \stackrel {[ d ^ {0} \otimes a, 1 ]} {\longleftrightarrow} [ [ 1 ] \otimes a, 1 ] \stackrel {[ [ 1 ] \otimes a, d ^ {1} ]} {\longrightarrow} [ [ 1 ], 1 ] \vee [ a, 1 ] \stackrel {[ d ^ {0} \otimes a, 2 ]} {\longleftrightarrow} [ e, 1 ] \vee [ a, 1 ] \stackrel {[ a, d ^ {1} ]} {\longrightarrow} [ e, 2 ] \vee [ a, 1 ]
\]

The fact that \([1] \star [a, 1]\) is the colimit of the given diagram then follows from the equality \([1] \star [a, 1] = e \star (e \star [a, 1])\) and from the explicit expression of \(e \star [a, 1]\) given in proposition 3.2.2.6.

#### 3.2.3 Link between the Gray cylinder and Gray cone

3.2.3.1. There is a canonical morphism \( I \otimes [a, n] \to e \star [a, n] \) sending \( [a, n_0] \vee [[n_1] \otimes a, 1] \vee [a, n_2] \) to \( [[n_1] \otimes a, 1] \vee [a, n_2] \). Note that the induced morphism \( I \otimes [e, 1] \to e \star [e, 1] \to e \star [e, 1]_t \) factors through \( I \otimes [e, 1]_t \). We can then extend it by colimit to a natural transformation \( I \otimes C \to e \star C \).

We now define \((I\otimes [a,n])_{/\{0\} \otimes [a,n]}\) and \([a,n_0]\vee [[n_1]\otimes a,1]\vee [a,n_2]_{/[a,n_0]}\) as the pushouts:

\[
\begin{array}{c} [ a, n ] \otimes \{0 \} \longrightarrow I \otimes [ a, n ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow (I \otimes [ a, n ]) _ {/ \{0 \} \otimes [ a, n ]} \end{array}
\]

\[
\begin{array}{c} [ a, n _ {0} ] \longrightarrow [ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow [ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] _ {/ [ a, n _ {0} ]} \end{array}
\]

By Segal extensions and by two out of three, the following canonical morphism

\[
[ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] _ {/ [ a, n _ {0} ]} \rightarrow [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ]
\]

131

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

is a weak equivalence. As \(\Delta_{/[n]}^{3}\) is Reedy elegant, this induces a weak equivalence

\[
\underset {\Delta_ {[ n ]} ^ {3}} {\operatorname{colim}} [ a, n _ {0} ] \vee [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ] _ {/ [ a, n _ {0} ]} \to \underset {\Delta_ {[ n ]} ^ {3}} {\operatorname{colim}} [ [ n _ {1} ] \otimes a, 1 ] \vee [ a, n _ {2} ].
\]

Remark furthermore that the left hand object is equivalent to  \( (I \otimes [a, n])_{/\{0\} \otimes [a, n]} \)  and the right one to  \( H(a, n) \) . As the construction 3.1.2.13 preserves weakly invertible natural transformations between functors that preserve cofibration, this induces a weakly invertible natural transformation  \( (I \otimes [a, n])_{/\{0\} \otimes [a, n]} \to e \star [a, n] \) . This directly implies that squares

![img-99.jpeg](img-99.jpeg)

![img-100.jpeg](img-100.jpeg)

are homotopy cocartesian. As every stratified Segal \(A\)-precategory is a homotopy colimit of objects of shape \([a, n]\) and \([e, 1]_t\), and as \(I \otimes_{-}\) and \(e \star_{-}\) preserves monomorphisms, this implies the following proposition:

Proposition 3.2.3.2. For any stratified Segal \(A\)-precategory \(C\), the natural transformation \(I \otimes_{-} \to e \star_{-}\) fits into a homotopy cocartesian square:

![img-101.jpeg](img-101.jpeg)

##### 3.2.3.3. We define the functor

\[
A \times \Delta \rightarrow \operatorname{Seg} (A)
\]

\[
[ n ], a \mapsto T (a, n)
\]

by the formula \( T(a, n) := [[n] \otimes a, 1] \).

Eventually we define the functor \(\Sigma^{\circ}[a,n]:\mathrm{tSeg}(A)\to \mathrm{tSeg}(A)\) induced, as in the construction 3.1.2.13, by \(T\) and with \(T(e,1):= [[1]_t\otimes e,1]\). This functor is called the \(\circ\)-suspension. With a proof similar to the on of proposition 3.2.3.2, one can show:

Proposition 3.2.3.4. There exists a natural transformation \( e \star_{-} \to \Sigma^{\circ}(_{-}) \) such that for any marked Segal \( A \)-precategory \( C \), \( e \star C \to \Sigma^{\circ}C \) induces a homotopy cocartesian square:

![img-102.jpeg](img-102.jpeg)

132

3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

### 3.2.4 Gray constructions are left Quillen

In this section, we show that the Gray cylinder is a Quillen functor. Combined with the proposition 3.2.3.2, this will imply that the Gray cone is Quillen.

3.2.4.1. Let $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ be an element of $\Delta^3_{/[n]}$. The degree of $x$, is $f(0) - f(k_1)$ where $f$ is the composite morphism:

$$f : [k_1]^{op} \to [k_0] \star [k_1]^{op} \star [k_2] \to [n]$$

We will denote by $K_{\le i}$ the full subcategory of $\Delta^3_{/[n]}$ whose objects are of degree inferior or equal to $i$.

An element $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ of degree $d$ is regular if $k_1 = d$, $k_0 + k_1 + k_2 = n$ and

$$x(l) := \begin{cases} l & \text{if } l \le k_0 \\ l-1 & \text{if } k_0 < l \le k_0 + k_1 \\ l-2 & \text{if } k_0 + k_1 < l \end{cases}$$

Remark that the regular object $x$ is characterized by the triple $(k_0, k_1, k_2)$.

3.2.4.2. Let $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ be an element $\Delta^3_{/[n]}$, and $i : [0] \to [k_0] \star [k_1]^{op} \star [k_2]$ a morphism. We denote by $d^i x := [k'_0] \star [k'_1]^{op} \star [k'_2] \xrightarrow{d} [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ the morphism that avoids $i$, and where $k'_j := k_j - 1$ if $i$ factors through $[k_j]$ and $k'_j := k_j$ if not. We then define $(\Delta^3_{/[n]})_{/\Lambda^i x}$ as the full subcategory of $(\Delta^3_{/[n]})_x$ that includes any non negative object $x' \to x$ that are different of $d^i x \to x$ and $id : x \to x$.

Lemma 3.2.4.3. For any regular object $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ and for any $i : [0] \to [k_0] \star [k_1]^{op} \star [k_2]$ which is neither $k_0 + 1$ nor $k_0 + k_1 + 1$, the morphism

$$\underset{(\Delta^3_{/[n]})_{\Lambda^i x}}{\operatorname{colim}} [a, \_] \vee [\_ \otimes a, 1] \vee [a, \_] \to [a, k_0] \vee [[k_1] \otimes a, 1] \vee [a, k_2]$$

is an acyclic cofibration.

Proof. Suppose first that the image of $i$ is in $[k_0]$. There is a cocartesian square:

$$\begin{array}{c} [[k_1] \otimes a, \Lambda^i [k_0 + 1 + k_2]] \cup [\partial [k_1] \otimes a, [k_0 + 1 + k_2]] \to \underset{(\Delta^3_{/[n]})_{/\Lambda^i x}}{\operatorname{colim}} [a, \_] \vee [\_ \otimes a, 1] \vee [a, \_] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [[k_1] \otimes a, [k_0 + 1 + k_2]] \xrightarrow{} [a, k_0] \vee [[k_1] \otimes a, 1] \vee [a, k_2] \end{array}$$

133

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

where the left-hand morphism is an acyclic cofibration. The case where the image of i is in  \( [k_{2}] \)  is similar. Suppose now that i lands in  \( [k_{1}] \) . We then define  \( i' := i - k_{0} - 1 \) , and there is a cocartesian square:

![img-103.jpeg](img-103.jpeg)

where the left-hand morphism is an acyclic cofibration.

Lemma 3.2.4.4. Let \(0 < k < n\) be two integers. The morphism

\[
\underset {\Delta_ {/ \Lambda^ {k} [ n ]} ^ {3} \cup K _ {\leq d}} {\text {colim}} [ a, \_ ] \vee [ \_ \otimes a, 1 ] \vee [ a, \_ ] \to \underset {\Delta_ {/ \Lambda^ {k} [ n ]} ^ {3} \cup K _ {\leq d + 1}} {\text {colim}} [ a, \_ ] \vee [ \_ \otimes a, 1 ] \vee [ a, \_ ]
\]

is an acyclic cofibration

Proof. For  \( x := [k_{0}] \star [k_{1}]^{op} \star [k_{2}] \to [n] \)  a regular element of degree  \( d + 1 \) , we denote by  \( s_{x} \)  the section of x that avoids  \( k_{0} + 1 \)  and  \( k_{0} + k_{1} + 1 \) . We denote  \( R_{d+1} \)  the set of regular elements of degree  \( d + 1 \) . We claim that we have a cocartesian square

\[
\begin{array}{c} \coprod_ {x \in R _ {d + 1}} (\Delta_ {/ [ n ]} ^ {3}) _ {/ \Lambda^ {s _ {k} (x)} x} \longrightarrow \Delta_ {/ \Lambda^ {k} [ n ]} ^ {3} \cup K _ {\leq d} \\ \Biggl \downarrow \quad \Biggl \downarrow \\ \coprod_ {x \in R _ {d + 1}} (\Delta_ {/ [ n ]} ^ {3}) _ {/ x} \longrightarrow \Delta_ {/ \Lambda^ {k} [ n ]} ^ {3} \cup K _ {\leq d + 1} \end{array} \tag {3.2.4.5}
\]

This will induce a cocartesian square:

![img-104.jpeg](img-104.jpeg)

where the left vertical morphism is an acyclic cofibration according to lemma 3.2.4.3, which will conclude the proof.

We then have to justify the cocartesianess of the square (3.2.4.5). We denote by \(D\) the colimit of the underlying span of this square and \(\psi : D \to \Delta_{/\Lambda^k [n]}^3 \cup K_{\leq d + 1}\) the induced morphism. We will construct an inverse \(\phi\) of this functor.

Let \( x:[k_0]\star [k_1]^{op}\star [k_2]\to [n] \) be an element of \( \Delta_{/[n]}^3 \) of degree \( (d + 1) \). We denote by \( x_{r} \) the regular element characterized by the triple \( (x(k_{1}),d + 1,n - x(k_{0} + k_{1} + 1)) \). There is a

134

3.2. GRAY CONSTRUCTIONS FOR STRATIFIED SEGAL A-CATEGORIES

unique morphism $x \to x_r$. Furthermore, for any other regular element $x'$, $\operatorname{Hom}(x, x') = \emptyset$. We then set

$$\phi(x) := x \to x_r \in (\Delta^3_{/[n]})_{/x_r}.$$

If $x : [k_0] \star [k_1]^{op} \star [k_2] \to [n]$ is an element of $\Delta^3_{/\Lambda^k[n]}$, we set

$$\phi(x) := x \in \Delta^3_{/\Lambda^k[n]} \cup K_{\le d}.$$

To justify that this is well defined, remark that for any object $x$ of $\Delta^3_{\Lambda^k[n]}$ of degree $d+1$, the morphism $x \to x_r$ factors through $\Lambda^{s_k(x_r)}x_r$. This assignation lifts to a functor $\phi : \Delta^3_{/\Lambda^k[n]} \cup K_{\le d+1} \to D$ that is an inverse of $\psi$.

**Proposition 3.2.4.6.** *The morphism $I \otimes ([a, 1] \cup [a, 1] \cup ... \cup [a, 1]) \to I \otimes [a, n]$ is an acyclic cofibration.*

*Proof.* Let $0 < k < n$ be two integers. Let's demonstrate first that morphisms $I \otimes [a, \Lambda^k[n]] \to I \otimes [a, n]$ are acyclic cofibrations. We set

$$P_d := \underset{\Delta^3_{/\Lambda^k[n]} \cup K_{\le d}}{\operatorname{colim}} [a, \_] \vee [\_ \otimes a, 1] \vee [a, \_].$$

According to lemma 3.2.4.4, we have a sequence of acyclic cofibrations $I \otimes [a, \Lambda^k[n]] = P_0 \to P_1... \to P_n = I \otimes [a, n]$. This implies that the functor $I \otimes [a, \_] : \operatorname{Psh}(\Delta) \to \operatorname{tSeg}(A)$ sends inner anodyne extensions to weak equivalences.

Eventually, proposition 3.7.4 of [Cis19] states that the inclusion $[1] \cup ... \cup [1] \cup [1] \to [n]$ is an inner anodyne extension, which concludes the proof.

**Lemma 3.2.4.7.** *Let $a \to b$ be a generating acyclic cofibration. The morphism $I \otimes ([a, n] \cup [b, \partial[n]]) \to I \otimes [b, n]$ is an acyclic cofibration.*

*Proof.* It is obvious that $I \otimes [a, n] \to I \otimes [b, n]$ is an acyclic cofibration. As $I \otimes [\_, \partial[n]]$ is the homotopy colimit of element of shape $I \otimes [\_, [k]]$, the morphism $I \otimes [a, \partial[n]] \to I \otimes [b, \partial[n]]$ also is an acyclic cofibration. Now, we consider the diagram:

![img-105.jpeg](img-105.jpeg)

By stability of acyclic cofibration by pushouts and by two out of three, this implies the result.

135

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Lemma 3.2.4.8. The morphism \( I \otimes E^{\cong} \to I \otimes (E^{\cong})' \) is an acyclic cofibration.

Proof. First of all, remark that  \( E^{\cong} \to [0] \)  is a weak equivalence in  \( \operatorname{tSeg}(A) \) . According to the proposition 3.2.3.2, we then have a commutative square:

![img-106.jpeg](img-106.jpeg)

where all arrows labelled by  \( \sim \)  are weak equivalences. By two out of three, this implies the result.

Lemma 3.2.4.9. The morphism \( I \otimes [e,1]_t \to I \otimes e \) is a weak equivalence.

Proof. This morphism is the horizontal colimit of the diagram

![img-107.jpeg](img-107.jpeg)

As all the vertical morphisms are weak equivalences, and as these colimits are homotopy colimits, this concludes the proof.

Proposition 3.2.4.10. The functor \( I \otimes \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A) \) is a left Quillen functor.

Proof. It is obvious that this functor preserves cofibrations. Proposition 3.2.4.6 and lemmas 3.2.4.7, 3.2.4.8 and 3.2.4.9 imply that it sends elementary anodyne extensions, and morphisms \( E^{\cong} \to (E^{\cong})' \), \( [e,1]_t \to 1 \) to weak equivalences. According to proposition 3.1.2.10, this implies the result.

Corollary 3.2.4.11. The functor \( e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)_{e/} \) is a left Quillen functor.

Proof. First of all, it is obvious that this functor preserves cofibrations. It is then enough to show that it preserves weak equivalences. Proposition 3.2.3.2 implies that \( e \star \_ \) is the homotopy colimit of the diagram of functors \( e \leftarrow id \xrightarrow{\mathrm{i}_0} I \otimes \_ \). Each of these functors preserves weak equivalences, and so does \( e \star \_ \).

### 3.3 Quillen Adjunction with tPsh(Δ)

The purpose of this section is to construct a Quillen adjunction

\[
\mathrm{tPsh} (\Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tSeg} (A)
\]

136

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

where the left adjoint sends $[n]$ to $e \star e \star \ldots \star e$.

In section 3.3.1, we show that this assignment extends to a left adjoint. In sections 3.3.2, 3.3.3, and 3.3.4, we show that this left adjoint sends complicial horn inclusions, complicial thinness extensions, and saturation extensions to weak equivalences.

### 3.3.1 Cosimplicial object

3.3.1.1. We consider the following span:

$$\Delta^2_{/[n]} \longleftarrow \underset{\Delta^2_{/[n]}}{\text{colim}} \Delta^2_{/[n_1]} \longrightarrow \underset{\Delta^2_{/[n]}}{\text{colim}} \Delta^2_{/[1+n_1]}$$

where the right functor is induced by $1 + \_ : [n_1] \to [1 + n_1]$ and where the left one sends an element $([n_0]^{op} \star [n_1] \to [n], [n_2]^{op} \star [n_3] \to [n_1])$ to the composite: $h : [n_2]^{op} \star [n_3] \to [n_1] \to [n]$. We define $H^2(a, n)$ as the pushout:

$$\begin{array}{c} \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/[n_1]}}{\text{colim}} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow \underset{\Delta^2_{/[n]}}{\text{colim}} [[n_2] \otimes a, 1] \vee [a, n_3] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/[1+n_1]}}{\text{colim}} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \end{array}$$

By construction, we have a cocartesian square

$$\prod_{l \le 1+n_1} \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/l}}{\text{colim}} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \to H^2(a, n) \prod_{H^2(a, \Pi_{p \le n}\{p\})} H^2(e, \Pi_{p \le n}\{p\}) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \prod_{l \le 1+n_1} \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/l}}{\text{colim}} [[n_2] \otimes e, 1] \vee [e, n_3] \longrightarrow e \star e \star [a, n] \end{array} \tag{3.3.1.2}$$

Let $x := ([n_0]^{op} \star [n_1] \to [n], [n_2]^{op} \star [n_3] \to [1 + n_1])$ be an element of $\underset{\Delta^2_{/[n]}}{\text{colim}} \Delta^2_{/[1+n_1]}$. We define two integers $-1 \le \tilde{n}_2 \le n_2$ and $-1 \le \tilde{n}_3 \le n_3$ as the ones fitting in the following pullbacks in $\Delta_+$

$$[\tilde{n}_2]^{op} \xrightarrow{\quad} [n_1] \xleftarrow{\quad} [\tilde{n}_3] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [n_2]^{op} \longrightarrow [n_2]^{op} \star [n_3] \longrightarrow [1 + n_1] \xleftarrow{\quad} [n_2]^{op} \star [n_3] \xleftarrow{\quad} [n_3]$$

137

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

where we set the convention  \( [-1] = \emptyset \) . This induces a cartesian square

![img-108.jpeg](img-108.jpeg)

We consider the morphism \( j:[n_2]\otimes [n_0]\otimes a\to ([n_2]\times [n_0])\otimes a\to ([\tilde{n}_2]\star [n_0])\otimes a \) where the right-hand morphism sends \( \{(k,l)\} \otimes a \) to \( (\{k\} \star \emptyset)\otimes a \) if \( k\leq \tilde{n}_2 \) and to \( (\emptyset \star \{l\})\otimes a \) if not. The inclusion \( [\tilde{n}_3]\to [n_3] \) induces an inclusion \( i:[1 + \tilde{n}_3]\to [1 + n_3] \). We denote \( r \) the unique retraction of this inclusion that verifies \( r(k) = 0 \) if \( k\notin Im(i) \). Put together, \( j \) and \( r \) induce a morphism:

\[
\psi_ {x}: [ [ n _ {2} ] \otimes [ n _ {0} ] \otimes a, 1 ] \vee [ [ n _ {0} ] \otimes a, n _ {3} ] \rightarrow [ ([ \tilde {n} _ {2} ] \star [ n _ {0} ]) \otimes a, 1 ] \vee [ a, \tilde {n} _ {3} ]
\]

where we set the convention  \( \left[\left(\left[\tilde{n}_{2}\right]\star\left[n_{0}\right]\right)\otimes a,1\right]\vee\left[a,-1\right]:=[0] \) .

Remark that if \([n_2]^{op} \star [n_3] \to [1 + n_1]\) factors through \([n_1] \to [1 + n_1]\), we have \(\tilde{n}_2 = n_2\) and \(\tilde{n}_3 = n_3\), and a unique arrow fitting in a commutative triangle

![img-109.jpeg](img-109.jpeg)

Considering the canonical morphism

\[
[ ([ \tilde {n} _ {2} ] \star [ n _ {0} ]) \otimes a, 1 ] \vee [ a, \tilde {n} _ {3} ] \rightarrow e \star [ a, n ]
\]

if \(\tilde{n}_3\geq 0\) (coming from the fact that \(([n_0]^{op}\star [\tilde{n}_2]^{op})\star [\tilde{n}_3]\to [n]\) is an element of \(\Delta_{[n]}^2\)), and the morphism

\[
[ ([ \tilde {n} _ {2} ] \star [ n _ {0} ]) \otimes a, 1 ] \vee [ a, \tilde {n} _ {3} ] \rightarrow e \star \emptyset \rightarrow e \star [ a, n ]
\]

if \(\tilde{n}_3 = -1\), this induces a natural transformation

\[
H ^ {s ^ {0}} (a, n): H ^ {2} (a, n) \to e \star [ a, n ]
\]

induced by \(\psi_{-}\) on \(\underset{\Delta_{j[n]}^{2}}{\mathrm{colim}}\underset{\Delta_{j[1 + n_{1}]}^{2}}{\mathrm{colim}}\left[[n_{2}]\otimes [n_{0}]\otimes a,1\right]\vee [[n_{0}]\otimes a,n_{3}]\) and by the identity on \(\underset{\Delta_{j[n]}^{2}}{\mathrm{colim}}\left[[n_{2}]\otimes a,1\right]\vee [a,n_{3}]\).

138

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

By construction, if $[n_0]^{op} \star [n_1] \to [n]$ factor through $\{p\}$ for $p \leq n$ we have a commutative diagram

$$\begin{array}{c} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \\ \downarrow \hspace{2em} \downarrow \\ [[n_2] \otimes [n_0] \otimes e, 1] \vee [[n_0] \otimes e, n_3] \longrightarrow e \star \{p\} \longrightarrow e \star [a, n] \end{array}$$

If $[n_2]^{op} \star [n_3] \to [1+n_1]$ factors through $\{0\}$, $\tilde{n}_3$ is equal to $-1$, and we have a commutative diagram

$$\begin{array}{c} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \\ \downarrow \hspace{2em} \downarrow \\ [[n_2] \otimes e, 1] \vee [e, n_3] \longrightarrow e \star \emptyset \longrightarrow e \star [a, n] \end{array}$$

and if $[n_2]^{op} \star [n_3] \to [1+n_1]$ factors through any other point, $\tilde{n}_3$ is equal to 0, and we have a commutative diagram

$$\begin{array}{c} [[n_2] \otimes [n_0] \otimes a, 1] \vee [[n_0] \otimes a, n_3] \longrightarrow H^2(a, n) \\ \downarrow \hspace{2em} \downarrow \\ [[n_2] \otimes e, 1] \vee [e, n_3] \longrightarrow e \star \{k\} \longrightarrow e \star [a, n] \end{array}$$

where $k$ is the image of the composite morphism $[\tilde{n}_2]^{op} \star [\tilde{n}_3] \to [n_1] \to [n]$. The cocartesian square (3.3.1.2) then implies that $H^2(a, n)$ lifts to a natural transformation

$$s^0 \star [a, n] : e \star e \star [a, n] \to e \star [a, n].$$

By extension by colimits, this induces a natural transformation

$$C \mapsto (s^0 \star C : e \star e \star C \to e \star C).$$

To define the cosimplicial object, we will need to show the commutativity of several diagrams whose initial objects are of shape $e \star .. \star e \star [a, n]$. To this extend, it is enough to find coverings of these objects by easier one, and to show that the induced diagrams commute.

**Lemma 3.3.1.3.** We set $\Pi^0_{/[n]} := \Delta^2_{/[n]}$ and

$$\Pi^k_{/[n]} := \underset{\Delta^2_{/[n]}}{\text{colim}} \underset{\Delta^2_{/[n_1+1]}}{\text{colim}} \dots \underset{\Delta^2_{/[n_{2k-1}+1]}}{\text{colim}} \Delta^2_{/[n_{2k+1}+1]}$$

There is an epimorphism:

$$\underset{\Pi^k_{/[n]} \times A}{\text{colim}} [[n_{2k}] \otimes [n_{2k-2}] \otimes ... \otimes [n_0] \otimes a, 1 + n_{2k-1}] \to \underbrace{e \star e \star ... \star e}_{k+1} \star [a, n]$$

139

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. This is an easy proof by induction, after remarking that

\[
[ [ n _ {0} ] \otimes a, 1 + n _ {1} ] \rightarrow [ [ n _ {0} ] \otimes a, 1 ] \vee [ a, n _ {1} ]
\]

is an epimorphism.

Lemma 3.3.1.4. The following triangles commute:

![img-110.jpeg](img-110.jpeg)

Proof. We will prove only the left triangle and we leave the other to the reader. Let  \( x := ([n_{0}]^{op} \star [n_{1}] \to [n], [n_{2}]^{op} \star [n_{3}] \to [1 + n_{1}]) \)  be an element of  \( \operatorname{colim}_{\Delta_{/[n]}^{2}} \Delta_{/[1+n_{1}]}^{2} \) . We have a diagram:

![img-111.jpeg](img-111.jpeg)

where we know that everything except the right triangle commutes. As this is true for any x, lemma 3.3.1.3 implies the desired commutativity. □

Lemma 3.3.1.5. The following square commutes

\[
\begin{array}{c} e \star e \star e \star [ a, n ] \xrightarrow {s ^ {1} \star e \star [ a , n ]} e \star e \star [ a, n ] \\ e \star s ^ {1} \star [ a, n ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star e \star [ a, n ] \xrightarrow [ s ^ {1} \star [ a , n ] ]{} e \star [ a, n ] \end{array}
\]

Proof. Let  \(  x = (f : [n_{0}]^{op} \star [n_{1}] \to [n], g : [n_{2}]^{op} \star [n_{3}] \to [1 + n_{1}], h : [n_{4}]^{op} \star [n_{5}] \to [n_{3} + 1])  \)  be an object of  \( \Pi_{k}^{2} \) . We define integers  \( -1 \leq \bar{n}_{4} \leq n_{4} \)  and  \( -1 \leq \bar{n}_{5} \leq n_{5} \)  as the one fitting in the following pullbacks in  \( \Delta_{+} \) .

![img-112.jpeg](img-112.jpeg)

140

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

This induces cartesian squares

![img-113.jpeg](img-113.jpeg)

The outer squares fits in the following cartesian squares:

![img-114.jpeg](img-114.jpeg)

This induces a diagram:

![img-115.jpeg](img-115.jpeg)

where we know that everything except the behind square commutes. As this is true for any x, lemma 3.3.1.3 implies the desired commutativity.

Definition 3.3.1.6. For k ≤ 1, the intelligent k-truncation functor, noted by τ_k^i, is the colimit preserving functor such that τ_k^i([a, n]) = [τ_{k-1}^i(a), n] and τ_k^i[e, 1]_t = [e, 1]_t. The intelligent 0-truncation functor, denoted by τ_0^i, is the colimit preserving functor such that τ_0^i([a, n]) fits in the following pushout

![img-116.jpeg](img-116.jpeg)

141

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

and such that $\tau_0^i[e,1]_t = [e,1]_t$. As the intelligent $k$-truncations on $A$ are left Quillen, the intelligent $k$-truncations on $\mathrm{tSeg}(A)$ preserve generating Reedy cofibrations and Segal extensions. It is straightforward that they also send $[e,1]_t \to [0]$ and $E^{\cong} \to (E^{\cong})'$ to weak equivalences. According to theorem 3.1.2.10, they are left Quillen functors.

3.3.1.7. The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of $\mathrm{tSeg}(A)$. Lemmas 3.3.1.4 and 3.3.1.5 show that $e \star \_ \$ is a monoid for this monoidal structure. This induces a cosimplicial object:

$$
\begin{array}{l}
\Delta \to \operatorname{End}(\mathrm{tSeg}(A)) \\
[n] \mapsto [n] \star \_ := \underbrace{e \star e \star \ldots \star e}_{n+1} \star \_
\end{array}
$$

We extend this functor to $\Delta_t$ in setting for a stratified Segal $A$-precategory $C$ and an integer $n > 0$:

$$
\begin{array}{ccc}
\coprod_{k \ge -1} & \coprod_{D, \tau_k^i(D)=D} & \coprod_{D \to C} [n] \star D & \longrightarrow & [n] \star C \\
& \downarrow & & \downarrow \\
\coprod_{k \ge -1} & \coprod_{D, \tau_k^i(D)=D} & \coprod_{D \to C} \tau_{n+k}^i([n] \star D) & \longrightarrow & [n]_t \star C
\end{array}
$$

where $\tau_{-1}^i$ is the constant functor with value $\emptyset$. Evaluated on the empty Segal $A$-category, and by extension under colimits, this gives a functor

$$
\mathrm{tPsh}(\Delta) \to \mathrm{tSeg}(A). \tag{3.3.1.8}
$$

The image of $[n]$ (resp. $[n]_t$) is also noted by $[n]$ (resp. $[n]_t$).

By construction, for $K, L$ two stratified sets and $D$ a stratified Segal $A$-precategory, we have $K \star (L \star C) \cong (K \star L) \star C$.

Lemma 3.3.1.9. Let $K$ be a stratified simplicial set. The morphism $K \star \_ \$$ is a left Quillen functor. Moreover, if $i$ is a cofibration of stratified simplicial sets and $g$ an acyclic cofibration of stratified Segal $A$-precategories, the morphism $i \star g$ is an acyclic cofibration.

Proof. As every simplicial set is a homotopy colimit of representables and as $\star$ preserves monomorphisms, it is enough to show the first assertion for $K = [n]$. In this case, this is a repeated application of the corollary 3.2.4.11. By diagram chasing and the use of two out of three, this implies the second assertion. □

142

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

### 3.3.2 Complicial horn inclusions

Notation. In this section, we will often consider morphisms $\tilde{a} \to \tilde{b}$ that fit into cocartesian squares:

![img-117.jpeg](img-117.jpeg)

where $a \to \tilde{a}$ and $b \to \tilde{b}$ are epimorphisms. To avoid complicating the notations unnecessarily, the induced morphism $\tilde{a} \to \tilde{b}$ will just be denoted $i$.

3.3.2.1. A marked Segal A-precategory is a stratified Segal A-precategory having the right lifting property against all entire acyclic cofibrations. We denote by mSeg(A) the full subcategory of marked Segal A-precategory. We then have an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tSeg}(A) \xleftarrow{\perp} \mathrm{mSeg}(A) : \iota$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified Segal A-precategory $(C, tC)$ to the marked Segal A-precategory $(C, \overline{tC})$, where $\overline{tC}$ is the smaller stratification that includes $tC$ and makes $(C, \overline{tC})$ a marked Segal A-precategory, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of preshaves, these two adjoints are the identity. We denote $r_C : C \to C_{\mathrm{mk}}$ the canonical inclusion. The proposition 2.1.2.9 states that $r_C$ is an entire acyclic cofibration.

There is an isomorphism $(e \star C_{\mathrm{mk}})_{\mathrm{mk}} \cong (e \star C)_{\mathrm{mk}}$. Indeed $e \star \_$ preserves both entire cofibrations and weak equivalences, we have two entire acyclic cofibration $e \star C \to (e \star C)_{\mathrm{mk}}$ and $e \star C \to (e \star C_{\mathrm{mk}})_{\mathrm{mk}}$. As the two codomain are marked, they are isomorphic.

The fact that will be used the most with the marked Segal A-precategory is their right lifting property with respect to morphisms of shape $[\tau_n^i(a), \Lambda^1[2]] \cup [a, 2] \to [\tau_n^i(a), 2]$. This fact will be used freely.

3.3.2.2. We recall that $[2] \bar{\otimes} a$ is the following pushout:

![img-118.jpeg](img-118.jpeg)

We define $[e, 1] \vee (e \star [a, 1])$ as the colimit of the following diagram

$$[e, 1] \vee [e \star a, 1] \xleftarrow{[d^0 \star a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^2]} [e, 2] \vee [a, 1]$$

143

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

The canonical composite morphism

\[
[ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {1} ]} [ e, 1 ] \vee [ e \star a, 1 ] \to [ e, 1 ] \vee (e \star [ a, 1 ])
\]

is also denoted by \([e\star a,d^1]\). Eventually, we define \(\overline{[1]\star[a,1]}\) as the following pushout

![img-119.jpeg](img-119.jpeg)

Lemma 3.3.2.3. There is a weak equivalence from \(\overline{[1] \star [a, 1]}\) to the colimit of the diagram

\[
[ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {1} ]} [ e, 1 ] \vee (e \star [ a, 1 ])
\]

making \(\overline{[1] \star [a, 1]}\) the homotopy colimit of the previous diagram.

Proof. The proposition 3.2.2.8 implies that \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) is the colimit of the diagram

\[
\begin{array}{c} \left[ [ 2 ] ^ {2} \bar {\otimes} a, 1 \right] \xleftarrow {[ d ^ {0} \otimes a , 1 ]} \left[ [ 1 ] _ {t} \otimes a, 1 \right] \xrightarrow {[ [ 1 ] \otimes a , d ^ {1} ]} \left[ [ 1 ] _ {t}, 1 \right] \vee [ a, 1 ] \xleftarrow {[ d ^ {0} \otimes a , 2 ]} [ e, 1 ] \vee [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 2 ] \vee [ a, 1 ] \\ \left[ d ^ {1} \bar {\otimes} a, 1 \right] \uparrow \\ [ e \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 1 ] \vee [ a, 1 ] \\ \left[ d ^ {1} \star a, 1 \right] \downarrow \\ [ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ d ^ {0} \star a, 1 ] \downarrow \\ [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {1} ]} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.3.2.4}
\]

In the previous diagram, the fact that we have \(\left[[1]_t\otimes a,1\right]\) instead of \(\left[[1]\otimes a,1\right]\) comes from the fact that we have considered \((\overline{[1]\star[a,1]})_{\mathrm{mk}}\) instead of \(\overline{[1]\star[a,1]}\).

Consider now the morphism

\[
[ [ 2 ] ^ {2} \bar {\otimes} a, 1 ] \coprod_ {[ [ 1 ] _ {t} \otimes a, 1 ]} [ [ 1 ] _ {t}, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 1 ] \tag {3.3.2.5}
\]

induces by the vertical colimit of the diagram

\[
\begin{array}{c} \left[ [ 2 ] ^ {2} \bar {\otimes} a, 1 \right] \xleftarrow {[ d ^ {0} \otimes a , 1 ]} \left[ [ 1 ] _ {t} \otimes a, 1 \right] \xrightarrow {[ [ 1 ] \otimes a , d ^ {1} ]} \left[ [ 1 ] _ {t}, 1 \right] \vee [ a, 1 ] \\ \left[ s ^ {0} \bar {\otimes} a, 1 \right] \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text {   } \\ [ e \star a, 1 ] \xleftarrow {} [ a, 1 ] \xrightarrow {} [ e, 1 ] \vee [ a, 1 ] \end{array} \tag {3.3.2.6}
\]

As all the vertical morphisms of  \( (3.3.2.6) \)  are cofibrations, the colimit of each line is a homotopy colimit. As all the horizontal morphisms of  \( (3.3.2.6) \)  are weak equivalences, the morphism  \( (3.3.2.5) \)  also is a weak equivalence.

144

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

Consider now the span

$$e \star [ a , 1 ] \xleftarrow {(3 . 3 . 2 . 5)} [ [ 2 ] ^ { 2 } \bar { \otimes } a , 1 ] \coprod _ { [ [ 1 ] _ { t } \otimes a , 1 ] } [ [ 1 ] _ { t } , 1 ] \vee [ a , 1 ] \rightarrow ( \overline { { [ 1 ] \star [ a , 1 ] } } ) _ { \mathrm { m k } } \tag {3.3.2.7}$$

As the right hand morphism is a cofibration, and as (3.3.2.5) is a weak equivalence, the canonical morphism from $$(\overline{[1] \star [a, 1]})_{\mathrm{mk}}$$ to the colimit of (3.3.2.7) is a weak equivalence. Using the diagram (3.3.2.4), the colimit of (3.3.2.7) is also the colimit of the following diagram

$$\begin{array} { c } { { e \star [ a , 1 ] \xleftarrow {} [ e , 1 ] \vee [ a , 1 ] \xrightarrow { [ a , d ^ { 1 } ] } [ e , 2 ] \vee [ a , 1 ] } } \\ { { \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ a , d ^ { 2 } ] } } \\ { { [ e \star a , 1 ] \xleftarrow { [ d ^ { 0 } \star a , 1 ] } [ a , 1 ] \xrightarrow { [ a , d ^ { 1 } ] } [ e , 1 ] \vee [ a , 1 ] } } } \\ { { [ d ^ { 1 } \star a , 1 ] \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ d ^ { 0 } \star a , 2 ] } } } \\ { { [ [ 1 ] \star a , 1 ] \xleftarrow { [ d ^ { 0 } \star a , 1 ] } [ e \star a , 1 ] \xrightarrow { [ e \star a , d ^ { 1 } ] } [ e , 1 ] \vee [ e \star a , 1 ] } } } \end{array}$$

As the upper left square is cocartesian, the colimit of the previous diagram is equivalent to the colimit of the given diagram. All put together, we have demonstrated the assertion.

□

### Lemma 3.3.2.8. The morphism

$$[ e , 1 ] \vee ( e \star [ a , 1 ] ) \cup \{ 1 \} \star [ e \star a , 1 ] \rightarrow [ e , 1 ] \vee ( e \star [ e \star a , 1 ] )$$

is a weak equivalence.

Proof. We have a cocartesian square

$$\begin{array} { c } { { [ e , 1 ] \cup e \star [ a , 1 ] \xrightarrow { [ e , 1 ] \cup e \star [ d ^ { 0 } \star a , 1 ] } [ e , 1 ] \cup e \star [ e \star a , 1 ] } } \\ { { \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ e , 1 ] \vee ( e \star [ a , 1 ] ) \longrightarrow [ e , 1 ] \vee ( e \star [ a , 1 ] ) \cup \{ 1 \} \star [ e \star a , 1 ] } } \end{array} \tag {3.3.2.9}$$

Remark that the left vertical morphism is the vertical colimit and homotopy colimit of the diagram

$$\begin{array} { c } { { [ e , 1 ] \cup [ e \star a , 1 ] \xleftarrow {} [ e , 1 ] \cup [ a , 1 ] \longrightarrow [ e , 1 ] \cup [ e , 1 ] \vee [ a , 1 ] } } \\ { { \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ e , 1 ] \vee [ e \star a , 1 ] \xleftarrow {} [ e , 1 ] \vee [ a , 1 ] \longrightarrow [ e , 2 ] \vee [ a , 1 ] } } \end{array}$$

and is then a weak equivalence. Similarly, $$[ e , 1 ] \cup e \star [ e \star a , 1 ] \rightarrow [ e , 1 ] \vee ( e \star [ e \star a , 1 ] )$$ is a weak equivalence. This implies that the right vertical morphism of (3.3.2.9) is a weak equivalence. By two out of three this concludes the proof.

145

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Lemma 3.3.2.10. The morphism \(\{1\} \star [0] \to [1]_t \star [0]\) is an acyclic cofibration.

Proof. Using proposition 3.2.2.6 we deduce that \([1]_t \star [0]\) is the colimit of the diagram

\[
[ [ 1 ] _ {t}, 1 ] \longleftarrow [ e, 1 ] \longrightarrow [ e, 1 ] _ {t} \vee [ e, 1 ]
\]

The inclusion \(\{1\} \star [0] \to [1]_t \star [0]\) is then the composite of the following sequence

\[
\begin{array}{c} [ e, 1 ] \xrightarrow {[ d ^ {0} , 1 ]} [ [ 1 ] _ {t}, 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e, 1 ] \xrightarrow {[ e , d ^ {0} ]} [ e, 1 ] _ {t} \vee [ e, 1 ] \longrightarrow [ 1 ] _ {t} \star [ 0 ] \end{array}
\]

As the morphism \([e, d^0]\) and \([d^0, 1]\) are acyclic cofibrations, this concludes the proof.

Lemma 3.3.2.11. The morphism \(\{1\} \star [a,1] \to [1]_t \star [a,1]\) is an acyclic cofibration.

Proof. The Segal \(A\)-precategory \([1]_t \star [a, 1]\) is the colimit and the homotopy colimit of the diagram

\[
\begin{array}{c} [ 1 ] \star \emptyset \\ \Big \downarrow \\ [ 1 ] _ {t} \star \emptyset \end{array} \xrightarrow {} \begin{array}{c} [ 1 ] \star [ a, 1 ] \\ \hline \end{array} \xleftarrow {} \begin{array}{c} [ a \star [ 1 ], 1 ] \\ \Big \downarrow \\ [ a \star [ 1 ] _ {t}, 1 ] \end{array}
\]

The lemma 3.3.2.3 then implies that we have a weak equivalence from \([1]_t \star [a, 1]\) to the colimit, denoted by \(K\), of the diagram

\[
[ [ 1 ] _ {t} \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {1} ]} [ e, 1 ] _ {t} \vee (e \star [ a, 1 ])
\]

As all the morphisms are cofibrations, \( K \) is also the homotopy colimit of the previous diagram.

The morphism \([e,1]_t\vee (e\star [a,1])\to e\star [a,1]\) is a weak equivalence as it is a homotopy colimit of weak equivalences. Moreover, the morphism \([(1)_t\star a,1]\to [e\star a,1]\) is also a weak equivalence. This implies that the composite \(s^0\star [a,1]:[1]_t\star [a,1]\to K\to [0]\star [a,1]\) is a weak equivalence. The morphism \(\{1\} \star [a,1]\to [1]_t\star [a,1]\) is a section of \(s^0\star [a,1]\) and is then also a weak equivalence.

Lemma 3.3.2.12. The morphism \(\Lambda^1 [2]\star [0]\to [2]_t\star [0]\) is an acyclic cofibration.

Proof. The Segal \(A\)-precategory \([2]_t \star [0]\) is the colimit of the following diagram

\[
[ [ 2 ] _ {t}, 1 ] \longleftarrow [ [ 2 ], 1 ] \longrightarrow \overline {{[ 1 ] \star [ 1 ]}}
\]

146

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

The lemma 3.3.2.3 then implies that we have a weak equivalence from \([2]_t \star [0]\) to the colimit, denoted by \(K\), of the diagram

\[
[ [ 2 ] _ {t}, 1 ] \xleftarrow {[ d ^ {0} , 1 ]} [ [ 1 ], 1 ] \xrightarrow {[ [ 1 ] , d ^ {1} ]} [ e, 1 ] \vee (e \star [ e, 1 ])
\]

On the other side, \(\Lambda^1 [2]\star [0]\) is the colimit of the diagram

![img-120.jpeg](img-120.jpeg)

The composite \(\Lambda^1 [2]\star [0]\to [2]_t\star [0]\to K\) fits in the sequence of acyclic cofibrations

![img-121.jpeg](img-121.jpeg)

and is then a weak equivalence. By two out of three, this concludes the proof.

Lemma 3.3.2.13. The morphism \(\Lambda^1 [2]\star [a,1]\to [2]_t\star [a,1]\) is an acyclic cofibration.

Proof. The lemma 3.3.2.12 implies that the inclusion \(\Lambda^1 [2]\star [a,1]\to \Lambda^1 [2]\star [a,1]\cup [2]_t\star \{0\}\) is an acyclic cofibration. Using proposition 3.2.2.6, we deduce that the Segal \(A\) -precategory \([2]_t\star [a,1]\) is the colimit of the diagram

![img-122.jpeg](img-122.jpeg)

while \(\Lambda^1 [2]\star [a,1]\cup [2]_t\star \{0\}\) is the colimit of the diagram

![img-123.jpeg](img-123.jpeg)

where \(\overline{[1] \star [e, 1]} := [2]_t \star [0]\) and where \(\overline{[1] \star [e \star a, 1]}\) is the following pushout:

![img-124.jpeg](img-124.jpeg)

147

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Let \( K_{1} \) be the following pushout:

![img-125.jpeg](img-125.jpeg)

The left-hand morphism is equal to \((d^0:[0]\to [1])\hat{\star} ([e,1]\cup [a,1]\to [e,1]\lor [a,1])\) which is an acyclic cofibration according to lemma 3.3.1.9. Furthermore, the morphism \(K_{1}\rightarrow\) \([2]_t\star [a,1]\) fits in the following pushout:

![img-126.jpeg](img-126.jpeg)

The lemma 3.3.2.3 implies that we have a weak equivalence from \(\overline{[1] \star [a, 1]} \cup \{1\} \star [e \star a, 1]\) to the colimit, denoted by \(K_2\), of the diagram

\[
[ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {1} ]} [ e, 1 ] \vee (e \star [ a, 1 ]) \cup \{1 \} \star [ e \star a, 1 ]
\]

As all the morphisms are cofibrations, \( K_{2} \) is also the homotopy colimit of the previous diagram. We now define \( K_{3} \) as the colimit of the diagram

\[
[ \Lambda^ {1} [ 2 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ [ 1 ] \star a, 1 ] \xrightarrow {[ [ 1 ] \star a , d ^ {1} ]} [ e, 1 ] \vee (e \star [ e \star a, 1 ])
\]

The canonical morphism \( K_{2} \to K_{3} \) fits in the cocartesian square

![img-127.jpeg](img-127.jpeg)

and is then a weak equivalence according to the lemma 3.3.2.8.

On the other side, the lemma 3.3.2.3 also implies that we have a weak equivalence from \(\overline{[1] \star [e \star a, 1]}\) to the colimit, denoted by \(K_4\), of the diagram

\[
[ [ 2 ] _ {t} \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ [ 1 ] \star a, 1 ] \xrightarrow {[ [ 1 ] \star a , d ^ {1} ]} [ e, 1 ] \vee (e \star [ e \star a, 1 ])
\]

As all the morphisms are cofibrations, \( K_{4} \) is also the homotopy colimit of the previous diagram. As \( \Lambda^1 [2]\star a\to [2]_t\star a \) is a weak equivalence in \( A \), this implies that the canonical morphism \( K_{3}\rightarrow K_{4} \) is also a weak equivalence. We then have commutative diagram:

![img-128.jpeg](img-128.jpeg)

148

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

where all arrows labelled by ∼ are weak equivalences. By two out of three, this implies the result.

Lemma 3.3.2.14. For any stratified Segal A-precategory C, the morphisms Λ¹[2] ⋆ C → [2]ₜ ⋆ C and {1} ⋆ C → [1]ₜ ⋆ C are acyclic cofibrations. Moreover, for any cofibration of stratified Segal A-precategory i, and j being either {1} → [1]ₜ or Λ¹[2] → [2]ₜ, the morphism j ⋆ i is an acyclic cofibration.

Proof. We begin with the first assertion. The lemma 3.3.1.9 implies that Λ¹[2] ⋆ _ and [2]ₜ ⋆ _ are left Quillen functors. As every object is a homotopy colimits of objects of shape [a, n] or [e, 1]ₜ, we can reduce to the case where C is of this shape. Using Segal extensions, we can reduce to the case where C is [a, 1], [0] or [e, 1]ₜ.

If C is [a, 1] or [0], the result follows from lemmas 3.3.2.10, 3.3.2.11, 3.3.2.12 and 3.3.2.13.

Eventually, for C := [e, 1]ₜ, we have a diagram:

![img-129.jpeg](img-129.jpeg)

![img-130.jpeg](img-130.jpeg)

Lemmas 3.3.1.9, 3.3.2.10 and 3.3.2.12 imply that all horizontal morphisms and right vertical morphisms are weak equivalences. By two out of three, this implies that the left vertical morphisms are weak equivalences.

This concludes the proof of the first assertion. The second one is obtained with some diagram chasing.

Proposition 3.3.2.15. The functor tPsh(Δ) → tSeg(A) sends complicial horn inclusions to weak equivalences.

Proof. Let k ≤ n be two integers. First, we suppose that 0 < k < n. We then have an equality

$$(\Lambda^k[n] \to [n]^k) = (\partial[k-2] \to [k-2]) \hat{\star}(\Lambda^1[2] \to [2]_t) \hat{\star}(\partial[n-k-2] \to [n-k-2]).$$

This is an acyclic cofibration according to lemmas 3.3.1.9 and 3.3.2.14. If k = 0, we have an equality

$$(\Lambda^0[n] \to [n]^0) = (\{1\} \to [e, 1]_t) \hat{\star}(\partial[n-2] \to [n-2])$$

and the right hand morphism is an acyclic cofibration again thanks to lemma 3.3.2.14. Eventually, for k = n, note that

$$(\Lambda^n[n] \to [n]^n) = (\partial[n-2] \to [n-2]) \hat{\star}(\{0\} \to [e, 1]_t).$$

This morphism is an acyclic cofibration according to lemma 3.3.1.9.

149

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

#### 3.3.3 Complicial thinness extensions

Notation. In this section, we will often consider morphisms \(\tilde{a} \to \tilde{b}\) that fit into cocartesian squares:

![img-131.jpeg](img-131.jpeg)

where  \( a \rightarrow \tilde{a} \)  and  \( b \rightarrow \tilde{b} \)  are epimorphisms. To avoid complicating the notations unnecessarily, the induced morphism  \( \tilde{a} \rightarrow \tilde{b} \)  will just be denoted i.

Lemma 3.3.3.1. Morphisms \(([n]^0)' \to ([n]^0)''\) and \(([n]^n)' \to ([n]^n)''\) are acyclic cofibrations.

Proof. For \( k \) equal to 0 or \( n \), we have pushout diagrams:

![img-132.jpeg](img-132.jpeg)

Lemmas 3.3.1.9 and 3.3.2.14 imply that both \( s^0 : [n]^0 \to [n-1] \) and \( s^{n-1} : [n]^{n-1} \to [n-1] \) are weak equivalences. As horizontal morphisms are cofibrations, the left properness imply that all the vertical morphisms are weak equivalences. By two out of three, this shows that \( ([n]^k)' \to ([n]^k)'' \) is a weak equivalence.

Construction 3.3.3.2. We consider these objects of \(\Delta_{\mathbb{Z}[1]}^2\) and \(\Delta_{\mathbb{Z}[2]}^2\):

\[
\begin{array}{l} s ^ {1}: [ 1 ] ^ {o p} \star [ 0 ] \rightarrow [ 1 ] \quad s ^ {0}: [ 0 ] ^ {o p} \star [ 1 ] \rightarrow [ 1 ] \\ s ^ {1}: [ 1 ] ^ {o p} \star [ 1 ] \rightarrow [ 2 ] s ^ {2}: [ 2 ] ^ {o p} \star [ 0 ] \rightarrow [ 2 ]. \\ \end{array}
\]

They induce morphisms:

\[
\begin{array}{l} \alpha_ {a}: [ e \star a, 1 ] \rightarrow e \star [ a, 1 ] \quad \beta_ {a}: [ e, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 1 ] \\ \delta_ {a}: [ e \star a, 1 ] \vee [ a, 1 ] \rightarrow e \star ([ a, 2 ]) \quad \epsilon_ {a}: [ [ 2 ] \bar {\otimes} a, 1 ] \rightarrow e \star ([ a, 2 ]) \\ \end{array}
\]

where \([2] \bar{\otimes} a\) and \([e \star a, 1] \vee [a, 1]\) are the following pushouts:

![img-133.jpeg](img-133.jpeg)

![img-134.jpeg](img-134.jpeg)

150

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

Moreover there are commutative diagrams:

![img-135.jpeg](img-135.jpeg)

![img-136.jpeg](img-136.jpeg)

![img-137.jpeg](img-137.jpeg)

![img-138.jpeg](img-138.jpeg)

![img-139.jpeg](img-139.jpeg)

![img-140.jpeg](img-140.jpeg)

which induce commutative diagrams:

(1):

![img-141.jpeg](img-141.jpeg)

![img-142.jpeg](img-142.jpeg)

(3):

![img-143.jpeg](img-143.jpeg)

![img-144.jpeg](img-144.jpeg)

(5):

![img-145.jpeg](img-145.jpeg)

![img-146.jpeg](img-146.jpeg)

Definition 3.3.3.3. Let \( b \) be an object of \( A \) and \( x: a \to b \), \( x': a' \to b \) two morphisms. The element \( b \) is \( n \)-relying on \( x \) if for any \( k \geq -1 \), the following square is homotopy cocartesian:

![img-147.jpeg](img-147.jpeg)

151

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

The element \( b \) is \( n \)-relying on \( x \) and \( x' \) if for any \( k \geq -1 \), the following square is homotopy cocartesian:

\[
\begin{array}{c} [ k ] \star a \amalg [ k ] \star a ^ {\prime} \longrightarrow [ k ] \star b \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star a) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star a ^ {\prime}) \longrightarrow \tau_ {n + k + 1} ^ {i} ([ k ] \star b) \end{array}
\]

3.3.3.4. We recall that we denote by  \( C_{mk} \)  the marked Segal A-precategory associated to a stratified Segal A-precategory C. The canonical inclusion  \( C \to C_{mk} \)  is denoted  \( r_{C} \)  and is an acyclic cofibration according to he proposition 2.1.2.9. These notions and notations are defined in paragraph 3.3.2.1. The fact that will be used the most with the marked Segal A-precategory is their right lifting property with respect to morphisms of shape  \( [\tau_{n}^{i}(a), \Lambda^{1}[2]] \cup [a, 2] \to [\tau_{n}^{i}(a), 2] \) . This fact will be used freely.

Definition 3.3.3.5. Let C be a Segal A-precategory. We define the relation  \( \geq_{n} \)  on morphisms of shape  \( [a,1]\to C \)  for a verifying  \( \tau_{n}^{i}a=a \) , as the smallest reflexive and transitive relation such that  \( (x:[a,1]\to C)\geq_{n}(x':[a',1]\to C) \)  whenever one of the three following conditions is verified:

(1) The elements \( a \) and \( a' \) are equal and there exists a lifting the following diagram:

![img-148.jpeg](img-148.jpeg)

(2) The elements \( a \) and \( a' \) are equal and there exists a lifting in the following diagram:

![img-149.jpeg](img-149.jpeg)

(3) There exists an element \( b \) which is \( (n - 1) \)-relying on \( a \to b \) and dotted arrows in

152

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

the following diagram:

![img-150.jpeg](img-150.jpeg)

Definition 3.3.3.6. We also set $$(\bar{x} : [\bar{a}, 1] \to C, \bar{x}' : [\bar{a}', 1] \to C) \geq_n \bar{x}'' : [\bar{a}'', 1] \to C$$ if there exists three elements $$x : [a, 1] \to C$$, $$x' : [a', 1] \to C$$ and $$x'' : [a'', 1] \to C$$ such that $$\bar{x} \geq_n x$$, $$\bar{x}' \geq_n x'$$, $$x'' \geq_n \bar{x}''$$ and one of the two following conditions is verified:

(1) The elements $$a$$, $$a'$$ and $$a''$$ are equal and there exists a dotted arrow:

![img-151.jpeg](img-151.jpeg)

(2) There exists an element $$b$$ which is $$(n - 1)$$-relying on $$a \to b$$ and $$a' \to b$$ and dotted arrows in the following diagram:

![img-152.jpeg](img-152.jpeg)

Proposition 3.3.3.7. Let $$C$$ be a stratified Segal $$A$$-precategory and $$x : [a, 1] \to C$$, $$y : [a', 1] \to C$$ two morphisms such that $$x \geq_n y$$. The morphism

$$C \coprod_{[a,1]} \tau_n^i([a, 1]) \to \tau_n^i([a', 1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a, 1])$$

is an acyclic cofibration.

153

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. By two out of three, we can suppose without loss of generality that C is already a marked Segal A-precategory. We suppose first that x and y fulfill one of the three cases of definition 3.3.3.5. The following square is then homotopy cartesian:

![img-153.jpeg](img-153.jpeg)

As the cocartesian square:

![img-154.jpeg](img-154.jpeg)

is also homotopy cocartesian, this implies that

\[
C \coprod_ {[ a, 1 ]} \tau_ {n} ^ {i} ([ a, 1 ]) \rightarrow \tau_ {n} ^ {i} ([ a ^ {\prime}, 1 ]) \coprod_ {[ a ^ {\prime}, 1 ]} C \coprod_ {[ a, 1 ]} \tau_ {n} ^ {i} ([ a, 1 ])
\]

is an acyclic cofibration. Suppose now that there exists a family of morphisms  \( (x_{k} : [a_{k}, 1])_{k \leq m} \to C \)  such that  \( x_{0} = x \) ,  \( x_{m} = y \)  and for any k,  \( x_{k} \)  and  \( x_{k+1} \)  fulfill one of the three cases of definition 3.3.3.5. We then have two homotopy cocartesian squares:

![img-155.jpeg](img-155.jpeg)

As before, this implies that

\[
C \coprod_ {[ a, 1 ]} \tau_ {n} ^ {i} ([ a, 1 ]) \to C \coprod_ {\coprod_ {k \leq m} [ a _ {k}, 1 ]} \coprod_ {k \leq m} \tau_ {n} ^ {i} [ a _ {k}, 1 ]
\]

and

\[
\tau_ {n} ^ {i} ([ a ^ {\prime}, 1 ]) \coprod_ {[ a ^ {\prime}, 1 ]} C \coprod_ {[ a, 1 ]} \tau_ {n} ^ {i} ([ a, 1 ]) \to C \coprod_ {\coprod_ {k \leq m} [ a _ {k}, 1 ]} \coprod_ {k \leq m} \tau_ {n} ^ {i} [ a _ {k}, 1 ]
\]

are acyclic cofibrations. By two out of three, this implies the result.

One can show similarly:

Proposition 3.3.3.8. Let C be a stratified Segal A-precategory, and  \( x : [a,1] \to C \) ,  \( y : [a',1] \to C \)  and  \( z : [a'',1] \to C \)  three morphisms such that  \( (x,y) \geq_{n} z \) . The morphism

\[
\tau_ {n} ^ {i} ([ a ^ {\prime}, 1 ]) \coprod_ {[ a ^ {\prime}, 1 ]} C \coprod_ {[ a, 1 ]} \tau_ {n} ^ {i} ([ a, 1 ]) \to \tau_ {n} ^ {i} ([ a ^ {\prime}, 1 ]) \coprod_ {[ a ^ {\prime}, 1 ]} C \coprod_ {[ a, 1 ]} \tau_ {n} ^ {i} ([ a, 1 ]) \coprod_ {[ a ^ {\prime \prime}, 1 ]} \tau_ {n} ^ {i} ([ a ^ {\prime \prime}, 1 ])
\]

is an acyclic cofibration.

154

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

Lemma 3.3.3.9. Let n be a non null integer and a an element such that $\tau_{n}^{i}(a)=a$. The object $[2]^{2}\otimes a$ is n-relying on $d^{1}\bar{\otimes}a:e\star a\to[2]^{2}\bar{\otimes}a$.

Proof. As the morphism $d^{1}\bar{\otimes}a:e\star a\to[2]^{2}\bar{\otimes}a$ is a weak equivalence, so are the horizontal morphisms of the following diagram:

$$\begin{array}{c} [ k ] \star e \star a \xrightarrow {\sim} [ k ] \star ([ 2 ] ^ {2} \bar {\otimes} a) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star e \star a) \xrightarrow {\sim} \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] ^ {2} \bar {\otimes} a)) \end{array}$$

As the vertical morphisms are cofibrations, this implies that this square is homotopy cocartesian.

Lemma 3.3.3.10. Let n be a non null integer and a an element such that $\tau_{n}^{i}(a)=a$. The object $[2]\bar{\otimes}a$ is n-relying on $d^{0}\otimes a:[1]\otimes a\to[2]\bar{\otimes}a$ and $d^{2}\otimes a:e\star a\to[2]\otimes a$. Moreover, $[2]\bar{\otimes}a\coprod_{d^{0}\otimes a}\tau_{n}^{i}([1]\otimes a)$ (resp. $[2]\bar{\otimes}a\coprod_{d^{2}\bar{\otimes}a}\tau_{n}^{i}(e\star a)$) is n-relying on $d^{2}\otimes a$ (resp. $d^{0}\bar{\otimes}a$).

Proof. Consider the following diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star (\Lambda^ {1} [ 2 ] \otimes a) \xrightarrow {\sim} [ k ] \star ([ 2 ] \otimes a) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star (\Lambda^ {1} [ 2 ] \otimes a)) \not \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \end{array}$$

The left square is cocartesian and so homotopy cocartesian. Horizontal morphisms of the right square are weak equivalences, so this square is also homotopy cocartesian. The outer square is then homotopy cocartesian and this implies that $[[2]\otimes a,1]$ is n-relying on $d^0\otimes a$ and $d^2\otimes a$. We then have a diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \bar {\otimes} a) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \bar {\otimes} a)) \end{array}$$

where the two squares are homotopy cocartesian and so is the outer one. This implies the first assertion and the two others follow easily.

Lemma 3.3.3.11. Let n be an integer strictly superior to 1 and a such that $\tau_{n}^{i}(a)=a$. We consider the projection $\pi:[a,2]\to[a,1]\vee[\tau_{n-1}^{i}(a),1]$ and $\pi':[a,2]\to[\tau_{n-1}^{i}(a),1]\vee[a,1]$. We then have inequalities

$$e \star \pi \circ \epsilon_ {a} \circ [ d ^ {0} \otimes a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ]$$

and

$$e \star \pi^ {\prime} \circ \epsilon_ {a} \circ [ d ^ {2} \bar {\otimes} a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ].$$

155

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. Using the diagram (6).3.3.3.2 we get a diagram

![img-156.jpeg](img-156.jpeg)

The morphism \(r_{e\star ([a,1]\vee [\tau_{n - 1}^i (a),1])}\circ e\star \pi \circ \epsilon_a\) then factors through \([ [2]\bar{\otimes} a\coprod_{d^2\otimes a}\tau_n^i (e\star a),1]\). According to lemma 3.3.3.10, we then get the first inequalities.

For the second inequality, using the diagrams (3).3.3.3.2 and (5).3.3.3.2, we have a diagram:

![img-157.jpeg](img-157.jpeg)

This implies that \(r_{e\star ([\tau_{n - 1}^i (a),1]\vee [a,1])}\circ e\star \pi '\circ e\star [a,d^2 ]\circ \alpha_a\) factors through \([\tau_n^i (e\star a),1]\). The morphism \(r_{e\star ([\tau_{n - 1}^i (a),1]\vee [a,1])}\circ e\star \pi \circ \epsilon_a\) then factors through \([ [2]\otimes a\coprod_{d^0\otimes a}\tau_n^i ([1]\otimes a),1]\). According to lemma 3.3.3.10, we then get the second inequality.

Lemma 3.3.3.12. Let \( n \) be an integer strictly superior to 1 and \( a \) such that \( \tau_n^i (a) = a \). We then have \( \delta_a\circ [e\star a,d^2 ]\geq_{n + 1}\delta_a\circ [[1]\otimes a,d^1 ] \).

Proof. There is a diagram:

![img-158.jpeg](img-158.jpeg)

156

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

As the morphism $[[1] \otimes a, 1] \vee [a, 1] \to [e \star a, 1] \vee [a, 1]$ factors through $[[1] \otimes a, 1] \vee [\tau_n^i([1] \otimes a), 1]$, we get the desired inequality.

**Proposition 3.3.3.13.** *Let $a$ be an object such that $\tau_n^i(a) = a$. Let $x : [a, 1] \to C, y : [a', 1] \to C$ be two morphisms, such that $x \ge_n y$, then if we denote by $\bar{x} := e \star x \circ \alpha_a$ and $\bar{y} := e \star y \circ \alpha_{a'}$, we have $\bar{x} \ge_{n+1} \bar{y}$.*

*Proof.* First, we suppose that we are in the first case of the definition 3.3.3.5. We can then suppose without loss of generality that $C = [a, 1] \vee [\tau_{n-1}^i(a), 1]$. We denote by $\pi$ the projection of $[a, 2]$ on $[a, 1] \vee [\tau_{n-1}^i(a), 1]$. Using the diagrams (3).3.3.3.2, (4).3.3.3.2 and (5).3.3.3.2, we have a diagram:

$$\begin{array}{c} [[1] \otimes a, 1] \xrightarrow{[d^0 \otimes a, 1]} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^1 \bar{\otimes} a, 1]} [e \star a, 1] \\ [[1] \otimes a, d^1] \Big\downarrow \qquad \qquad \qquad \Big\downarrow \epsilon_a \qquad \qquad \qquad \Big\downarrow \alpha_a \\ [e \star a, 1] \vee [a, 1] \xrightarrow{\delta_a} e \star [a, 2] \xleftarrow{e \star [a, d^1]} e \star [a, 1] \\ [e \star a, d^2] \Big\uparrow \qquad \qquad \qquad e \star [a, d^2] \Big\uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e \star a, 1] \xrightarrow{\alpha_a} e \star [a, 1] \qquad \qquad \qquad e \star ([a, 1] \vee [\tau_{n-1}^i(a), 1]) \end{array}$$

Thanks to lemmas 3.3.3.11 and 3.3.3.12, this implies the result.

If we are in the second case of 3.3.3.5, we can suppose that $C = [\tau_{n-1}^i(a), 1] \vee [a, 1]$, and we note by $\pi'$ the projection from $[a, 2] \to [\tau_{n-1}^i(a), 1] \vee [a, 1]$. Using the diagrams (4).3.3.3.2 and (6).3.3.3.2, we have a diagram:

$$\begin{array}{c} [e \star a, 1] \xrightarrow{[d^2 \bar{\otimes} a, 1]} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^1 \bar{\otimes} a, 1]} [e \star a, 1] \\ \alpha_a \Big\downarrow \qquad \qquad \qquad \Big\downarrow \epsilon_a \qquad \qquad \qquad \Big\downarrow \alpha_a \\ e \star [a, 1] \xrightarrow{e \star [a, d^0]} e \star [a, 2] \xleftarrow{e \star [a, d^1]} e \star [a, 1] \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star ([\tau_{n-1}^i(a), 1] \vee [a, 1]) \end{array}$$

Thanks to lemmas 3.3.3.11, this implies the result.

If we are in the third case, it is a direct consequence of the naturality of $\alpha$, of the definition of $n$-reliability and of the fact that $(e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}}$ as remarked in 3.3.2.1.

**Proposition 3.3.3.14.** *Let $x : [a, 1] \to C$, $y : [a', 1] \to C$ and $z : [a'', 1]$ be three morphisms, such that $(x, y) \ge_n z$, then if we denote by $\bar{x} := e \star x \circ \alpha_a$, $\bar{y} := e \star y \circ \alpha_{a'}$ and $\bar{z} := e \star z \circ \alpha_{a''}$, we have $(\bar{x}, \bar{y}) \ge_{n+1} \bar{z}$.*

157

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. Suppose first that we are in the first case of the definition 3.3.3.6. We can then suppose without loss of generality that \( C = [a,2] \). We define \( \tilde{x} := \epsilon_a \circ [d^0 \otimes a,1] \). Diagram (6).3.3.3.2 and lemma 3.3.3.11 imply that \( (\tilde{x},\bar{y}) \geq_{n+1} \bar{z} \). Eventually, diagrams (3).3.3.3.2 and (5).3.3.3.2 induce a diagram:

\[
\begin{array}{c} [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {2} ]} [ e \star a, 1 ] \vee [ a, 1 ] \xleftarrow {[ [ 1 ] \otimes a , d ^ {1} ]} [ [ 1 ] \otimes a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {2} ] ]{} e \star [ a, 2 ] \xleftarrow [ \epsilon_ {a} ]{} [ [ 2 ] \bar {\otimes} a, 1 ] \end{array}
\]

wich implies that \(\bar{x} \geq_{n+1} \tilde{x}\).

If we are in the second case of the definition, it is a direct consequence of the naturality of  \( \alpha \) , of the definition of n-reliability and of the fact that  \( (e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}} \)  as remarked in paragraph 3.3.2.1.

Lemma 3.3.3.15. For any \(a\) such that \(\tau_{n}^{i}a = a\) and \(x:[a,1]\to C\), if we denote by \(\bar{x} := e\star x\circ d^0\star [a,1]\) and \(\tilde{x} := e\star x\circ \alpha_a\circ [d^0\star a,1]\), then \(\bar{x}\geq_{n + 1}\tilde{x}\).

Proof. Using the diagrams (1).3.3.3.2 and (2).3.3.3.2, we have a diagram:

\[
\begin{array}{c} [ a, 1 ] \xrightarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \\ [ a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \alpha_ {a} \\ [ e, 1 ] \vee [ a, 1 ] \xrightarrow {\beta_ {a}} e \star [ a, 1 ] \xrightarrow {e \star x} C \\ [ a, d ^ {0} ] \Big \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ a, 1 ] \end{array}
\]

which implies the desired inequality.

3.3.3.16. We now use these results to show that the thinness extensions are weak equivalences. We define by induction the morphism  \( \iota_{n}:[[n-1],1]\to[n] \)  where  \( \iota_{2}:=\alpha_{[0]} \)  and  \( \iota_{n+1}:=e\star\iota_{n}\circ\alpha_{[n-1]} \) .

We can easily show by induction that \([n]\) is a colimit of terms which are all invariant under \(\tau_{n - 1}^{i}\) except the one corresponding to \(\iota_{n}\). For any \(n\) we then have a pushout square:

\[
\begin{array}{c} [ [ n - 1 ], 1 ] \xrightarrow {\iota_ {n}} [ n ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ [ n - 1 ] _ {t}, 1 ] \xrightarrow {\iota} [ n ] _ {t} \end{array}
\]

Lemma 3.3.3.17. For any \( n \) and for any \( k < n \), such that \( k \neq n - 2 \), we have inequalities \( d^k \circ \iota_{n-1} \geq_{n-1} \iota_n \circ [d^k, 1] \) and \( (d^n \circ \iota_{n-1}, d^{n-2} \circ \iota_{n-1}) \geq_{n-1} \iota_n \circ [d^{n-2}, 1] \)

158

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

Proof. We start by showing the first inequality by induction on n. If n = 2, the only case is k = 1, and the two morphisms are equal.

Suppose now the result true at the stage n. If k > 0, we have

$$\begin{array}{l} d ^ { k } \circ \iota _ { n } = e \star d ^ { k - 1 } \circ e \star \iota _ { n - 1 } \circ \alpha _ { [ n - 2 ] } \\ \geq _ { n } \quad e \star \iota _ { n } \circ e \star [ d ^ { k - 1 } , 1 ] \circ \alpha _ { [ n - 2 ] } \quad ( \text { induction hypothesis and 3.3.3.13 } ) \\ = \quad e \star \iota _ { n } \circ \alpha _ { [ n - 1 ] } \circ [ e \star d ^ { k - 1 } , 1 ] \\ = \quad \iota _ { n + 1 } \circ \alpha _ { [ n - 1 ] } \circ [ d ^ { k } , 1 ] \end{array}$$

We still have to deal with the case k = 0. As $d ^ { 0 } : [ n ] \to [ n + 1 ]$ (resp $[ d ^ { 0 } , 1 ] : [ [ n - 1 ] , 1 ] \to [ [ n ] , 1 ] )$ is equal to $d ^ { 0 } \star [ n ]$ (resp. $[ d ^ { 0 } \star [ n - 1 ] , 1 ] )$), this is exactly the content of lemma 3.3.3.15.

For the second inequality, we proceed again by induction. We remark that this is true for n = 2. Suppose now the result true at the stage n. We have

$$\begin{array}{l} \left( d ^ { n + 1 } \circ \iota _ { n } , d ^ { n - 1 } \iota _ { n } \right) = \quad \left( e \star d ^ { n } \circ e \star \iota _ { n - 1 } \circ \alpha _ { [ n - 2 ] } , e \star d ^ { n - 2 } \circ e \star \iota _ { n - 1 } \circ \alpha _ { [ n - 2 ] } \right) \\ \geq _ { n - 1 } \quad e \star \iota _ { n } \circ e \star [ d ^ { n - 2 } , 1 ] \circ \alpha _ { [ n - 2 ] } \quad ( \text { induction hypothesis and 3.3.3.14 } ) \\ = \quad e \star \iota _ { n } \circ e \star \alpha _ { [ n - 1 ] } \circ [ e \star d ^ { n - 2 } , 1 ] \\ = \quad \iota _ { n + 1 } \circ [ d ^ { n - 1 } , 1 ] \end{array}$$

Lemma 3.3.3.18. Let $0 < k < n$ be two integers. We denote by $\tau ^ { k }$ the projection $[ n ] \to [ n ] ^ { k }$. We then have

$$\tau ^ { k } \circ \iota _ { n } \circ [ d ^ { k } , 1 ] \geq _ { n - 1 } \tau ^ { k } \circ d ^ { k } \circ \iota _ { n - 1 } .$$

Proof. We demonstrate the result by induction on n. For the initialization, the only case is n = 2 and k = 1, and is obvious. Suppose now the result true at the stage n, and let k > 1. We have inequalities:

$$\begin{array}{l} \tau ^ { k } \circ \iota _ { n + 1 } \circ [ d ^ { k } , 1 ] = e \star \tau ^ { k } \circ e \star \iota _ { n } \circ \alpha _ { [ n - 1 ] } \circ [ d ^ { k } , 1 ] \\ = \quad \star \tau ^ { k } \circ e \star \iota _ { n } \circ e \star [ d ^ { k - 1 } , 1 ] \circ \alpha _ { [ n - 2 ] } \\ \geq _ { n } \quad e \star \tau _ { k } \circ e \star d ^ { k - 1 } \circ e \star \iota _ { n - 1 } \circ \alpha _ { [ n - 2 ] } \quad ( \text { induction hypothesis and 3.3.3.13 } ) \\ = \quad \tau _ { k } \circ d ^ { k } \circ \iota _ { n } \end{array}$$

We still have to deal with the case k = 1. Using diagrams (1), (2), (4) and (5), of construction 3.3.3.2, we get a diagram:

$$\begin{array}{l} [ [ n - 1 ] , 1 ] \xrightarrow { \alpha _ { [ n - 2 ] } } e \star [ [ n - 2 ] , 1 ] \xrightarrow { e \star \iota _ { n - 1 } } [ n ] \\ [ d ^ { 2 } \tilde { \otimes } [ n - 2 ] , 1 ] \Biggl \downarrow \qquad \qquad \qquad \Biggl \downarrow e \star [ [ n - 1 ] , d ^ { 0 } ] \qquad \qquad \Biggl \downarrow d ^ { 1 } \\ [ [ 2 ] \tilde { \otimes } [ n - 2 ] , 1 ] \xrightarrow { e \star \pi \circ \iota _ { [ n - 2 ] } } e \star ( [ e , 1 ] \vee [ [ n - 2 ] , 1 ] ) \xrightarrow { e \star \beta _ { [ n - 1 ] } } [ n + 1 ] \xrightarrow { \tau ^ { 1 } } [ n + 1 ] ^ { 1 } \\ [ d ^ { 1 } \tilde { \otimes } [ n - 2 ] , 1 ] \Biggl \uparrow \qquad \qquad \qquad \Biggl \uparrow e \star [ [ n - 1 ] , d ^ { 1 } ] \qquad \qquad \Biggl \uparrow e \star \iota _ { n } \\ [ [ n - 1 ] , 1 ] \xrightarrow { \alpha _ { [ n - 2 ] } } e \star [ [ n - 2 ] , 1 ] \xrightarrow [ e \star [ d ^ { 0 } , 1 ] ] { } e \star [ [ n - 1 ] , 1 ] \end{array}$$

159

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

where  \( \pi \)  is the projection  \( [[n-2],2]\to[e,1]\vee[[n-2],1] \) . However, according to the diagrams (5) and (3) of 3.3.3.2, there is a diagram:

\[
\begin{array}{c} \left[ [ 1 ] \otimes [ n - 2 ], 1 \right] \xrightarrow {\left[ [ 1 ] \otimes [ n - 2 ] , d _ {1} ^ {1} \right]} [ e \star [ n - 2 ], 1 ] \vee \left[ [ n - 2 ], 1 \right] \xleftarrow {e \star [ n - 2 ] , d ^ {2}} [ e \star [ n - 2 ], 1 ] \\ [ d ^ {0} \otimes [ n - 2 ], 1 ] \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Biggl \downarrow \delta_ {[ n - 2 ]} \qquad \qquad \qquad \Biggl \downarrow \alpha_ {[ n - 2 ]} \\ \left[ [ 2 ] \bar {\otimes} [ n - 2 ], 1 \right] \xrightarrow {\epsilon_ {[ n - 2 ]}} \left[ [ n - 2 ], 2 \right] \xleftarrow {} e \star [ [ n - 2 ], 1 ] \\ \Biggl \downarrow e \star \pi \qquad \qquad \qquad \Biggl \downarrow \\ e \star ([ e, 1 ] \vee [ [ n - 2 ], 1 ]) \xleftarrow {} e \star [ e, 1 ] \\ \tau_ {1} \circ e \star \beta_ {[ n - 1 ]} \Biggl \downarrow \qquad \qquad \qquad \Biggl \downarrow \\ [ n + 1 ] ^ {1} \xleftarrow [ d ^ {3} \circ .. \circ d ^ {n + 1} ]{} [ 2 ] _ {t} \end{array}
\]

This implies that \([[2]\bar{\otimes}[n - 2],1]\to [n + 1]^k\to ([n + 1]^k)_{\mathrm{mk}}\) factors through \([[2]\bar{\otimes}[n - 2]\coprod_{d^0\otimes a}\tau_{n - 1}^t ([1]\otimes [n - 2]),1]\). We can then apply lemma 3.3.3.10.

Lemma 3.3.3.19. Let \(0 < k < n - 1\) be two integers. We denote by \(\tau^k\) the projection \([n] \to [n]^k\). We then have

\[
\left(\tau^ {k} \circ \iota_ {n} \circ [ d ^ {k - 1}, 1 ], \tau^ {k} \circ \iota_ {n} \circ [ d ^ {k + 1}, 1 ]\right) \geq_ {n - 1} \tau^ {k} \circ \iota_ {n} \circ [ d ^ {k}, 1 ]
\]

and

\[
\tau^ {n - 1} \circ \iota_ {n} \circ [ d ^ {n - 2}, 1 ] \geq_ {n - 1} \tau^ {k} \circ \iota_ {n} \circ [ d ^ {n - 1}, 1 ].
\]

Proof. By construction, for any \(a\), the morphism \([(2] \star a, 1] \to [2] \star [a, 1] \to [2]_t \star [a, 1]\) factors through \([(2]_t \star a, 1]\). By induction, this implies that the composite morphism \([(n-1], 1] \xrightarrow{\iota_n} [n] \to [n]^k\) factors through \([(n-1]^k, 1]\) for any \(k < n-1\). This implies the first assertion.

For the second one, note that  \( [[1], e] \to [2] \to [2]_{t} \)  factors through  \( [[1]_{t}, e] \) . By induction, this implies that the composite morphism  \( [[n-1], 1] \xrightarrow{\iota_{n}} [n] \to [n]^{n-1} \)  factors through  \( [[n-1]^{n-2}, 1] \)  which gives the second one. □

Proposition 3.3.3.20. For any \(0 \leq k \leq n\), the morphism \(([n]^k)' \to ([n]^k)''\) is a weak equivalence.

Proof. The case k = 0 and k = n are demonstrated in lemma 3.3.3.1. For the case  \( 0 < k < n \) , lemmas 3.3.3.17, 3.3.3.18 and 3.3.3.19 imply that if we denote by  \( \tau_{k} \)  the projection  \( [n] \to [n]^{k} \) , we have an inequality:  \( (\tau_{k} \circ d^{k-1} \circ \iota_{n-1}, \tau_{k} \circ d^{k+1} \circ \iota_{n-1}) \geq_{n-1} \tau_{k} \circ d^{k} \circ \iota_{n-1} \) . Together with the proposition 3.3.3.8, this implies that the following square is homotopy cartesian:

\[
\begin{array}{c} [ n - 1 ] \cup [ n - 1 ] \xrightarrow {d ^ {k + 1} \cup d ^ {k - 1}} [ n ] ^ {k} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ [ n - 1 ] _ {t} \cup [ n - 1 ] _ {t} \longrightarrow ([ n ] ^ {k}) ^ {\prime \prime} \end{array}
\]

160

3.3. QUILLEN ADJUNCTION WITH tPsh(Δ)

The morphism \(([n]^k)' \to ([n]^k)''\) is then a weak equivalence.

#### 3.3.4 Saturation extensions

Let \(\Lambda[3]^{eq} \to [3]^{eq}\) be the entire inclusion generated by \(Im(d^3) \cup Im(d^0) \subset [3]\). This inclusion fits in the following sequence:

![img-159.jpeg](img-159.jpeg)

This inclusion is then a weak equivalence according to propositions 3.3.2.15 and 3.3.3.20. Now, note that we have a pushout:

![img-160.jpeg](img-160.jpeg)

As the left vertical morphism is a weak equivalence, so is the right one. Let \(\Lambda[3]^{\sharp} \to [3]^{\sharp}\) be the entire inclusion generated by \(Im(d^3) \cup Im(d^0) \subset [3]\). Using the same reasoning, we show that this cofibration is acyclic and that there is a weak equivalence \(\Lambda[3]^{\sharp} \to [e, [3]^{\sharp}]\). We then have a commutative square:

![img-161.jpeg](img-161.jpeg)

where all arrows labelled by  \( \sim \)  are weak equivalences. By two out of three, this implies that  \( [3]^{eq} \rightarrow [3]^{\sharp} \)  is a weak equivalence. Combined with the lemma 3.3.1.9, this implies the following proposition:

Proposition 3.3.4.1. For any \( n \geq -1 \), the morphism \( [n] \star [3]^{eq} \to [n] \star [3]^{\sharp} \) is an acyclic cofibration.

Theorem 3.3.4.2. The stratified cosimplicial object constructed in paragraph 3.3.1.7 induces a Quillen adjunction \(\mathrm{tPsh}(\Delta)^{\omega}\to \mathrm{tSeg}(A)\).

Proof. It is a direct consequence of theorem 2.2.1.6 and propositions 3.3.2.15, 3.3.3.20, and 3.3.4.1. \(\square\)

161

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

### 3.4 The case  \( A := \operatorname{tPsh}(\Delta)^{n} \)

For \( n \in \mathbb{N} \cup \{\omega\} \), we denote by \( \mathrm{tPsh}(\Delta)^n \) the category of stratified simplicial set endowed with the model structure for \( n \)-complicial set given in theorem 2.2.1.6. As remarked in example 3.1.3.5, these model categories are Gray modules. The functor \( \mathrm{tPsh}(\Delta) \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \) defined in 3.3.1.7 is left Quillen according to theorem 3.3.4.2. It was noted in paragraph 3.3.3.16 that for \( k > 0 \), \( [k] \to [k]_t \) fits in the following cocartesian square:

![img-162.jpeg](img-162.jpeg)

The functor \(\mathrm{tPsh}(\Delta) \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)\) then sends \([k] \to [k]_t\) to an acyclic cofibration for \(k > n + 1\), and then induces a left Quillen functor

\[
i ^ {n + 1}: \mathrm{tPsh} (\Delta) ^ {n + 1} \rightarrow \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n}) \tag {3.4.0.1}
\]

#### 3.4.1 Comparison with \((0,\omega)\)-cat

We denote by

\[
\mathrm{R}: \mathrm{tPsh} (\Delta) ^ {\omega} \xrightarrow [ \leftarrow ]{\perp} (0, \omega) \text {-cat}: \mathrm{N}
\]

the adjunction between stratified simplicial sets and  \( (0,\omega) \) -categories described in section 2.2.4. For an  \( (0,\omega) \) -category C and an integer n, the  \( (0,\omega) \) -category  \( [C,n] \)  is defined as the colimit of the following diagram

![img-163.jpeg](img-163.jpeg)

This induces an adjunction

\[
\mathrm{R}: \mathrm{tSeg} (\mathrm{tPsh} (\Delta)) \xrightarrow [ \leftarrow ]{\perp} (0, \omega) \text {-cat}: \mathrm{N}
\]

where the left adjoint sends  \( [K,n] \)  to  \( [\mathrm{R}(K),n] \)  and  \( [e,1]_{t} \)  on [0].

Lemma 3.4.1.1. For any \((0,\omega)\)-category \(C\), the canonical morphism

\[
[ \mathrm{N} C, 1 ] \rightarrow \mathrm{N} [ C, 1 ]
\]

is an isomorphism.

162

3.4. THE CASE $A := \mathrm{tPsh}(\Delta)^n$

Proof. Let $K$ be a stratified simplicial set, $n$ an integer. By construction, we have two cartesian squares

$$\begin{array}{c} \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \times \mathrm{Hom}_{\mathrm{tPsh}(\Delta)}(K, \mathrm{N}C) \longrightarrow \mathrm{Hom}_{\Delta}([n], [1]) \times \mathrm{Hom}_{\mathrm{tPsh}(\Delta)}(K, \mathrm{N}C) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \longrightarrow \mathrm{Hom}_{\mathrm{tSeg}(\mathrm{tPsh}(\Delta))}([K, n], [\mathrm{N}C, 1]) \\ \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \times \mathrm{Hom}_{(0,\omega)\text{-cat}}(\mathrm{R}(K), C) \longrightarrow \mathrm{Hom}_{\Delta}([n], [1]) \times \mathrm{Hom}_{(0,\omega)\text{-cat}}(\mathrm{R}(K), C) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{\epsilon \in \{0,1\}} \mathrm{Hom}_{\Delta}([n], \{\epsilon\}) \longrightarrow \mathrm{Hom}_{(0,\omega)\text{-cat}}(\mathrm{R}([K, n]), [C, 1]) \end{array}$$

which directly concludes the proof.

Lemma 3.4.1.2. Let $C$ be an $(0, \omega)$-category and $n$ an integer. There is a canonical commutative square in $(0, \omega)$-cat:

$$\begin{array}{c} \coprod_{k \leq n} \mathrm{colim}_{\Delta_{/\{k\}}^2}[[n_0] \otimes C, 1] \vee [C, n_1] \longrightarrow \mathrm{colim}_{\Delta_{/\{n\}}^2}[[n_0] \otimes C, 1] \vee [C, n_1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{k \leq n} \mathrm{colim}_{\Delta_{/\{k\}}^2}[[n_0], 1] \vee [n_1] \longrightarrow 1 \star [C, n] \end{array}$$

natural in $C : (0, \omega)$-cat and $[n] : \Delta$.

Proof. In this proof, we use the Steiner theory recalled in section 1.2.1. It is sufficient to show the assertion when $C$ is a globular form, and then a fortiori, an $(0, \omega)$-category with an atomic and loop free basis. Using the equivalence between $(0, \omega)$-cat$_\mathrm{B}$ and ADC$_\mathrm{B}$ given in 1.2.1.23 and the equivalences

$$(K \otimes L)^{op} \sim L^{op} \otimes K^{op} \quad (K \otimes L)^{co} \sim L^{co} \otimes K^{co} \quad (1 \star K)^{op} \sim K^{op} \star 1$$

provided by propositions A.20 and 6.10 of [AM20], it is sufficient to construct for every augmented direct complex $K$ a natural commutative square:

$$\begin{array}{c} \coprod_{k \leq n} \mathrm{colim}_{[n_1] \star [n_0] \to \{k\}}[K, n_1] \vee [K \otimes \lambda[n_0], 1] \longrightarrow \mathrm{colim}_{[n_1] \star [n_0] \to [n]}[K, n_1] \vee [K \otimes \lambda[n_0], 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{k \leq n} \mathrm{colim}_{[n_1] \star [n_0] \to \{k\}} \lambda[n_1] \vee [\lambda[n_0], 1] \longrightarrow [K, n] \star 1 \end{array}$$

163

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

For an element \( f:[n_0] \star [n_1] \to [n] \) of \( \Delta_{/[n]}^2 \), we consider the morphism \( \phi_f:[K,n_1] \vee [K \otimes \lambda[n_0],1] \to [K,n] \star 1 \) as the unique morphism fulfilling

\[
\phi_ {f} ([ x, v _ {i, i + 1} ]) := [ x, v _ {f _ {0} (i), f _ {0} (i) + 1} ] \star \emptyset + \dots + [ x, v _ {f _ {0} (i) - 1, f _ {0} (i + 1)} ] \star \emptyset
\]

\[
\phi_ {f} ([ x \otimes v _ {i}, 1 ]) := 0
\]

\[
\phi_ {f} ([ x \otimes v _ {i, i + 1}, 1 ]) := [ x, v _ {f _ {1} (i), f _ {1} (i) + 1} ] \star 1 + \dots + [ x, v _ {f _ {1} (i) - 1, f _ {1} (i + 1)} ] \star 1
\]

for \( x \) an element of \( K \) and where we denote by \( f_0 \) and \( f_1 \) the induced morphisms \( [n_0] \to [n_0] \star [n_1] \to [n] \) and \( [n_1] \to [n_0] \star [n_1] \to [n] \).

Peforming this for any such \( f:[n_0] \star [n_1] \to [n] \) of \( \Delta_{/[n]}^2 \), this induces a morphism

\[
\psi : \underset {\Delta_ {/ [ n ]} ^ {2}} {\operatorname{colim}} [ [ n _ {0} ] \otimes a, 1 ] \vee [ a, n _ {1} ] \to 1 \star [ a, n ]
\]

whose restriction to \(\coprod_{k\leq n}\mathrm{colim}_{\Delta_{/ (k)}^2}[[n_0]\otimes a,1]\vee [a,n_1]\) factors through \(\coprod_{k\leq n}\mathrm{colim}_{\Delta_{/ (k)}^2}[[n_0],1]\vee [1,n_1]\) and this concludes the proof.

Lemma 3.4.1.3. There is an invertible natural transformation \(\mathrm{R}(e\star_{-})\to 1\star \mathrm{R}(\_)\) that firs in a commutative square

\[
\begin{array}{c} \operatorname{R} (\emptyset \star_ {-}) \longrightarrow \operatorname{R} (e \star_ {-}) \\ \stackrel {{i d}} {{\downarrow}} \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \emptyset \star \operatorname{R} (_ {-}) \longrightarrow 1 \star \operatorname{R} (_ {-}) \end{array}
\]

Proof. The lemma 3.4.1.2 provides such natural transformation. As R sends weak equivalences to isomorphisms, it is sufficient to show that  \( \mathrm{R}(e \star [K,1]) \to 1 \star [\mathrm{R}(K),1] \)  is an equivalence, which directly follows from the explicit description of these two objects provided by proposition 3.2.2.6 and by the example 3.2.2.4. □

Proposition 3.4.1.4. The following triangle commutes up to an invertible natural transformation

\[
\begin{array}{c} \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n}) \\ \xrightarrow {i ^ {n + 1}} \quad \Big \downarrow_ {\mathrm{R}} \\ \mathrm{tPsh} (\Delta) ^ {n + 1} \xrightarrow [ \mathrm{R} ]{} (0, \omega) \text {-cat} \end{array}
\]

For any integer \( k \leq n + 1 \), the induced morphism \( i^{n+1}(\mathrm{N}\mathbf{D}_k) \to \mathrm{N}(\mathbf{D}_k) \) is a weak equivalence.

Proof. It is sufficient to show the result for  \( n := \omega \) . The lemma 3.4.1.3 provides an invertible transformation  \( \phi : (\mathrm{R} i^{\omega})_{|\Delta} \to \mathrm{R}_{|\Delta} \)  which is natural when restricted to the full

164

3.4. THE CASE $A := \mathrm{tPsh}(\Delta)^n$

subcategory of $\Delta$ whose morphisms are the monomorphisms. The lemma 2.4.4.12 then implies that $\phi : (\mathrm{R} i^\omega)_{|\Delta} \to \mathrm{R}_{|\Delta}$ is natural. As all these functors commute with the intelligent truncations, we can extend it to a natural transformation $\phi : (\mathrm{R} i^\omega)_{|t\Delta} \to \mathrm{R}_{|t\Delta}$. Eventually, as all theses morphisms preserves colimits, we can extend $\phi$ to an invertible natural transformation $\phi : \mathrm{R} i^\omega \to \mathrm{R}$.

We now turn our attention to the second assertion. We define the functor $\Sigma^\circ : \mathrm{tPsh}(\Delta) \to \mathrm{tPsh}(\Delta)$ that sends a stratified simplicial set $K$ onto the following pushout:

![img-164.jpeg](img-164.jpeg)

Remark that we have a canonical equivalence

$$(\Sigma^\circ X)^{op} \sim \Sigma^* X^{op}$$

where $\Sigma^*$ is the functor defined in paragraph 2.2.2.16. As the nerve commutes with the op-dualities, and as globes are invariant under it, a repeated application of [OR22, theorem 3.22] imply that the following canonical morphism between stratified simplicial sets

$$(\Sigma^\circ)^k[0] \to \mathrm{N}(\mathbf{D}_k)$$

is an acyclic cofibration. Furthermore, proposition 3.2.3.4 provides a weak equivalence

$$i^{n+1}(\Sigma^\circ K) \to \Sigma^\circ K.$$

A direct induction then induces a weak equivalence

$$i^{n+1}((\Sigma^\circ)^k[0]) \to (\Sigma^\circ)^k[0]$$

Otherwise, remark that by construction, $\Sigma^\circ[K, 1] := [[0] \diamond K \coprod_K[0], 1]$. The weak equivalence $[0] \diamond K \to [0] \star K$ provided by proposition 2.2.2.15 induces a weak equivalence

$$\Sigma^\circ[K, 1] \to [\Sigma^\circ K, 1].$$

As $\Sigma^\circ[0] = [[0], 1]$, a direct induction induces a weak equivalence

$$(\Sigma^\circ)^k[0] \to [(\Sigma^\circ)^{k-1}([0]), 1].$$

All put together, and using lemma 3.4.1.1, this induces two acyclic cofibrations

$$\begin{array}{l} \psi_k : \ i^{n+1}((\Sigma^\circ)^k[0]) \xrightarrow{\sim} \mathrm{N} \mathbf{D}_k \\ \psi'_k : \ i^{n+1}((\Sigma^\circ)^k[0]) \xrightarrow{\sim} (\Sigma^\circ)^k[0] \xrightarrow{\sim} [(\Sigma^\circ)^{k-1}[0], 1] \xrightarrow{\sim} [\mathrm{N} \mathbf{D}_{k-1}, 1] \cong \mathrm{N} \mathbf{D}_k \end{array}$$

165

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

To concludes, one have to show that the induces diagram

![img-165.jpeg](img-165.jpeg)

commutes. By adjunction, this is sufficient to show that the diagram

![img-166.jpeg](img-166.jpeg)

commutes. We claim that  \( R N D_{k} \)  has no non-trivial automorphisms. This directly implies the results as R sends acyclic cofibrations to isomorphisms.

It then remains to show that  \( RN D_{k} \)  has no non-trivial automorphisms. If k = 0, this is trivial as  \( RN D_{0} \cong D_{0} \) . We suppose now that k > 0. As R commutes with the suspension and sends acyclic cofibration to isomorphism, the lemma 3.4.1.1 and a repeated application of the theorem 2.2.4.2 imply that the morphism

\[
\begin{array}{l} \mathbf {D} _ {k} = [ \mathbf {D} _ {k - 1}, 1 ] \\ \cong [ \Sigma^ {k - 1} \mathrm{RND} _ {0}, 1 ] \\ \cong \mathrm{R} [ \Sigma^ {k - 1} \mathrm{ND} _ {0}, 1 ] \\ \rightarrow \mathrm{R} [ \mathrm{N} \Sigma^ {k - 1} \mathbf {D} _ {0}, 1 ] \\ \cong \mathrm{RN} [ \Sigma^ {k - 1} \mathbf {D} _ {0}, 1 ] \\ = \mathrm{RND} _ {k} \\ \end{array}
\]

is an isomorphism. The result then follows from proposition 1.2.3.11 that states that \(\mathbf{D}_k\) has no non-trivial automorphisms.

#### 3.4.2 The other adjunction

We define the colimit preserving functor

\[
j: \mathrm{tSeg} (\mathrm{tPsh} (\Delta)) \rightarrow \mathrm{tPsh} (\Delta) \tag {3.4.2.1}
\]

sending \([K,n]\) to the pushout:

![img-167.jpeg](img-167.jpeg)

166

3.4. THE CASE \(A := \mathrm{tPsh}(\Delta)^n\)

and $[[0], 1]_t$ to $[1]_t$. As $_\boxtimes_-$ is a left Quillen bifunctor, and as $j([[0], 1]_t \to [0]) = [1]_t \to [0]$ and $j([[0], E^{\cong}] \to [[0], (E^{\cong})']) = E^{\cong} \to (E^{\cong})'$ are weak equivalences, the proposition 3.1.2.10 implies that the functor

$$
j^\omega : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^\omega) \to \mathrm{tPsh}(\Delta)^\omega
$$

is a left Quillen functor. By definition of the Gray pre-tensor given in [Ver08c, Definition 128], we remark that $j([[k], n] \to [[k]_t, n])$ is a pushout of a disjoint union of $[k + 1] \to [k + 1]_t$. This implies that for any $n \in \mathbb{N}$,

$$
j^{n+1} : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \to \mathrm{tPsh}(\Delta)^{n+1}
$$

is a left Quillen functor.

**Proposition 3.4.2.2.** *The following triangle commutes up to an invertible natural transformation:*

![img-168.jpeg](img-168.jpeg)

*For any integer $k \leq n + 1$, the induced morphism $j^{n+1}(\mathrm{N}\mathbf{D}_k) \to \mathrm{N}(\mathbf{D}_k)$ is a weak equivalence.*

*Proof.* The first assertion is a direct consequence of the definition of $\mathrm{R} : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \to (0, \omega)$-cat and the corollary 1.2.3.19. We denote $\phi : \mathrm{R}j^{n+1} \to \mathrm{R}$ the corresponding invertible natural transformation.

For the second assertion, remark that the case $k = 0$ is trivial, and for $k > 0$, lemma 3.4.1.1, theorem 2.2.4.2 and the definition of $j^{n+1}$ induce a weak equivalence

$$
\psi_k : j^{n+1}(\mathrm{N}\mathbf{D}_k) \cong j^{n+1}([\mathrm{N}\mathbf{D}_{k-1}, 1]) = \Sigma \mathrm{N}\mathbf{D}_{k-1} \to \mathrm{N}[\mathbf{D}_{k-1}, 1] = \mathrm{N}\mathbf{D}_k
$$

To conclude, one have to show that $\phi_{\mathrm{N}\mathbf{D}_k}$ is equal to $\mathrm{R}\psi_k$. We claim that $\mathrm{R}\mathrm{N}\mathbf{D}_k$ has no non-trivial automorphisms. This directly implies the results as $\mathrm{R}$ sends acyclic cofibrations to isomorphisms.

It then remains to show that $\mathrm{R}\mathrm{N}\mathbf{D}_k$ has no non-trivial automorphisms. As $\mathrm{R}$ commutes with the suspension and sends acyclic cofibration to isomorphism, a repeated application of the theorem 2.2.4.2 implies that the morphism

$$
\mathbf{D}_k = \Sigma^k \mathbf{D}_0 \cong \Sigma^k \mathrm{R}\mathrm{N}\mathbf{D}_0 \cong \mathrm{R}\Sigma^k \mathrm{N}\mathbf{D}_0 \to \mathrm{R}\mathrm{N}\Sigma^k \mathbf{D}_0 \cong \mathrm{R}\mathrm{N}\mathbf{D}_k
$$

is an isomorphism. The result then follows from proposition 1.2.3.11 that states that $\mathbf{D}_k$ has no non-trivial automorphisms. $\square$

167

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

### 3.4.3 Complicial sets as a model of  \( (\infty,\omega) \) -categories

Proposition 3.4.3.1. For any \(n \in \mathbb{N} \cup \{\omega\}\), the composite

\[
j ^ {n + 1} \circ i ^ {n + 1}: \mathrm{tPsh} (\Delta) ^ {n + 1} \to \mathrm{tPsh} (\Delta) ^ {n + 1}
\]

is a Quillen equivalence.

Proof. Using theorem 2.2.4.2, and propositions 3.4.1.4 and 3.4.2.2, we have a zigzag of weak equivalences

\[
j ^ {\omega} \circ i ^ {\omega} (\mathbf {D} _ {n}) \rightarrow j ^ {\omega} \circ i ^ {\omega} (\mathrm{N} (\mathbf {D} _ {n})) \rightarrow \mathrm{N} (\mathbf {D} _ {n}) \leftarrow \mathbf {D} _ {n}
\]

natural in \( n \). The corollary 2.4.4.15 then provides a zigzag of weakly invertible natural transformations

\[
j ^ {\omega} \circ i ^ {\omega} \leftrightarrow i d _ {\mathrm{tPsh} (\Delta) ^ {\omega}}.
\]

This also induces for any integer n a zigzag of weakly invertible natural transformations

\[
j ^ {n + 1} \circ i ^ {n + 1} \leftrightarrow i d _ {\mathrm{tPsh} (\Delta) ^ {n + 1}}.
\]

□

Theorem 3.4.3.2. For \( n < \omega \), the model category \( \mathrm{tPsh}(\Delta)^n \) is a model of \( (\infty, n) \)-categories.

Proof. To demonstrate the theorem, we will proceed by induction. The initialization is exactly the theorem 2.14 of [BOR21]. Suppose now the result is true at the stage n. We can apply [BSP21, example 15.8] which implies that the  \( (\infty,1) \) -category represented by  \( \operatorname{Seg}(\operatorname{tPsh}(\Delta)^{n}) \)  is a model of  \( (\infty,n+1) \) -categories, and according to 3.1.2.10, so is  \( \operatorname{tSeg}(\operatorname{tPsh}(\Delta)^{n}) \) . Eventually, the proposition 3.4.1.4 and 3.4.2.2 imply that the functor

\[
i ^ {n + 1} \circ j ^ {n + 1}: \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n}) \to \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n})
\]

preserves globes up to homotopy. Proposition 15.10 of [BSP21] states that \( i^{n+1} \circ j^{n+1} \) is a Quillen equivalence, and proposition 3.4.3.1 implies that \( j^{n+1} \circ i^{n+1} \) is a Quillen equivalence. The functor \( i^{n+1} \) is then a Quillen equivalence, and \( \mathrm{tPsh}(\Delta)^{n+1} \) is a model of \( (\infty, n+1) \)-categories.

3.4.3.3. For an integer n, we consider the model structure on  \( \mathrm{Psh}_{\Delta}(\Theta_{n}) \)  (resp.  \( \mathrm{Psh}_{\Delta}(\Theta) \) ) obtained as the left Bousfield localization of the projective model structure along the set of map  \( W_{n} \)  (resp. W) defined in paragraph 1.1.2.14. For any  \( n < \omega \) , the inclusion  \( \Theta_{n} \to \Theta \)  induces a Quillen adjunction

\[
\iota^ {n}: \mathrm{Psh} _ {\Delta} (\Theta_ {n}) \xrightarrow [ \leftarrow ]{\perp} \mathrm{Psh} _ {\Delta} (\Theta): \tau_ {n} \tag {3.4.3.4}
\]

168

3.4. THE CASE $A := \mathrm{tPsh}(\Delta)^n$

3.4.3.5. Let $n \in \mathbb{N} \cup \{\omega\}$. We consider the functor

$$\Theta_n \times \Delta \to \mathrm{tPsh}(\Delta)$$

sending a pair $(a, [n])$ onto $\mathrm{N}(a) \times \tau_0^i([n])$. By left Kan extension, this induces an adjunction

$$L_n : \mathrm{Psh}_\Delta(\Theta_n) \xrightarrow{\perp} \mathrm{tPsh}(\Delta) : N_{L_n} \tag{3.4.3.6}$$

**Theorem 3.4.3.7** (Ozornova-Rovelli). *The adjunction*

$$L_n : \mathrm{Psh}_\Delta(\Theta_n) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)^n : N_{L_n}$$

*is a Quillen adjunction.*

*Proof.* This is [OR22, theorem 4.16].

**Remark 3.4.3.8.** The two authors demonstrate this result when $\mathrm{tPsh}(\Delta)$ is endowed with the model structure for $n$-complicial sets with $n < \omega$. However, their argument generalizes directly to the case $n = \omega$.

A direct induction using [OR22, theorem 3.22] implies that the left adjoint preserves globes.

**Proposition 3.4.3.9.** *For any $n \in \mathbb{N}$, the adjunction given in theorem 3.4.3.7 is a Quillen equivalence.*

*Proof.* This is an adjunction between two models of $(\infty, n)$-categories. As the left adjoint preserves globes up to homotopy, the result follows from [BSP21, proposition 15.10].

3.4.3.10. If $C$ is a model category, we denote by $C^{(\infty,1)}$ the corresponding $(\infty, 1)$-category.

**Lemma 3.4.3.11.** *For any integer $n$, the $(\infty, 1)$-functor*

$$\iota^n : (\mathrm{Psh}_\Delta(\Theta_n))^{(\infty,1)} \to (\mathrm{Psh}_\Delta(\Theta))^{(\infty,1)}$$

*is fully faithful.*

*Proof.* This is proposition 4.2.1.39.

**Lemma 3.4.3.12.** *For any integer $n$, the $(\infty, 1)$-functor*

$$\tau_n^i : (\mathrm{tPsh}(\Delta)^n)^{(\infty,1)} \to (\mathrm{tPsh}(\Delta)^\omega)^{(\infty,1)}$$

*is fully faithful.*

169

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. This is a direct consequence of the fact that  \( \mathrm{tPsh}(\Delta)^{n} \)  is the left Bousfield localization of  \( \mathrm{tPsh}(\Delta)^{\omega} \)  along morphisms  \( [m] \to [m]_{t} \)  for m > n. □

Lemma 3.4.3.13. The \((\infty,1)\)-functor \(L_{\omega}:(\mathrm{Psh}_{\Delta}(\Theta))^{(\infty,1)}\to (\mathrm{tPsh}(\Delta)^{\omega})^{(\infty,1)}\) is fully faithful.

Proof. We have to show that for any pair of \(\Theta\)-spaces \(X\) and \(Y\), the induced morphism of \(\infty\)-groupoids

\[
\mathrm{Hom} _ {(\mathrm{Psh} _ {\Delta} (\Theta)) ^ {(\infty , 1)}} (X, Y) \to \mathrm{Hom} _ {(\mathrm{tPsh} (\Delta) ^ {\omega}) ^ {(\infty , 1)}} (L _ {\omega} (X), L _ {\omega} (Y))
\]

is an equivalence. As every  \( \Theta \) -space is a  \( (\infty,1) \) -colimit of globular sums, which are themself  \( (\infty,1) \) -colimits of globes, we can suppose that X is of shape  \( D_{n} \) . In this case  \( D_{n} \)  is  \( \omega \) -small. As  \( L(\mathbf{D}_{n}) \)  has a finite presentation, given by the n-times interated suspension of [0], it is also  \( \omega \) -small.

Eventually, proposition 4.2.1.45 implies that every \(\Theta\)-spaces is a directed colimit of objects that are in the image of \(\iota_{n}\) for an integer \(n\). We can then restrict ourselves to the case where \(Y\) is in the image of \(\iota_{n}\). As we have an equivalences \(L_{\omega} \circ \iota_{n} \sim \tau_{n}^{i} \circ L_{n}\), the results follow from proposition 3.4.3.9, and lemmas 3.4.3.11 and 3.4.3.12.

Theorem 3.4.3.14. For any \(n \in \mathbb{N} \cup \{\omega\}\), the adjunction

\[
L _ {n}: \mathrm{Psh} _ {\Delta} (\Theta_ {n}) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta) ^ {\omega}: N _ {L _ {n}}
\]

is a Quillen equivalence. The two induced diagrams

![img-169.jpeg](img-169.jpeg)

![img-170.jpeg](img-170.jpeg)

commute up to homotopy.

Proof. If  \( n < \omega \) , the first assertion is a consequence of proposition 3.4.3.9. Suppose now that  \( n = \omega \) . The lemma 3.4.3.13 implies that the left adjoint is homotopically fully faithful. It then remains to show that the right adjoint is conservative. This is a direct consequence of the preservation of globes by  \( L_{\omega} \)  up to homotopy and theorem 2.4.2.9.

For the second assertion, it is sufficient to demonstrate that the restriction to  \( \Theta \)  of the canonical natural transformation  \( R \circ L_{\omega} \to \pi_{0} \)  is an isomorphism. As these two functors send Segal extensions on isomorphisms, it is sufficient to show the result on globes where it directly follows from the preservation of globes by  \( L_{\omega} \)  up to homotopy. ☐

170

## Part II

### On the side of theory

171



# Chapter 4

## The $(\infty, 1)$-category of $(\infty, \omega)$-categories

### Contents

|  **4.1** | **Preliminaries** | **175**  |
| --- | --- | --- |
|  4.1.1 | Explicit computation of some colimits | 175  |
|  4.1.2 | Factorization sytems | 177  |
|  4.1.3 | Reflexive localization | 183  |
|  **4.2** | **Basic constructions** | **185**  |
|  4.2.1 | $(\infty, \omega)$-Categories | 185  |
|  4.2.2 | Discrete Conduché functors | 202  |
|  **4.3** | **Gray Operations** | **207**  |
|  4.3.1 | Gray operations on $(\infty, \omega)$-categories | 207  |
|  4.3.2 | Gray deformation retract | 212  |
|  4.3.3 | Gray operations and strict objects | 216  |

This chapter is dedicated to the basic definition of $(\infty, \omega)$-categories. In the first section, we recall some results on factorization systems in presentable $(\infty, 1)$-categories. In the second section, we define $(\infty, \omega)$-categories and give some basic properties. We also define and study *discrete Conduché functor*, which are morphisms having the unique right lifting property against units $\mathbb{I}_{n+1} : \mathbf{D}_{n+1} \to \mathbf{D}_n$ for any integer $n$, and against compositions $\nabla_{k,n} : \mathbf{D}_n \to \mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$ for any pair of integers $k \leq n$. This notion was originally defined and studied in the context of strict $\omega$-category by Guetta in [Gue18].

173

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**Theorem 4.2.2.9.** *Let $f : C \to D$ be a discrete Conduché functor. The pullback functor $f^* : (\infty, \omega)\text{-cat}_{/D} \to (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.*

In the third section, we study Gray operations for $(\infty, \omega)$-categories. We conclude this chapter by proving results of strictification. In particular, we demonstrate the following theorem:

**Theorem 4.3.3.19.** *Let $C$ be an $(\infty, \omega)$-category, $b$ a globular sum, and $f : b \to C$ any morphism. The $(\infty, \omega)$-categories*

$$1 \stackrel{co}{\star} b \coprod_b C, \; C \coprod_b b \otimes [1] \text{ and } C \coprod_b b \star 1$$

*are strict whenever $C$ is.*

We will also prove the following theorem:

**Theorem 4.3.3.26.** *If $C$ is strict, so are $C \star 1$, $1 \stackrel{co}{\star} C$ and $C \otimes [1]$.*

In the process, we will demonstrate another fundamental equation combining $C \otimes [1]$, $1 \stackrel{co}{\star} C$, $C \star 1$, and $[C, 1]$.

**Theorem 4.3.3.25.** *Let $C$ be an $(\infty, \omega)$-category. The five squares appearing in the following canonical diagram are both cartesian and cocartesian:*

$$\begin{array}{ccc} & C \otimes \{0\} & \longrightarrow & 1 \\ & \downarrow & & \downarrow \\ C \otimes \{1\} & \longrightarrow & C \otimes [1] & \longrightarrow & C \star 1 \\ \downarrow & & \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{co}{\star} C & \longrightarrow & [C, 1] \end{array}$$

*where $[C, 1]$ is the suspension of $C$.*

**About the use of the language of $(\infty, 1)$-categories.** In this chapter and the two following, we will freely use the language of $(\infty, 1)$-categories$^1$.

$^1$As there are currently several directions for the formalization of the language of $(\infty, 1)$-categories ([RV22], [RS17], [Nor19], [CNW]), talking about "the" language of (infinite, 1)-categories may be confusing.

In such case, the reader may consider that we are working within the quasi-category Qcat of **T**-small quasi-categories for **T** a Grothendieck universe. This quasi-category may be obtained either using the coherent nerve as described in [Lur09a, chapter 3], or by considering it as the codomain of the universal co-

174

4.1. PRELIMINARIES

We allow ourselves the following abuse of language: when a ∞-groupoid X is contractible, we will use the expression the element of X to refer to any element of X. For example, we'll talk about the composition of two functors, or the colimit/limit of a functor. The adjective unique should be understood as the ∞-groupoid of choice is contractible.

An equivalence v in a (∞, 1)-category C between an object a and an object b is denoted by v : a ∼ b.

The maximal sub ∞-groupoid of an (∞, 1)-category C is denoted by τ₀(C).

Eventually, we will identify (strict) categories with the (∞, 1)-categories obtained by applying the simplicial nerve.

Cardinality hypothesis. We fix during this chapter three Grothendieck universes U ∈ V ∈ W, such that ω ∈ U. All defined notions depend on a choice of cardinality. When nothing is specified, this corresponds to the implicit choice of the cardinality V. With this convention in mind, we denote by Set the W-small 1-category of V-small sets, ∞-grd the W-small (∞, 1)-category of V-small ∞-groupoids and (∞, 1)-cat the W-small (∞, 1)-category of V-small (∞, 1)-categories.

## 4.1 Preliminaries

### 4.1.1 Explicit computation of some colimits

4.1.1.1. We have an adjunction:

$$\pi_0 : \infty\text{-grd} \xrightarrow{\perp} \text{Set} : \iota \tag{4.1.1.2}$$

For a category B, we denote by Psh(B) the category of functors Bᵒᵖ → Set. For a (∞, 1)-category A, we denote by Psh∞(A) the (∞, 1)-category of functors Aᵒᵖ → ∞-grd. A presheaf on B, (resp. a ∞-presheaves on A) is U-small if it is pointwise a U-small set (resp. a U-small ∞-groupoid).

cartesian fibration with T-small fibers as done in [CN22]. In both cases, the straightening/unstraightening correspondence provides a morphism

$$\mathrm{N}(\mathrm{Psh}(\Delta)_\mathbf{T}) \to \mathrm{Qcat}$$

that exhibits Qcat as the quasi-categorical localization of N(Psh(Δ)T) with respect to the weak equivalences of the Joyal's model structure ([CN22, theorem 8.13]).

The constructions we use to build new objects - (co)limits of functor between quasi-categories, quasi-categories of functor, localization of quasi-categories, sub maximal Kan complex, full sub quasi-category, adjunction, left and right Kan extension, Yoneda lemma - are well documented in the Joyal model structure (see [Lur09a] or [Cis19]), and therefore have direct incarnation in the quasi-category Qcat.

175

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

4.1.1.3. If A is a 1-category, the adjunction (4.1.1.2) induces an adjunction:

\[
\pi_ {0}: \mathrm{Psh} ^ {\infty} (A) \xrightarrow [ \leftarrow ]{\perp} \mathrm{Psh} (A): \iota \tag {4.1.1.4}
\]

4.1.1.5. We recall that the notion of elegant Reedy category is defined in paragraph 1.1.2.5. The following lemma provides a powerful way to compute simple colimits in \((\infty, 1)\)-categories by reducing to computations in (stricts) categories. These techniques will be used freely in the rest of this text.

Lemma 4.1.1.6. Let \( A \) be a \( \mathbf{V} \)-small category. We denote \( \iota : \mathrm{Psh}(A) \to \mathrm{Psh}^{\infty}(A) \) the canonical inclusion.

(1) The functor \(\iota\) preserves cocartesian square

![img-171.jpeg](img-171.jpeg)

where the left vertical morphism is a monomorphism.

(2) The functor \(\iota\) preserves colimit of finite diagrams of shape:

![img-172.jpeg](img-172.jpeg)

where morphisms labeled  \( \hookrightarrow \)  are monomorphisms.

(3) The functor \(\iota\) preserves transfinite composition.
(4) For any \(\mathbf{V}\)-small elegant Reedy category, and any functor \(F: I \to \mathrm{Psh}(A)\) that is Reedy cofibrant, i.e such that for any \(i \in I\), \(\operatorname{colim}_{\partial i} F \to F(i)\) is a monomorphism, the canonical comparison

\[
\iota \operatorname{colim} F \to \operatorname{colim} \iota F
\]

is an isomorphism. In particular, if \( A \) is itself an elegant Reedy category, for any set-valued presheaf \( X \) on \( A \), there is an equivalence

\[
\iota (X) \sim \underset {A _ {/ X}} {\operatorname{colim}} a.
\]

Proof. For this result, we use model categories. We consider the interval induces by the constant functor  \( I: A \to \mathrm{Psh}(\Delta) \)  with value [1]. We then consider the model structure on  \( \mathrm{Psh}(A \times \Delta) \)  produced by [Cis06, theorem 1.3.22] and induces by the homotopical data  \( (I \times \_, \emptyset) \) . This model structure represents  \( \mathrm{Psh}^{\infty}(A) \) . To conclude, we then have to show that all the given colimits, seen as (simplicialy constant) presheaves on  \( \Delta \times A \)  are also homotopy colimits of the same diagrams. This then follows from proposition 2.1.1.3, 2.1.1.4, 2.1.1.5 and theorem 2.1.1.7. □

176

4.1. PRELIMINARIES

### 4.1.2 Factorization sytems

4.1.2.1. For the rest of the section, we fix a presentable $(\infty, 1)$-category $C$, i.e a $(\infty, 1)$-category $C$ that is a reflexive and $\mathbf{V}$-accessible localization of a $(\infty, 1)$-category of $\infty$-presheaves on a $\mathbf{V}$-small $(\infty, 1)$-category.

A full sub $\infty$-groupoid of the $\infty$-groupoid of arrows of $C$ is cocomplete if it is closed under colimit and composition and contains the equivalences. For a $\infty$-groupoid $S$, we define $\widehat{S}$ as the smallest cocomplete full sub $\infty$-groupoid of the $\infty$-groupoid of arrows containing $S$.

Remark 4.1.2.2. A cocomplete full sub $\infty$-groupoid $U$ is closed by pushouts along any morphism. Indeed, suppose given a cocartesian square

![img-173.jpeg](img-173.jpeg)

with $f$ in $U$. Remark that $f'$ is the horizontal colimit of the diagram

![img-174.jpeg](img-174.jpeg)

and then is in $U$.

We say that an $\infty$-groupoid of morphisms $T$ is closed under left cancellation (resp. closed under right cancellation), if for any pair of composable morphisms $f$ and $g$, if $gf$ and $f$ are in $T$, so is $g$ (resp. if $gf$ and $g$ are in $T$, so is $f$).

Proposition 4.1.2.3. Let $U$ be a cocomplete $\infty$-groupoid of arrows of $C$. The $\infty$-groupoid $U$ is closed under left cancellation.

Proof. Suppose given $f : a \to b$, $g : b \to c$ such that $gf$ and $f$ are in $S$. As $g$ is the horizontal colimit of the following diagram

![img-175.jpeg](img-175.jpeg)

it is in $U$.

177

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

4.1.2.4. We recall some standard results on factorization systems, which appear in many places in the literature, such as in section 5.5.5 of [Lur09a] for the \((\infty,1)\)-case and [Joy] for the strict case.

Let \( S \) be a \( \mathbf{V} \)-small \( \infty \)-groupoid of maps of \( C \). We denote by \( \operatorname{Arr}_S(C) \) the full sub \( (\infty, 1) \)-category of \( \operatorname{Arr}(C) \) whose objects correspond to arrows of \( S \).

A weak factorization system in  \( (L,R) \)  is the data of two full sub  \( \infty \) -groupoids L and R of the  \( \infty \) -groupoid of arrows of C, stable under composition and containing equivalences, and of section  \( \operatorname{Arr}_{R}(C)\to\operatorname{Arr}_{L}(C)\times_{C}\operatorname{Arr}_{R}(C) \)  of the functor  \( \operatorname{Arr}_{L}(C)\times_{C}\operatorname{Arr}_{R}(C)\to\operatorname{Arr}(C) \)  sending two arrows onto their composite. This is a factorization system if the functor  \( \operatorname{Arr}(C)\to\operatorname{Arr}_{L}(C)\times_{C}\operatorname{Arr}_{R}(C) \)  is an equivalence.

Until the end of this section, we suppose given such factorization system in  \( (L,R) \) .

Definition 4.1.2.5. Let i and p be two morphisms, and consider a square of shape:

![img-176.jpeg](img-176.jpeg)

A lift in such square is the data of a morphism  \( h : c \to b \)  and of two commutative triangles

![img-177.jpeg](img-177.jpeg)

Equivalently, we can see a square of the previous shape as a morphism  \( s:1\to\operatorname{Sq}(i,p):=\operatorname{Hom}(a,b)\times_{\operatorname{Hom}(a,d)}\operatorname{Hom}(c,d) \)  and a lift as the data of a morphism  \( h:1\to\operatorname{Hom}(c,d) \)  and of a commutative triangle

![img-178.jpeg](img-178.jpeg)

The \(\infty\)-groupoid of lift of \(s\) is the fibers of \(\mathrm{Hom}(c,b) \to \mathrm{Sq}(i,p)\) at \(s\).

Definition 4.1.2.6. Let i and p be two morphisms. The morphism i has the unique left lifting property against p, or equivalently, p has the unique right lifting property against i, if for any square  \( s \in \operatorname{Sq}(i, p) \) , the  \( \infty \) -groupoid of lift of s is contractible. This is equivalent to asking for the morphism  \( \operatorname{Hom}(c, d) \to \operatorname{Sq}(i, p) \)  to be an equivalence.

Lemma 4.1.2.7. Suppose that we have a weak factorization system in  \( (L', R') \)  such that morphisms in  \( R' \)  have the unique right lifting property against morphisms of  \( L' \) . The weak factorization system is a factorization system.

178

4.1. PRELIMINARIES

Proof. Our goal is to demonstrate that the fibers of  \( \operatorname{Arr}_{L'}(C) \times_{C} \operatorname{Arr}_{R'}(C) \to \operatorname{Arr}(C) \)  are contractible. Let f be a morphism of C. As we have a weak factorization system, there exists an element in the fiber at f. Suppose given two elements in this fiber. This corresponds to a square

![img-179.jpeg](img-179.jpeg)

Morphisms between these two factorizations correspond to lifts in the previous square, which are contractible by assumption, and the fiber is then contractible.

We recall that in this section, we suppose that we have a factorization system in  \( (L, R) \) .

Lemma 4.1.2.8. Morphisms in L have the unique left lifting property with respect to morphisms in R.

Proof. Let  \( i : a \to c \)  be a morphim of L and  \( p : b \to d \)  a morphism of R. The factorization functor induces an equivalence between squares  \( s \in \operatorname{Sq}(i, p) \)  and diagrams of shape

![img-180.jpeg](img-180.jpeg)

where all the morphisms of the left triangle are in L and the ones of the right triangle are in R. Such diagrams are then in equivalence between composite  \( c \rightarrow e \rightarrow b \)  where the first morphism is in S and the second in R. Using once again the factorization functor, we can see that this data is exactly equivalent to a lift in the square s. □

We now show the converse of the previous lemma.

Lemma 4.1.2.9. A morphism having the unique left lifting property against morphisms of R is in L. Analogously, a morphism having the unique right lifting property against morphisms of L is in R.

Proof. Let f be a morphism having the unique left lifting property against morphisms in R. We factorize the morphism f in  \( i \in L \)  followed by  \( p \in R \)  and we want to produce an equivalence  \( f \sim i \) . The previous data induces by construction a square

![img-181.jpeg](img-181.jpeg)

179

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

By hypothesis, this square admits a lift $l : c \to b$, that we factorize in a morphism $r' \in L$ followed by a morphism $p' \in R$. The commutativity of the lower triangle implies equivalences $pl' \sim pp'r' \sim id$, and by unicity, $r' \sim id$ and $pp' \sim id$. The lift $l$ is equivalent to $p'$ and is then in $R$. The commutativity of the upper triangle implies $lf \sim lpi \sim i$ and by unicity again, $p'p \sim id$. The morphism $p$ is then an isomorphism, this implies that $f \sim i$, and $f$ is then in $L$. We proceed similarly for the dual assertion. □

**Proposition 4.1.2.10.** *A morphism is in $L$ (resp. in $R$) if and only if it has the unique left lifting property against morphisms of $R$ (resp. the unique right lifting property against the morphisms of $R$).*

*Proof.* This is the content of lemma 4.1.2.8 and 4.1.2.9.

**Proposition 4.1.2.11.** *The forgetful functor from the $(\infty,1)$-category of squares with lifts, and whose left (resp. right) vertical morphism is in $L$ (resp. in $R$), to the $(\infty,1)$-category of squares whose left (resp. right) vertical morphism is in $L$ (resp. in $R$), is an equivalence.*

*Roughly speaking, the formation of the lift in squares whose left (resp. right) vertical morphism is in $L$ (resp. in $R$) is functorial.*

*Proof.* The $(\infty,1)$-category of squares with lifts, and whose left (resp. right) vertical morphism is in $L$ (resp. in $R$), is the $(\infty,1)$-category

$$
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C)
$$

and the $(\infty,1)$-category whose left (resp. right) vertical morphism is in $L$ (resp. in $R$) of squares is the limit of the diagram

$$
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) \xrightarrow{\nabla} \operatorname{Arr}(C) \xleftarrow{\nabla} \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C)
$$

The forgetful functor is induced by the commutative diagram

$$
\begin{array}{ccc}
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C) & \xrightarrow{\nabla \times_C \operatorname{Arr}_R(C)} & \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C) \\
\operatorname{Arr}_L(C) \times_C \nabla \downarrow & & \downarrow \nabla \\
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) & \xrightarrow{\nabla} & \operatorname{Arr}(C)
\end{array}
$$

and we then have to show that it is cartesian.

By definition of factorization system, the morphism

$$
\nabla : \operatorname{Arr}_L(C) \times_C \operatorname{Arr}_R(C) \to \operatorname{Arr}(C)
$$

180

4.1. PRELIMINARIES

is an equivalence. The previous square is then equivalent to the square

$$\begin{array}{c} \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}(C)_{L} \times_{C} \operatorname{Arr}_{R}(C) \times_{C} \operatorname{Arr}_{R}(C) \xrightarrow{\nabla \times_{C} \operatorname{Arr}_{R}(C) \times_{C} \operatorname{Arr}_{R}(C)} \operatorname{Arr}(C)_{L} \times_{C} \operatorname{Arr}_{R}(C) \times_{C} \operatorname{Arr}_{R}(C) \\ \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{L}(C) \times_{C} \nabla \Bigg\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{R}(C) \xrightarrow{\nabla \times_{C} \operatorname{Arr}_{R}(C)} \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{R}(C) \end{array}$$

which is obviously cartesian.

**Proposition 4.1.2.12.** *The $\infty$-groupoid $L$ is stable under colimit, retract, composition, and left cancellation. The $\infty$-groupoid $R$ is stable under limit, retract, composition, and right cancellation.*

*Proof.* Let $p : b \to d$ be a morphism of $R$ and $\{i_j : a_j \to c_j\}_{j:J}$ a family of morphisms of $L$ indexed by a functor $J \to \operatorname{Arr}_L(C)$, admitting a colimit $\bar{i} : \bar{a} \to \bar{c}$. Both functors $r \mapsto \operatorname{Sq}(r, p)$ and $c \mapsto \operatorname{Hom}(c, b)$ send colimits on limits. This implies that the morphism

$$\operatorname{Hom}(\bar{c}, b) \to \operatorname{Sq}(\bar{i}, p)$$

is the limit in $\operatorname{Arr}(\operatorname{Sp})$ of the family of morphisms

$$\operatorname{Hom}(c_j, b) \to \operatorname{Sq}(i_j, p).$$

Each of these morphisms is an equivalence by assumption, so that implies that $\operatorname{Hom}(\bar{c}, b) \to \operatorname{Sq}(\bar{i}, p)$ is an equivalence. As this is true for any $p$ in $R$, proposition 4.1.2.10 implies that $\bar{i}$ is in $L$.

Consider now a retract diagram:

$$\begin{array}{c} a \xrightarrow{id} a' \xrightarrow{} a \\ \downarrow i \qquad \qquad \downarrow i' \qquad \qquad \downarrow i \\ c \xrightarrow{id} c' \xrightarrow{} c \end{array}$$

such that $i'$ is in $L$. For any morphism $p : b \to d$ of $R$, this induces a retract diagram

$$\begin{array}{c} \operatorname{Hom}(c, b) \xrightarrow{id} \operatorname{Hom}(c', b) \xrightarrow{} \operatorname{Hom}(c, b) \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \\ \operatorname{Sq}(i, p) \xrightarrow{id} \operatorname{Sq}(i', p) \xrightarrow{} \operatorname{Sq}(i, p) \end{array}$$

As equivalences are stable under retract, $\operatorname{Hom}(c, b) \to \operatorname{Sq}(i, p)$ is an equivalence, and as it is true for any $p$ in $R$, $i$ is in $L$.

For the cloture under left cancellation, this is proposition 4.1.2.3.

We proceed similarly for the dual assertion.

181

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

4.1.2.13. We fix an  \( \infty \) -groupoid S of arrows of C with U-small domain and codomain. We define  \( L_{S} := \widehat{S} \) , i.e as the smallest full sub  \( \infty \) -groupoid of arrows of C stable under colimits, composition and including S, and  \( R_{S} \)  as the full sub  \( \infty \) -groupoid of arrows of C having the unique right lifting property against morphisms of S.

Construction 4.1.2.14 (Small object Argument). Let \( f: x \to y \) be an arrow. We define by induction on \( \mathbf{U} \) a sequence \( \{x_{\alpha}\}_{\alpha < \mathbf{U}} \) sending \( \emptyset \) on \( x \). For a limit ordinal \( \alpha < \mathbf{U} \), we set \( x_{\alpha} := \operatorname{colim}_{\alpha' < \alpha} x_{\alpha'} \). For a successor ordinal, we define \( x_{\alpha + 1} \) as the pushout:

![img-182.jpeg](img-182.jpeg)

Let \( i: x \to \tilde{x} \) be the transfinite composition of this sequence. There is an induced morphism \( p: \tilde{x} \to y \), and an equivalence \( f \sim pi \).

Proposition 4.1.2.15. The previous construction defines a factorization system between \( L_{S} \) and \( R_{S} \).

Proof. Let  \( f : x \to y \)  be any morphism. The previous construction produces functorially morphisms  \( i : x \to \tilde{x} \)  and  \( p : \tilde{x} \to y \)  whose composite is f. The morphism i is obviously in  \( L_{S} \) . We then need to show that p has the unique right lifting property against any morphism of  \( L_{S} \) . Let  \( j : a \to b \)  be any morphism in  \( L_{S} \) , n an integer and consider a commutative square

![img-183.jpeg](img-183.jpeg)

By stability by \(\omega\)-small colimits, the object \(a \coprod_{\mathrm{colim}_{\mathbb{S}_n} a} \mathrm{colim}_{\mathbb{S}_n} b\) is \(\mathbf{U}\)-small. There exists then \(\alpha < \mathbf{U}\) such that the top morphism factors through \(x_\alpha\), and by construction there exists a morphism \(l: b \to x_{\alpha+1}\) and a comutative square

![img-184.jpeg](img-184.jpeg)

182

4.1. PRELIMINARIES

The induced diagonal is a lift in the first square. This implies that $\operatorname{Hom}(b, x) \to \operatorname{Sq}(j, p)$ has the right lifting property against $\mathbb{S}_n \to 1$. Eventually, this implies that $\operatorname{Hom}(b, x) \to \operatorname{Sq}(j, p)$ is an equivalence of $\infty$-groupoid, and $p$ then has the unique right lifting property against $i$. We then have a weak factorization system, which is a factorization system according to lemma 4.1.2.7.

### 4.1.3 Reflexive localization

4.1.3.1. An object $x$ is $S$-local if for any $i : a \to b \in S$, the induced functor $\operatorname{Hom}(i, x) : \operatorname{Hom}(b, x) \to \operatorname{Hom}(a, x)$ is an equivalence. We define $C_S$ as the full sub $(\infty, 1)$-category of $C$ composed of $S$-local objects.

Lemma 4.1.3.2. An object is $S$-local if and only if $x \to 1$ is in $R_S$.

Proof. Let $i \in S$. Remark that the functor $\operatorname{Hom}(b, x) \to \operatorname{Sq}(i, x \to 1) \sim \operatorname{Hom}(a, x)$ is $\operatorname{Hom}(i, f)$. The proposition 4.1.2.10 then implies the desired result.

Theorem 4.1.3.3. The inclusion $\iota : C_S \to C$ is part of an adjunction

$$\mathbf{F}_S : C \xrightarrow[\downarrow]{} C_S : \iota$$

Moreover, $\mathbf{F}_S : C \to C_S$ is the localization of $C$ by $\widehat{S}$.

Proof. For an object $x$, the small object argument provides a factorization of $x \to 1$ into a morphism $x \to \mathbf{F}_S x$ of $L_S$ followed by a morphism $\mathbf{F}_S x \to 1$ in $R_S$. According to lemma 4.1.3.2, $\mathbf{F}_S x$ is in $C_S$. As the factorization is functorial, this defines a functor $\mathbf{F}_S : C \to C_S$, and a natural transformation $\nu : id \to \mathbf{F}_S$ constant on $S$-local objects. As $\mathbf{F}_S \iota$ is equivalent to the identity, this induces the claimed adjunction.

For the second proposition, let $F : C \to D$ be a functor sending morphisms of $L_S$ on equivalences. We define $\mathbf{D}(F) := F \circ \iota$, and we have a diagram

![img-185.jpeg](img-185.jpeg)

that commutes up to the natural transformation $F \circ_0 \nu : F \to D(F) \circ \mathbf{F}_S$. However, the natural transformation $\nu$ is pointwise in $L_S$, which implies that $F \circ \nu$ is pointwise an equivalence, and the previous diagram then commutes. Now, let $G : C_S \to D$ be any other functor such that $G \circ \mathbf{F}_S \sim F$. By precomposing with iota, this implies that $G \sim F \circ \iota$.

183

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

Corollary 4.1.3.4. The  \( (\infty,1) \) -category  \( C_{S} \)  is cocomplete. Moreover, if  \( F:C\to D \)  is a colimit preserving functor sending S onto equivalences, the induced functor  \( DF:C_{S}\to D \)  preserves colimits.

Proof. The first assertion is a direct consequence of the adjunction given in theorem 4.1.3.3.

This adjunction also implies that the colimit of a functor  \( G: A \to C_{S} \)  is given by  \( \mathbf{F}_{S}(\operatorname{colim}_{a:A} \iota G(a)) \) . As the canonical morphism  \( \operatorname{colim}_{a:A} \iota G(a) \to \mathbf{F}_{S}(\operatorname{colim}_{a:A} \iota G(a)) \)  is by construction in  \( \widehat{S} \)  this proves the second assertion. ☐

4.1.3.5. Suppose given an adjunction between two \((\infty, 1)\)-categories

\[
F: C \xrightarrow [ \leftarrow ]{\perp} D: G
\]

with unit  \( \nu \)  and counit  \( \epsilon \) , as well as an  \( \infty \) -groupoid of morphisms S of C and T of D such that  \( F(S) \subset \widehat{T} \) . By adjunction property, it implies that for any T-local object  \( d \in D \) ,  \( G(d) \)  is S-local. The previous adjunction induces a derived adjunction

\[
\mathbf {L} F: C _ {S} \xrightarrow [ \leftarrow ]{\perp} D _ {T}: \mathbf {R} G
\]

where \(\mathbf{L}F\) is defined by the formula \(c\mapsto \mathbf{F}_T F(c)\) and \(\mathbf{R}G\) is the restriction of \(G\) to \(D_{T}\). The unit is given by \(\nu \circ \mathbf{F}_S\) and the counit by the restriction of \(\epsilon\) to \(D_{T}\).

Example 4.1.3.6. Let C be a presentable  \( (\infty,1) \) -category, S a full sub  \( \infty \) -groupoid of morphisms of  \( \mathrm{Psh}^{\infty}(A) \)  with U-small codomain and domain. Eventually, we set  \( S_{/c} \)  as the  \( \infty \) -groupoid of morphisms of shape

![img-186.jpeg](img-186.jpeg)

where s : S.

A morphism \( f: c \to d \) induces an adjunction

\[
f _ {!}: C _ {/ c} \xrightarrow [ \leftarrow ]{\perp} C _ {/ d}: f ^ {*}
\]

where the left adjoint is the composition and the right adjoint is the pullback. By construction,  \( f_{!}(S_{/c}) \subset S_{/d} \) . The previous adjunction can then be derived, and induced an adjunction:

\[
\mathbf {L} f _ {!}: (C _ {/ c}) _ {S _ {/ c}} \xrightarrow [ \leftarrow ]{\perp} (C _ {/ d}) _ {S _ {/ d}}: \mathbf {R} f ^ {*}
\]

where the right adjoint is just the restriction of  \( f^{*} \)  to  \( S_{/d} \) -local objects.

184

4.2. BASIC CONSTRUCTIONS

If the functor $f^*: C_{/d} \to C_{/c}$ preserves colimits and $f^*(S_{/c}) \subset S_{/d}$, the adjunction

$$f^*: C_{/d} \xrightarrow{\perp} C_{/c}: f_*$$

induces an adjunction

$$\mathbf{L}f^*: (C_{/d})_{S_{/d}} \xrightarrow{\perp} (C_{/c})_{S_{/c}}: \mathbf{R}f_*$$

## 4.2 Basic constructions

### 4.2.1 $(\infty, \omega)$-Categories

The definitions of section 1.1.2 will be used freely here.

#### 4.2.1.1. We denote by

$$[\_, \_]: \mathrm{Psh}^\infty(\Theta) \times \mathrm{Psh}^\infty(\Delta) \to \mathrm{Psh}^\infty(\Delta[\Theta])$$

the extension by colimit of the functor $\Theta \times \Delta \to \mathrm{Psh}^\infty(\Delta[\Theta])$ sending $(a, n)$ onto $[a, n]$. For an integer $n$, we denote

$$[\_, n]: \mathrm{Psh}^\infty(\Theta)^n \to \mathrm{Psh}^\infty(\Theta)$$

the extension by colimit of the functor $\Theta^n \to \mathrm{Psh}^\infty(\Theta)$ sending $\mathbf{a} := \{a_1, ..., a_n\}$ onto $[\mathbf{a}, n]$.

#### 4.2.1.2. We have an adjunction

$$i_! : \mathrm{Psh}^\infty(\Delta[\Theta]) \xrightarrow{\longleftrightarrow} \mathrm{Psh}^\infty(\Theta) : i^* \tag{4.2.1.3}$$

where the left adjoint is the left Kan extension of the functor $\Delta[\Theta] \xrightarrow{i} \Theta \to \mathrm{Psh}^\infty(\Theta)$. The sets of morphisms W and M are respectively defined in paragraphs 1.1.2.14 and 1.1.2.15. There is an obvious inclusion $i_!(M) \subset W$. The previous adjunction then induced a derived adjunction

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta])_M \xrightarrow{\longleftrightarrow} \mathrm{Psh}(\Theta)_W : \mathbf{R}i^* \tag{4.2.1.4}$$

**Proposition 4.2.1.5.** *The unit and counit of the adjunction (4.2.1.3) are respectively in $\widehat{M}$ and $\widehat{W}$. As a consequence, the adjunction (4.2.1.4) is an adjoint equivalence.*

*Proof.* We denote by $\iota : \mathrm{Psh}(\Theta) \to \mathrm{Psh}^\infty(\Theta)$ and $\iota : \mathrm{Psh}(\Delta[\Theta]) \to \mathrm{Psh}^\infty(\Delta[\Theta])$ the two canonical inclusions. By the definition of the smallest precocomplete class (paragraph 1.1.3.1) and according to lemma 4.1.1.6, we have inclusions $\iota(\overline{W}) \subset \widehat{W}$ and $\iota(\overline{M}) \subset \widehat{M}$. The result then directly follows from theorem 1.1.3.3. $\square$

185

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**4.2.1.6.** A $(\infty, \omega)$-category is a W-local $\infty$-presheaf $C \in \mathrm{Psh}^{\infty}(\Theta)$. We then define

$$(\infty, \omega)\text{-cat} := \mathrm{Psh}^{\infty}(\Theta)_{\mathrm{W}}.$$

Proposition 4.2.1.5 implies that $(\infty, \omega)$-cat identifies itself with the full sub $(\infty, 1)$-category of $\mathrm{Psh}^{\infty}(\Delta[\Theta])$ of M-local objects:

$$(\infty, \omega)\text{-cat} \sim \mathrm{Psh}^{\infty}(\Delta[\Theta])_{\mathrm{M}}.$$

We recall that the sets of morphisms W and M are respectively defined in paragraphs 1.1.2.14 and 1.1.2.15.

**4.2.1.7.** We denote by $\pi_0 : \mathrm{Psh}^{\infty}(\Theta) \to \mathrm{Psh}(\Theta)$ the functor sending an $\infty$-presheaf $X$ onto the presheaf

$$\pi_0 X : a \mapsto \pi_0(X_a)$$

This functor admits a fully faithful right adjoint: $\mathrm{N} : \mathrm{Psh}(\Theta) \to \mathrm{Psh}^{\infty}(\Theta)$. As $\pi_0$ preserves W, it induces an adjoint pair:

$$\pi_0 : (\infty, \omega)\text{-cat} \underset{\longleftarrow}{\overset{\perp}{\longrightarrow}} (0, \omega)\text{-cat} : \mathrm{N}$$

where the right adjoint N is fully faithful. Every $(0, \omega)$-category can then be seen as an $(\infty, \omega)$-category and we will call *strict* the $(\infty, \omega)$-categories lying in the image of this functor.

The inclusion $\Delta \to \Theta$ induces by extention by colimit a functor $\mathrm{Psh}^{\infty}(\Delta) \to \mathrm{Psh}^{\infty}(\Theta)$. Passing to the localization, this induces a fully faithful inclusion $(\infty, 1)$-cat $\to (\infty, \omega)$-cat.

The inclusion $\{[0]\} \to \Theta$ induces by extention by colimit a functor $\infty\text{-grd} \to \mathrm{Psh}^{\infty}(\Theta)$. Passing to the localization, this induces a fully faithful inclusion $\infty\text{-grd} \to (\infty, \omega)$-cat. The $(\infty, \omega)$-categories lying in the image of this functors will be also called $\infty$-*groupoids*.

**4.2.1.8.** A $n$-cell of an $(\infty, \omega)$-category is a morphism $\mathbf{D}_n \to C$. If $C$ is an $(\infty, \omega)$-category, we denote by $C_n$ the value of $C$ on $\mathbf{D}_n$.

**Proposition 4.2.1.9.** *Let $C, D$ be two $(\infty, \omega)$-categories, and $f : C \to D$ any map. The morphism $f$ is an equivalence if and only if for any $n$, the induced morphism $f_n : C_n \to D_n$ is an equivalence.*

*Proof.* This is a necessary condition. For the converse, let $f$ be a morphism fulfilling this condition. To show that $f$ is an equivalence, we have to show that for any globular sum $a$, $f_a : C_a \to D_a$ is an equivalence. This is true as

$$f_a : C_a \to D_a \sim \lim_{n \in \mathrm{Sp}_a} f_n : C_n \to D_n.$$

$\square$

186

4.2. BASIC CONSTRUCTIONS

Lemma 4.2.1.10. A functor is an equivalence if it has the unique right lifting property against \(\emptyset \to \mathbf{D}_n\) for any \(n \geq 0\).

Proof. This is a necessary condition. For the converse, let  \( f : C \to D \)  be a morphism fulfilling this condition. By definition of left unique lifting property, it implies that the induced morphism  \( f_{n} : C_{n} \to D_{n} \)  is an equivalence for any  \( n \geq 0 \) . Using proposition 4.2.1.9, f is an equivalence. □

4.2.1.11. Let  \( \mathrm{Psh}^{\infty}(\Theta)_{\bullet,\bullet} \)  be the  \( (\infty,1) \) -category of  \( \infty \) -presheaves on  \( \Theta \)  with two distinguished points, i.e. of triples  \( (C,a,b) \)  where a and b are elements of  \( C_{0} \) . The functor  \( [\_,1]:\Theta\to\mathrm{Psh}^{\infty}(\Theta)_{\bullet,\bullet} \)  that sends a onto  \( ([a,1],\{0\},\{1\}) \)  induces by extension by colimit an adjunction

\[
[ \_, 1 ]: \mathrm{Psh} ^ {\infty} (\Theta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{Psh} ^ {\infty} (\Theta) _ {\bullet , \bullet}: \hom_ {-} (\_, \_) \tag {4.2.1.12}
\]

As the left adjoint preserves representables, the right adjoint commutes with colimit. It is then easy to check on representables that the unit of this adjunction is an equivalence. As a consequence, the left adjoint is fully faithful.

Lemma 4.2.1.13. Let C be an  \( \infty \) -presheaves on  \( \Theta \) . The canonical morphisms

\[
C \to \hom_ {[ C, 1 ]} (0, 1) \quad \hom_ {[ C, 1 ]} (0, 0) \to 1 \quad \hom_ {[ C, 1 ]} (1, 1) \sim 1 \quad \emptyset \to \hom_ {[ C, 1 ]} (1, 0)
\]

are equivalences.

Proof. As both hom and  \( [\_,1] \)  preserve colimits, it is sufficient to check this property on representables, where it is an easy computation. □

Proposition 4.2.1.14. The functor \([\_, 1] : \mathrm{Psh}^{\infty}(\Theta) \to \mathrm{Psh}^{\infty}(\Theta)\) preserves \((\infty, \omega)\)-categories.

Proof. By construction, for any pair of integers \( k < n \), and any pair of globular sums \( ([\mathbf{a}, n], b) \), we have cartesian squares

![img-187.jpeg](img-187.jpeg)

![img-188.jpeg](img-188.jpeg)

where \(\epsilon\) denote any constant functor with value 0 or 1, and \(\alpha_{k}\) the morphism that sends \(k\) on 0 and \(k + 1\) on 1. Let \(C\) be an \((\infty, \omega)\)-category. As the \((\infty, 1)\)-category \(\infty\)-grd is

187

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

locally cartesian closed, we have cartesian squares

![img-189.jpeg](img-189.jpeg)

which induces cartesian squares

![img-190.jpeg](img-190.jpeg)

This directly implies that \([C,1]\) is \(\mathrm{W_{Seg}}\)-local.

Furthermore, for any integer \( n > 0 \), the cartesian squares (4.2.1.15) induces cartesian squares

![img-191.jpeg](img-191.jpeg)

which implies that \([C,1]\) is local with respect to \(\Sigma^n E^{eq}\to \Sigma^n 1\).

Eventually, suppose given a diagram of shape

\[
\begin{array}{c} E ^ {e q} \longrightarrow [ C, 1 ] \\ \Big \downarrow \\ 1 \end{array} \tag {4.2.1.16}
\]

The canonical morphism \( E^{eq} \to [C,1] \xrightarrow{\pi} [1] \) then factors through 0 or 1. As the two fibers of \( \pi \) are trivial, the diagram (4.2.1.16) admits a unique lift, which concludes the proof.

4.2.1.17. As \([\_, 1]\) sends W to a subset of M, the functor \(\mathrm{hom}_{-,\_}(\_)\) preserves \((\infty, \omega)\)-categories. Combined with the last proposition, this implies that the adjunction (4.2.1.12) restricts to an adjunction:

\[
[ \_, 1 ]: (\infty , \omega) \text {-cat} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat} _ {\bullet , \bullet}: \hom_ {-} (\_, \_) \tag {4.2.1.18}
\]

The left adjoint is the suspension functor.

Proposition 4.2.1.19. Let \(C\) be an \((\infty, \omega)\)-categories. We have natural equivalences

\[
\hom_ {[ C, 1 ]} (0, 1) \sim C \quad \hom_ {[ C, 1 ]} (0, 0) \sim \hom_ {[ C, 1 ]} (1, 1) \sim 1 \quad \hom_ {[ C, 1 ]} (1, 0) \sim \emptyset .
\]

Proof. This is a direct consequence of lemma 4.2.1.13.

188

4.2. BASIC CONSTRUCTIONS

4.2.1.20. Suppose given an  \( (\infty,\omega) \) -category C and a 1-cells  \( f:x'\to x \) . As C is an  \( (\infty,\omega) \) -category, for any globular sum a, the morphism

\[
\mathrm{Hom} ([ 1 ] \vee [ a, 1 ], C) \to \mathrm{Hom} ([ 1 ], C) \times_ {\mathrm{Hom} ([ 0 ], C)} \mathrm{Hom} ([ a, 1 ], C)
\]

is an equivalence. This induces a morphism

\[
\mathrm{Hom} (a, \mathrm{hom} _ {C} (x, y)) \to \mathrm{Hom} ([ 1 ] \vee [ a, 1 ], (C, x ^ {\prime}, y)) \to \mathrm{Hom} (a, \mathrm{hom} _ {C} (x ^ {\prime}, y))
\]

where the two distinguished points of  \( [1] \vee [a,1] \)  are the extremal ones, and where the left-hand morphism is the restriction of the inverse of the previous morphism. By the Yoneda lemma, this corresponds to a morphism

\[
f _ {!}: \hom_ {C} (x ^ {\prime}, y) \to \hom_ {C} (x, y).
\]

Conversely, a 1-cell \( g: y \to y' \) induces a morphism

\[
g _ {!}: \hom_ {C} (x, y) \to \hom_ {C} (x, y ^ {\prime}).
\]

4.2.1.21. We denote by \(\iota\) the inclusion of \((\infty, \omega)\)-cat into \(\mathrm{Psh}^{\infty}(\Theta)\). A functor \(F: I \to (\infty, \omega)\)-cat has a special colimit if the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota F (i) \rightarrow \iota (\underset {i: I} {\operatorname{colim}} F (i)) \tag {4.2.1.22}
\]

is an equivalence of presheaves.

Similarly, we say that a functor \(\psi : I \to \mathrm{Arr}((\infty, \omega)\text{-cat})\) has a special colimit if the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota \psi (i) \to \iota (\underset {i: I} {\operatorname{colim}} \psi (i))
\]

is an equivalence in the arrow  \( (\infty,1) \) -category of  \( \mathrm{Psh}^{\infty}(\Theta) \) .

Example 4.2.1.23. Let C be an  \( (\infty,\omega) \) -category. The canonical diagram  \( \Theta_{/C} \to (\infty,\omega) \) -cat has a special colimit, given by C.

Proposition 4.2.1.24. Let \( F, G: I \to (\infty, \omega) \)-cat be two functors, and \( \psi: F \to G \) a natural transformation. If \( \psi \) is cartesian, and \( G \) has a special colimit, then \( \psi \) and \( F \) have special colimits.

Proof. We have to show that \( F \) has a special colimit, it will directly imply that \( \psi \) also has one. The morphism (4.2.1.22) is always in \( \widehat{\mathrm{W}} \). To conclude, one then has to show that \( \operatorname{colim}_{i:I} \iota \psi(i) \) is W-local. To this extend, it is enough to demonstrate that the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota \psi (i): \underset {i: I} {\operatorname{colim}} \iota F (i) \to \underset {i: I} {\operatorname{colim}} \iota G (i)
\]

189

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

has the unique right lifting property against W. We then consider a square

$$\begin{array}{c} a \longrightarrow \operatorname{colim}_{i:I} \iota F(i) \\ \downarrow \quad \downarrow \operatorname{colim}_{i:I} \iota \psi(i) \\ b \longrightarrow \operatorname{colim}_{i:I} \iota G(i) \end{array} \tag{4.2.1.25}$$

where $f \in W$. As the domain of $f$ is representable, there always exists $j : I$, such that the bottom horizontal morphism factors through $G(j)$. As $\psi$ is cartesian, the square (4.2.1.25) factors in two squares, where the right one is cartesian.

$$\begin{array}{c} a \longrightarrow F(i) \longrightarrow \operatorname{colim}_{i:I} \iota F(i) \\ \downarrow \quad \downarrow \psi(i) \quad \downarrow \operatorname{colim}_{i:I} \iota \psi(i) \\ b \longrightarrow G(i) \longrightarrow \operatorname{colim}_{i:I} \iota G(i) \end{array}$$

Lifts in the square (4.2.1.25) are then equivalent to lifts in the left square, which exist and are unique as $F(i) \to G(i)$ has the unique right lifting property against W. $\square$

**Proposition 4.2.1.26.** *For any integer $n$, and globular sums $a$ and $b$, the equalizer diagram*

$$\coprod_{k+l=n-1}[a, k] \vee [a \times b, 1] \vee [a, l] \longrightarrow \coprod_{k+l=n}[a, k] \vee [b, 1] \vee [a, l]$$

*where the top diagram is induced by $[a \times b, 1] \to [a, 1] \vee [b, 1]$ and to bottom one by $[a \times b, 1] \to [b, 1] \vee [a, 1]$, has a special colimit, which is $[a, n] \times [b, 1]$.*

*Proof.* The lemma 4.1.1.6 implies that the colimit of the previous diagram, computed in $\operatorname{Psh}^{\infty}(\Theta)$ is strict. It is then enough to show that this colimit, computed in $\operatorname{Psh}(\Theta)$, is equivalent to $[a, n] \times [b, 1]$. As this last object is W-local, this will conclude the proof. The remaining combinatorial exercise is left to the reader. $\square$

**Proposition 4.2.1.27.** *Any sequence of $(\infty, \omega)$-categories has a special colimit.*

*Proof.* Suppose given such sequence. If the sequence is finite, this is obviously true. Suppose now that the sequence is non finite. As codomains and domains of morphism of W are $\omega$-small, the colimit of the sequence, computed in $\operatorname{Psh}^{\infty}(\Theta)$ is W-local, which concludes the proof. $\square$

**Lemma 4.2.1.28.** *The functor $[\_, 1] : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}_{\bullet,\bullet}$ preserves special colimits.*

*Proof.* This is a direct consequence of proposition 4.2.1.14. $\square$

190

4.2. BASIC CONSTRUCTIONS

Lemma 4.2.1.29. We denote by

\[
[ \_, 1 ] \vee [ 1 ]: (\infty , \omega) \text {-cat} \rightarrow (\infty , \omega) \text {-cat} _ {[ 0 ] \mathrm{II} [ 1 ] /}
\]

\[
(r e s p. [ 1 ] \vee [ \_, 1 ]: (\infty , \omega) \text {-cat} \rightarrow (\infty , \omega) \text {-cat} _ {[ 1 ] \mathrm{II} [ 0 ] /})
\]

the colimit preserving functor that sends an element \(a\) of \(\Theta\) onto the globular sum \([a,1]\vee [1]\) (resp. \([1]\vee [a,1]\)).

The functors \([\_, 1] \vee [\_, 1]\) and \([1] \vee [\_, 1]\) preserve special colimits.

Proof. To prove this, we establish a result analogous to the one given in the proposition 4.2.1.14. We omit its proof because it is long but essentially identical. \(\square\)

Proposition 4.2.1.30. Suppose given two cartesian squares

![img-192.jpeg](img-192.jpeg)

The diagram

\[
[ 1 ] \vee [ B, 1 ] \xleftarrow {\nabla} [ B, 1 ] \longrightarrow [ C, 1 ] \longleftarrow [ D, 1 ] \xrightarrow {\nabla} [ D, 1 ] \vee [ 1 ]
\]

has a special colimit.

Proof. Remark firsts that the colimit, computed in \(\mathrm{Psh}^{\infty}(\Theta)\), of the diagram

\[
[ 1 ] \vee [ 1 ] \xleftarrow {\nabla} [ 1 ] \xrightarrow {[ \{0 \} , 1 ]} [ [ 1 ], 1 ] \xleftarrow {[ \{1 \} , 1 ]} [ 1 ] \xrightarrow {\nabla} [ 1 ] \vee [ 1 ]
\]

is strict. We leave it to the reader to check that the previous diagram has a special colimit.

Remark now that \(\Theta\) is stable by pullback and \([\_, 1]\) preserves cartesian squares in \(\Theta\). The lemma 4.2.1.28 states that \([\_, 1]\) preserves special colimit, and as \(\mathrm{Psh}^{\infty}(\Theta)\) is locally cartesian closed, pullbacks also preserve them. As every \((\infty, \omega)\)-category is a special colimit of representables, this implies that the squares

![img-193.jpeg](img-193.jpeg)

are cartesian. Furthermore, for any globular sum \( b \), we have cartesian squares

![img-194.jpeg](img-194.jpeg)

![img-195.jpeg](img-195.jpeg)

191

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

According to lemma 4.2.1.29, \([\_, 1] \vee [1]\) and \([1] \vee [\_, 1]\) preserve special colimits. As every \((\infty, \omega)\)-category is a colimit of representables, this implies that the squares

![img-196.jpeg](img-196.jpeg)

![img-197.jpeg](img-197.jpeg)

are cartesian. The result then follows from proposition 4.2.1.24.

Proposition 4.2.1.31. Suppose given a cartesian square

![img-198.jpeg](img-198.jpeg)

The diagram

\[
[ 1 ] \vee [ B, 1 ] \xleftarrow {\triangledown} [ B, 1 ] \longrightarrow [ C, 1 ]
\]

has a special colimit.

Proof. The proof is similar to the previous one.

##### 4.2.1.32. We have an adjunction

\[
i _ {!}: \mathrm{Psh} ^ {\infty} (\Delta [ \Theta_ {n - 1} ]) \xrightarrow [ \longleftarrow ]{} \mathrm{Psh} ^ {\infty} (\Theta_ {n}): i ^ {*} \tag {4.2.1.33}
\]

where the left adjoint is the left Kan extension of the functor  \( \Delta[\Theta_{n-1}] \xrightarrow{i} \Theta_n \to \mathrm{Psh}^\infty(\Theta_n) \) . We recall that the sets of morphisms  \( W_n \)  and  \( M_n \)  are respectively defined in paragraphs 1.1.2.14 and 1.1.2.15. Remark that there is an obvious inclusion  \( i_!(\mathrm{M}_n) \subset \mathrm{W}_n \) . The previous adjunction then induced a derived adjunction

\[
\mathbf {L} i _ {!}: \mathrm{Psh} (\Delta [ \Theta_ {n - 1} ]) _ {\mathrm{M}} \xrightarrow [ \longleftarrow ]{} \mathrm{Psh} (\Theta_ {n}) _ {\mathrm{W}}: \mathbf {R} i ^ {*} \tag {4.2.1.34}
\]

Proposition 4.2.1.35. The unit and counit of the adjunction (4.2.1.33) are respectively in \(\widehat{\mathrm{M}}_n\) and \(\widehat{\mathrm{W}}_n\). As a consequence, the adjunction (4.2.1.34) is an adjoint equivalence.

Proof. We denote by \(\iota : \mathrm{Psh}(\Theta_n) \to \mathrm{Psh}^\infty(\Theta_n)\) and \(\iota : \mathrm{Psh}(\Delta[\Theta_{n-1}]) \to \mathrm{Psh}^\infty(\Delta[\Theta_{n-1}])\) the two canonical inclusions. By the definition of the smallest precocomplete class (paragraph 1.1.3.1) and according to lemma 4.1.1.6, we have inclusions \(\iota(\overline{\mathrm{W}_n}) \subset \widehat{\mathrm{W}_n}\) and \(\iota(\overline{\mathrm{M}_n}) \subset \widehat{\mathrm{M}_n}\). The result then directly follows from theorem 1.1.3.3.

192

4.2. BASIC CONSTRUCTIONS

4.2.1.36. Let $n > 0$ be an integer. An $(\infty, n)$-category is a $\mathrm{W}_n$-local $\infty$-presheaf $C \in \mathrm{Psh}^\infty(\Theta_n)$. We then define

$$
(\infty, n)\text{-cat} := \mathrm{Psh}^\infty(\Theta_n)_{\mathrm{W}_n}.
$$

Remark that the $(\infty, 1)$-category $(\infty, 0)$-cat is equivalent to $\infty$-grd. Proposition 4.2.1.35 implies that $(\infty, n)$-cat identifies itself with the full sub $(\infty, 1)$-category of $\mathrm{Psh}^\infty(\Delta[\Theta_{n-1}])$ of $\mathrm{M}_n$-local objects:

$$
(\infty, n)\text{-cat} \sim \mathrm{Psh}^\infty(\Delta[\Theta_{n-1}])_{\mathrm{M}_n}.
$$

The inclusion $i_n : \Theta_n \to \Theta$ fits in an adjunction

$$
\tau_n^i : \Theta \xrightarrow{\perp} \Theta_n : i_n
$$

where the left adjoint sends $\mathbf{D}_k$ on $\mathbf{D}_{\min(n,k)}$. By extension by colimits, this induces an adjoint pair

$$
\tau_n^i : \mathrm{Psh}^\infty(\Theta) \xrightarrow{\perp} \mathrm{Psh}^\infty(\Theta_n) : i_n. \tag{4.2.1.37}
$$

where the two functors are colimit preserving. As the image of every morphism of $\mathrm{W}$ by $\tau_n^i$ is in $\mathrm{W}_n$ or is an equivalence, and as the image of $\mathrm{W}_n$ by $i_n$ is included in $\mathrm{W}$, the previous adjunction induces by localization an adjunction

$$
\tau_n^i : (\infty, \omega)\text{-cat} \xrightarrow{\perp} (\infty, n)\text{-cat} : i_n \tag{4.2.1.38}
$$

where the two adjoints are colimit preserving. The left adjoint is called the *intelligent n-truncation*.

**Proposition 4.2.1.39.** *The functor $i_n : (\infty, n)\text{-cat} \to (\infty, \omega)\text{-cat}$ is fully faithful.*

*Proof.* We have to check that the unit of the adjunction (4.2.1.38) is an equivalence. As the two functors preserve colimits, we have to show that the restriction to $\Theta$ of the unit is an equivalence which is obvious. $\square$

Being colimit preserving, the functor $i_n$ is also part of an adjunction

$$
i_n : (\infty, n)\text{-cat} \xrightarrow{\perp} (\infty, \omega)\text{-cat} : \tau_n \tag{4.2.1.40}
$$

The right adjoint is called the *n-truncation*.

We will identify objects of $(\infty, n)$-cat with their image in $(\infty, \omega)$-cat and we will then also note by $\tau_n$ and $\tau_n^i$ the composites $i_n\tau_n^i$ and $i_n\tau_n^i$.

**Proposition 4.2.1.41.** *The functor $\tau_n : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}$ preserves special colimits.*

193

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

Proof. As  \( i_{n} \)  preserves representable objects, the functor  \( \tau_{n}:(\infty,\omega) \) -cat  \( \rightarrow(\infty,n) \) -cat preserves special colimits. As  \( i_{n}:\mathrm{Psh}^{\infty}(\Theta_{n})\rightarrow\mathrm{Psh}^{\infty}(\Theta) \)  preserves colimits and W-local objects, this concludes the proof. ☐

Proposition 4.2.1.42. Let \( C \) be an \( (\infty, \omega) \)-category and \( n \) an integer. The following canonical square is cartesian

![img-199.jpeg](img-199.jpeg)

Proof. For this results we use model categories. The theorem 3.4.3.14 implies that the \((\infty, 1)\)-category \((\infty, \omega)\)-cat is presented by the category of marked simplicial sets \(\mathrm{mPsh}(\Delta)\) endowed with the model structure for \(\omega\)-complicial sets given by proposition 2.2.1.9, and the functor \(\tau_n^i: (\infty, \omega)\)-cat \(\to (\infty, \omega)\)-cat corresponds to the left Quillen functor \(\tau_n^i: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)\) given in paragraph 2.2.1.10. Remark that in this model category, for any marked simplicial set \(X\), the following square is cocartesian

![img-200.jpeg](img-200.jpeg)

As all the morphisms are cofibrations, this square is also homotopy cocartesian which concludes the proof.

4.2.1.43. The family of truncation functor induces a sequence

\[
\dots \to (\infty , n + 1) \text {-cat} \xrightarrow {\tau_ {n}} (\infty , n) \text {-cat} \to \dots \to (\infty , 1) \text {-cat} \xrightarrow {\tau_ {0}} (\infty , 0) \text {-cat}
\]

which induces an adjunction

\[
\operatorname{colim} _ {n: \mathbb {N}}: \lim _ {n: \mathbb {N}} (\infty , n) \text {-cat} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat}: (\tau_ {n}) _ {n: \mathbb {N}} \tag {4.2.1.44}
\]

where the left adjoint sends a sequence  \( (C_{n}, C_{n} \sim \tau_{n} C_{n+1})_{n:\mathbb{N}} \)  to the colimit of the induced sequence

\[
i _ {0} C _ {0} \rightarrow i _ {1} C _ {1} \rightarrow \dots \rightarrow i _ {n} C _ {n} \rightarrow \dots ,
\]

and the right adjoint sends an \((\infty, \omega)\)-category \(C\) to the sequence \((\tau_n C, \tau_n C \sim \tau_n \tau_{n+1} C)_{n:\mathbb{N}}\). Indeed, we have equivalence

\[
\begin{array}{l} \operatorname{Hom} \left(\operatorname{colim} _ {n: \mathbb {N}} i _ {n} C _ {n}, D\right) \sim \lim _ {n: \mathbb {N}} \operatorname{Hom} \left(C _ {n}, \tau_ {n} D\right) \\ \sim \mathrm{Hom} ((C _ {n}, C _ {n} \sim \tau_ {n} C _ {n + 1}) _ {n: \mathbb {N}}, (\tau_ {n} D, \tau_ {n} D \sim \tau_ {n} \tau_ {n + 1} D) _ {n: \mathbb {N}}) \\ \end{array}
\]

natural in \((C_n, C_n \sim \tau_n C_{n+1})_{n:\mathbb{N}}\) and \(D\).

194

4.2. BASIC CONSTRUCTIONS

Proposition 4.2.1.45. The adjunction (4.2.1.44) is an adjoint equivalence. As a consequence, we have an equivalence

\[
(\infty , \omega) \text {-cat} \sim \lim _ {n: \mathbb {N}} (\infty , n) \text {-cat}.
\]

Proof. According to proposition 4.2.1.27, any sequence \((C_n)_{n:\mathbb{N}}:\lim_{n:\mathbb{N}}(\infty ,n)\)-cat has a special colimit. Let \(k\) be an integer. According to proposition 4.2.1.41, this implies the equivalence

\[
\tau_ {k} (\underset {n: \mathbb {N}} {\operatorname{colim}} C _ {n}) \sim \underset {n: \mathbb {N}} {\operatorname{colim}} (\tau_ {k} C _ {n}).
\]

Furthermore, the sequence  \( (\tau_{k}C_{n})_{n:\mathbb{N}} \)  is constant after the rank k. We then have

\[
\tau_ {k} \underset {n: \mathbb {N}} {\operatorname{colim}} C _ {n} \sim \tau_ {k} C _ {n}.
\]

This directly implies that the unit of the adjunction (4.2.1.44) is an equivalence.

To conclude, one has to show that the right adjoint is conservative, i.e that a morphism \( f \) is an equivalence if and only if for any \( n \), \( \tau_{n}f \) is an equivalence. This last statement is a direct consequence of proposition 4.2.1.9.

4.2.1.46. The following proposition states that the cartesian product preserves colimits in both variables. There exists then an internal hom functor that we denote by \(\underline{\mathrm{Hom}}(-, -)\).

Proposition 4.2.1.47. The cartesian product in  \( (\infty,\omega) \) -cat preserves colimits in both variables.

We first need several lemmas:

Lemma 4.2.1.48. Let \(a, b\) be two globular sums, and \(n, m\) two integer. The colimit in \(\mathrm{Psh}^{\infty}(\Delta[\Theta])\) of the diagram

![img-201.jpeg](img-201.jpeg)

is \([a,n]\times [b,m]\)

Proof. The lemma 4.1.1.6 implies that the object

\[
K := \coprod_ {k \leq n} [ b, m ] \coprod_ {\coprod_ {k \leq n} [ a \times b, \{k \} \times [ m ] ]} [ a \times b, [ n ] \times [ m ] ]
\]

is strict. As the induced morphism  \( \coprod_{l\leq m}[a\times b,[n]\times\{l\}]\to K \) , is a monomorphism, the lemma op cit implies that the colimit of the diagram given in the statement is strict. We can then show the result in the category of set valued presheaves on  \( \Delta[\Theta] \)  and we leave this combinatorial exercise to the reader.

195

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**Lemma 4.2.1.49.** *Let $f$ be a morphism of $\mathrm{W}_1$ and $n$ an integer. The morphism $f \times [n]$ is in $\widehat{\mathrm{W}}_1$.*

*Proof.* Suppose first that $f$ is of shape $\mathrm{Sp}_m \to [m]$. Remark first that for any $k$, $[k] \times [m]$ is $\mathrm{W}_1$-local as both $[k]$ and $[m]$ are. We then have $\mathbf{F}_{\mathrm{W}_1}([k] \times [m]) \sim [k] \times [m]$. As the fibrant replacement preserves colimits and as the cartesian product in $(\infty, 1)$-categories preserves colimits, we have a sequence of equivalences in $(\infty, 1)$-cat:

$$\begin{array}{rcl} \mathbf{F}_{\mathrm{W}_1}(\mathrm{Sp}_m \times [n]) & \sim & \mathbf{F}_{\mathrm{W}_1}([1] \times [n]) \coprod_{\mathbf{F}_{\mathrm{W}_1}([0] \times [n])} \cdots \coprod_{\mathbf{F}_{\mathrm{W}_1}([0] \times [n])} \mathbf{F}_{\mathrm{W}_1}([1] \times [n]) \\ & \sim & [1] \times [n] \coprod_{[0] \times [n]} \cdots \coprod_{[0] \times [n]} [1] \times [n] \\ & \sim & [m] \times [n] \end{array}$$

By construction, the morphism $\mathrm{Sp}_m \times [n] \to \mathbf{F}_{\mathrm{W}_1}(\mathrm{Sp}_m \times [n])$ is in $\widehat{\mathrm{W}}_1$. We proceed similarly for the case $f := E^{eq} \to [0]$.

*Proof of proposition 4.2.1.47.* As the cartesian product on $\mathrm{Psh}^\infty(\Theta)$ preserves colimits in both variables, according to corollary 4.1.3.4, we then have to show that for any globular sum $a$, and any $f \in \mathrm{W}$, $f \times a$ is in $\widehat{\mathrm{W}}$.

We demonstrate by induction on $k$ that for any $f \in \mathrm{W}_k$ and any globular sum $a$, $f \times a$ is in $\mathrm{W}_k$. The case $k = 0$ is trivial as $\mathrm{W}_0$ is the singleton $\{id_{[0]}\}$.

Suppose then the statement is true at this stage $k$. We recall that we denote $(i!, i^*)$ the left and right adjoints between $\mathrm{Psh}^\infty(\Delta[\Theta])$ and $\mathrm{Psh}^\infty(\Theta)$. As $i^*$ preserves cartesian product, proposition 4.2.1.5 implies that it is enough to show that for any $f \in \mathrm{M}_{k+1}$ and any object $[b, n]$, $f \times [b, n]$ is in $\widehat{\mathrm{M}}$.

Suppose first that $f$ is of shape $[a, 1] \to [c, 1]$ for $a \to c \in \mathrm{W}_k$. According to lemma 4.2.1.48, the morphism $f \times [b, m]$ is the colimit in depth of the diagram

![img-202.jpeg](img-202.jpeg)

The lemma 1.1.3.6 and the induction hypothesis implies that all the depth morphisms are in $\widehat{M}$. By stability by colimit, this implies that $f \times [b, m]$ belongs to $\widehat{\mathrm{M}}$.

196

4.2. BASIC CONSTRUCTIONS

Suppose now that $f$ is of shape $[a, \mathrm{Sp}_n] \to [a, n]$. According to lemma 4.2.1.48, the morphism $f \times [b, m]$ is the colimit in depth of the diagram

![img-203.jpeg](img-203.jpeg)

The lemma 4.2.1.49 implies that $\mathrm{Sp}_n \times [m] \to [n] \times [m]$ is in $\widehat{\mathrm{W}}_1$. Combined with lemma 1.1.3.6, this implies that all the morphisms in depth are in $\widehat{\mathrm{M}}$. By stability by colimit, so is $f \times [b, m]$.

It remains to show the case $f = E^{eq} \to [0]$. According to lemma 4.2.1.48, the morphism $f \times [b, m]$ is the horizontal colimit of the diagram

![img-204.jpeg](img-204.jpeg)

The lemma 4.2.1.49 implies that $E^{eq} \times [m] \to [m]$ is in $\widehat{\mathrm{W}}_1$. Combined with lemma 1.1.3.6, this implies that all the vertical morphisms are in $\widehat{\mathrm{M}}$. By stability by colimit, so is $f \times [b, m]$.

**Corollary 4.2.1.50.** Let $C$ be an $(\infty, \omega)$-category, $S$ an $\infty$-groupoid, and $f : C \to S$ any morphism. The functor $f^* : (\infty, \omega)\text{-cat}_{/S} \to (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.

*Proof.* As $\mathrm{Psh}^\infty(\Theta)$ is locally cartesian closed, we just have to verify that for any cartesian squares:

![img-205.jpeg](img-205.jpeg)

if $i$ is in $\mathrm{W}$, then $j$ is in $\widehat{\mathrm{W}}$. Suppose given such cartesian squares. As $b$ is a globular form, $\tau_0^i(b) \sim 1$ and as $S$ is an $\infty$-groupoid, there exists an object $s$ of $S$ such that the

197

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

morphism \( b \to S \) factor through \( \{s\} \to S \). If we denote by \( C_s \) the fiber of \( f \) in \( \{s\} \), the morphisms \( i \) and \( j \) then fit in the following cartesian squares:

![img-206.jpeg](img-206.jpeg)

The proposition 4.2.1.47 implies that \( j \) verifies the desired property, which concludes the proof.

The following proposition implies that a natural transformation is an equivalence if and only if it is pointwise one.

Proposition 4.2.1.51. For any \((\infty, \omega)\)-categories \(X\) and \(C\), the following natural square is cartesian:

![img-207.jpeg](img-207.jpeg)

Proof. As \(\underline{\mathrm{Hom}} (\_, C)\) sends colimits to limits, we can suppose that \(X\) is of shape \(\mathbf{D}_n\) for \(n\geq 0\). Eventually, proposition 4.2.1.9 implies that pullbacks are detected on globes. We then have to show that for any integer \(m\), the following square is cartesian:

![img-208.jpeg](img-208.jpeg)

To this extent, we claim that the following square is cocartesian in  \( (\infty,\omega) \) -cat:

![img-209.jpeg](img-209.jpeg)

Applying the functor \(\underline{\mathrm{Hom}} (\_, C)\) it will prove the desired property. To show the cocartesianess of (4.2.1.52), remark that if either \(n\) or \(m\) is null, this is trivial. If not, proposition 4.2.1.26 states that \(\mathbf{D}_n\times \mathbf{D}_m\) is the colimit of the span:

\[
[ \mathbf {D} _ {n - 1}, 1 ] \vee [ \mathbf {D} _ {m - 1}, 1 ] \leftarrow [ \mathbf {D} _ {n - 1} \times \mathbf {D} _ {m - 1}, 1 ] \rightarrow [ \mathbf {D} _ {m - 1}, 1 ] \vee [ \mathbf {D} _ {n - 1}, 1 ]
\]

198

4.2. BASIC CONSTRUCTIONS

Using the two cartesian squares

![img-210.jpeg](img-210.jpeg)

![img-211.jpeg](img-211.jpeg)

this implies that the pushout of the upper span of (4.2.1.52) is then the colimit of the diagram:

\[
[ \mathbf {D} _ {n - 1}, 1 ] \leftarrow [ \mathbf {D} _ {n - 1} \times \mathbf {D} _ {m - 1}, 1 ] \rightarrow [ \mathbf {D} _ {n - 1}, 1 ] \tag {4.2.1.53}
\]

The proposition 4.2.1.42 states that the square

![img-212.jpeg](img-212.jpeg)

is cocartesian. Combined with proposition 4.2.1.47, this implies that the square

![img-213.jpeg](img-213.jpeg)

is cocartesian. As a consequence, the colimit of the span (4.2.1.53), and so of the upper span of (4.2.1.52), is  \( [D_{n-1},1]\sim D_{n} \) , which concludes the proof. □

4.2.1.54. In paragraph 1.1.1.5, for any subset S of  \( N^{*} \) , we have defined the duality  \( (\_)^{S}:(0,\omega) \) -cat  \( \rightarrow(0,\omega) \) -cat. These functors restrict to functors  \( \Theta\rightarrow\Theta \)  that induce by extension by colimit functors

\[
(\_) ^ {S}: \mathrm{Psh} ^ {\infty} (\Theta) \to \mathrm{Psh} ^ {\infty} (\Theta)
\]

which are once again called dualities. It is easy to see that this functor preserves  \( (\infty,\omega) \) -categories and then induces functors

\[
(\_) ^ {S}: (\infty , \omega) \text {-cat} \to (\infty , \omega) \text {-cat}.
\]

In particular, we have the odd duality  \( (\_)^{op} \) , corresponding to the set of odd integer, the even duality  \( (\_)^{co} \) , corresponding to the subset of non negative even integer, the full duality  \( (\_)^{\circ} \) , corresponding to  \( N^{*} \)  and the transposition  \( (\_)^{t} \) , corresponding to the singleton  \( \{1\} \) . Eventually, we have equivalences

\[
((\_) ^ {c o}) ^ {o p} \sim (\_) ^ {\circ} \sim ((\_) ^ {o p}) ^ {c o}.
\]

199

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

4.2.1.55. A morphism $f : C \to D$ is an *epimorphism* if it is in the smallest cocomplete $\infty$-groupoid of arrows of $(\infty, \omega)$-cat that includes the codiagonal $\mathbf{D}_n \coprod \mathbf{D}_n \to \mathbf{D}_n$ for any $n \geq 0$. A morphism is a *monomorphism* if it has the unique right lifting property against epimorphisms.

A morphism $i : C \to D$ is then a monomorphism if and only if for any $n$, $C_n \to D_n$ is a monomorphism. The small object argument induces a factorization system:

$$
C \to \operatorname{Im} i \to D \tag{4.2.1.56}
$$

of any morphism $i : C \to D$, where the left map is an epimorphism, and the right one is a monomorphism. The object $\operatorname{Im} i$ is called the *image of i*. We then have by construction the following result:

**Proposition 4.2.1.57.** *A morphism is an equivalence if and only if it is both a monomorphism and a epimorphism.*

**Proposition 4.2.1.58.** *The image is stable under the cartesian product.*

*Proof.* One has to show that both epimorphisms and monomorphisms are stable under the functor $\_ \times A$ for $A$ any $(\infty, \omega)$-category. For monomorphisms, it is a direct consequence of the fact that this notion has been defined with a right lifting property. For epimorphisms, as $\_ \times A$ commutes with colimit, we can reduce to show that for any $n$,

$$
(\mathbf{D}_n \coprod \mathbf{D}_n) \times A \sim \mathbf{D}_n \times A \coprod \mathbf{D}_n \times A \to \mathbf{D}_n \times A
$$

is an epimorphism. However, the $\infty$-groupoid of object $B$ such that $B \coprod B \to B$ is an epimorphism is closed by colimits and contains globes. This $\infty$-groupoid then contains all the object and so in particular $\mathbf{D}_n \times A$. $\square$

**Lemma 4.2.1.59.** *For any integer $n$, the projection $\mathbb{I} : \mathbf{D}_{n+1} \to \mathbf{D}_n$ is an epimorphism.*

*Proof.* Remark first that we have a cocartesian square:

![img-214.jpeg](img-214.jpeg)

As the left hand morphism is an epimorphism, so is the right one. By stability by left cancellation, this implies that $\partial \mathbf{D}_{n+1} \to \mathbf{D}_n$ is an epimorphism. Now, the map $\mathbb{I}$ can be

200

4.2. BASIC CONSTRUCTIONS

factored as:

![img-215.jpeg](img-215.jpeg)

which directly implies that $\mathbb{I}$ is an epimorphism.

**Proposition 4.2.1.60.** *For any integer $n$, the canonical natural transformation $id \to \tau_n^i$ is pointwise an epimorphism.*

*Proof.* This is a direct consequence of lemma 4.2.1.59.

**Proposition 4.2.1.61.** *For any integer $n$, any $(\infty, n)$-category $C$, and any $(\infty, \omega)$-category $D$, the canonical morphisms*

$$\alpha : \coprod_{C_n} \mathbf{D}_n \to C \qquad \beta : \coprod_{(n,D_n)} \mathbf{D}_n \to D$$

*are epimorphisms.*

*Proof.* Let $I$ be the image of $\alpha$. We are willing to show that the canonical morphism $j : I \to C$ is an equivalence. According to lemma 4.2.1.10, and as $j$ is a monomorphism, we have to show that $j$ has the (non unique) right lifting property against $\emptyset \to \mathbf{D}_k$ for any $k \leq n$. It is sufficient to show that $\alpha$ has the (non unique) right lifting property against $\emptyset \to \mathbf{D}_k$ for any $k \leq n$, which is obviously true. We proceed similarly for $\beta$.

**Proposition 4.2.1.62.** *Let $i : A \to B$ be an epimorphism and $n$ an integer. The canonical square*

![img-216.jpeg](img-216.jpeg)

*is cocartesian.*

*Proof.* We can reduce to the case where $i$ is $\mathbf{D}_k \coprod \mathbf{D}_k \to \mathbf{D}_k$. If $n \geq k$, it is directly true, and we then suppose $n < k$. In this case, the colimit of the span:

$$\mathbf{D}_n \coprod \mathbf{D}_n \leftarrow \mathbf{D}_k \coprod \mathbf{D}_k \to \mathbf{D}_k$$

is $\mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$. The proposition 4.2.1.42 implies that this pushout is $\mathbf{D}_n$, which concludes the proof.

201

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES---

**4.2.1.63.** A functor $f : C \to D$ is *fully faithful* if for any pair of objects $a, b \in C$, the induced morphism $\hom_C(a, b) \to \hom_D(fa, fb)$ is an equivalence.

**Proposition 4.2.1.64.** *A functor is fully faithful if and only if it has the unique right lifting property against $\{0\} \coprod \{1\} \to \mathbf{D}_n$ for $n > 0$.*

*Proof.* Let $f$ be a functor having the unique right lifting property against $\{0\} \coprod \{1\} \to \mathbf{D}_n$ for $n > 0$. As $[\emptyset, 1] = \{0\} \coprod \{1\}$ and $[\mathbf{D}_n, 1] = \mathbf{D}_{n+1}$, this is equivalent to asking for any pair of objects $c, d$ and for any integer $n$, that $f(c, d)$ has the unique right lifting property against $\emptyset \to \mathbf{D}_n$, which in turn is equivalent to $f$ being fully faithful according to lemma 4.2.1.10. $\square$

**Proposition 4.2.1.65.** *Fully faithful functors are stable under limits.*

*Proof.* This is a consequence of the fact that fully faithful functors are characterized by unique right lifting properties. $\square$

**Lemma 4.2.1.66.** *Let $p : C \to D$ be a fully faithful functor. The induced morphism $C_0 \to D_0$ is a monomorphism.*

*Proof.* To this extent, we have to show that $p : C \to D$ has the unique right lifting property against $1 \coprod 1 \to 1$. This is equivalent to show that $p$ has the unique right lifting property against $\iota : 1 \coprod 1 \to E^{eq}$.

The proposition 4.2.1.64 implies that $p$ as the unique right lifting property against $1 \coprod 1 \to \mathbf{D}_1$ and $1 \coprod 1 \to \mathbf{D}_2$. By left cancellation, this implies that $p$ has the unique right lifting property against $\mathbf{D}_2 \to \mathbf{D}_1$. As $\iota$ is a composition of pushouts along $1 \coprod 1 \to \mathbf{D}_1$ and $\mathbf{D}_2 \to \mathbf{D}_1$, this directly concludes the proof. $\square$

**Proposition 4.2.1.67.** *A morphism $f : C \to D$ is an equivalence if and only if it is fully faithful and induces a surjection on objects.*

*Proof.* This is necessary. Suppose that $f$ is fully faithful. According to 4.2.1.64, for any $n > 0$, $f_n : C_n \to D_n$ is an equivalence. If $f$ induces a surjection on objects, lemma 4.2.1.66 implies that $f_0 : C_0 \to D_0$ is an equivalence. We can then apply proposition 4.2.1.9. $\square$

## 4.2.2 Discrete Conduché functors

**4.2.2.1.** We denote $\nabla_{k,n}$ the unique globular morphism between $\mathbf{D}_n$ and $\mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$. A morphism $f : C \to D$ between $(\infty, \omega)$-categories is a *discrete Conduché functor* if it has the unique right lifting property against units $\mathbb{I}_{n+1} : \mathbf{D}_{n+1} \to \mathbf{D}_n$ for any integer $n$, and against compositions $\nabla_{k,n} : \mathbf{D}_n \to \mathbf{D}_n \coprod_{\mathbf{D}_k} \mathbf{D}_n$ for any pair of integers $k \leq n$.

202

4.2. BASIC CONSTRUCTIONS

Lemma 4.2.2.2. The two following full sub \(\infty\)-groupoids of morphisms of \((\infty, \omega)\)-cat are equivalent:

(1) The smallest cocomplete full sub \(\infty\)-groupoid of morphisms containing the family of morphism \(\{\mathbb{I}_{n+1}:\mathbf{D}_{n+1}\to\mathbf{D}_n,\}\) and the family \(\{\nabla_{k,n}:\mathbf{D}_n\to\mathbf{D}_n\coprod_{\mathbf{D}_k}\mathbf{D}_n k\leq n\}\).
(2) The smallest cocomplete full sub \(\infty\)-groupoid of morphisms containing algebraic morphisms of \(\Theta\) (this notion is defined in paragraph 1.1.2.9).

Proof. For any pair of integers  \( k \leq n \) ,  \( I_{n+1} \)  and  \( \nabla_{k,n} \)  are algebraic morphisms. This directly induces the inclusion of the first  \( \infty \) -groupoid in the second one. To conclude, one has to show that every algebraic morphism  \( i : a \to b \)  is contained in the first  \( \infty \) -groupoid.

We proceed by induction on  \( |a| + |b| \) . Suppose first that there exists n such that  \( a = D_{n} \) . In this case two cases have to be considered. Either n > 0 and i factors as  \( D_{n} \xrightarrow{I_{n}} D_{n-1} \xrightarrow{j} b \) . The result then follows by the induction hypothesis. Suppose now that i does not factor though  \( I_{n} \) . In this case, there exists k such that i factors as  \( D_{n} \xrightarrow{\nabla_{k,n}} D_{n} \coprod_{D_{k}} D_{n} \xrightarrow{j} b \) . The unique factorization system between algebraic and globular morphisms given in proposition 1.1.2.11 produces a diagram

![img-217.jpeg](img-217.jpeg)

where arrows labeled by  \( \hookrightarrow \)  are globular and the other ones are algebraic. Remark that we have a cocartesian square in  \( (\infty,1) \) -category of arrows of  \( (\infty,\omega) \) -cat:

![img-218.jpeg](img-218.jpeg)

is cocartesian. As  \( j_{0} \) ,  \( j_{1} \)  and  \( j_{2} \)  are in the first  \( \infty \) -groupoid by induction hypothesis, so is j. By stability by composition, the morphism i is then in the first  \( \infty \) -groupoid.

Suppose now that the domain of  \( i : a \to b \)  is not a globe. Using once again the unique factorization system between algebraic and globular, we can construct a functor  \( \mathrm{Sp}_{a} \to \mathrm{Arr}(\Theta) \)  whose value on  \( D_{n} \hookrightarrow a \)  is given by the unique algebraic morphism j

203

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

fitting in a commutative square

![img-219.jpeg](img-219.jpeg)

where arrows labeled by $\hookrightarrow$ are globular. By induction hypothesis, $j$ is in the first $\infty$-groupoid. The colimit of $\mathrm{Sp}_a \to \mathrm{Arr}(\Theta) \to \mathrm{Arr}((\infty, \omega)\text{-cat})$ is then in the first $\infty$-groupoid. As this colimit is $i$, this concludes the proof. $\square$

**Proposition 4.2.2.3.** *A morphism $f : X \to Y$ is a discrete Conduché functor if and only if it as the unique right lifting property against algebraic morphism of $\Theta$ (this notion is defined in paragraph 1.1.2.9).*

*Proof.* Given a morphism $f$, the full sub $\infty$-groupoid of morphisms having the unique left lifting property against $f$ is cocomplete. The result is then a direct implication of lemma 4.2.2.2. $\square$

**Example 4.2.2.4.** The proposition 1.1.2.11 implies that a morphism $a \to b$ between globular sums is a discrete Conduché functor if and only if it is globular.

**Lemma 4.2.2.5.** *Let $p : C \to a$ be discrete Conduché functor with $a$ a globular sum. We denote by $(\Theta_{/p})^{Cd}$ the full sub $(\infty, 1)$-category of $\Theta_{/p}$ whose objects are triangles*

![img-220.jpeg](img-220.jpeg)

*where every arrow is a discrete Conduché functor. The canonical inclusion of $(\infty, 1)$-category $\iota : (\Theta_{/p})^{Cd} \to \Theta_{/p}$ is final.*

*Proof.* To prove this statement, we will endow $\iota$ with a structure of right deformation retract. We then first build a right inverse of $\iota$. Any triangle

![img-221.jpeg](img-221.jpeg)

induces a diagram of shape

![img-222.jpeg](img-222.jpeg)

204

4.2. BASIC CONSTRUCTIONS

where $b'$ is obtained in factorizing $b \to a$ in a algebraic morphism followed by a globular morphism, and $l$ comes from the unique right lifting property of $p$ against algebraic morphisms. By right cancellation, this implies that $l$ is a discrete Conduché functor.

As these two operations are functorial, this defines a retraction $r: \Theta_{/p} \to (\Theta_{/p})^{Cd}$ sending the triangle spotted by $b, C$ and $a$ to the triangle spotted by $b', C$ and $a$. Moreover, this retraction comes along with a natural transformation $id \to r\iota$. As right deformation retracts are final, this concludes the proof.

**Lemma 4.2.2.6.** *Let $p: C \to D$ be a discrete Conduché functor. Then for any globular sums $a$, and any cartesian squares in $\mathrm{Psh}^{\infty}(\Theta)$:*

![img-223.jpeg](img-223.jpeg)

*the morphism $j$ is in $\widehat{\mathrm{W}_{\mathrm{Seg}}}$.*

*Proof.* By stability under pullback, the morphism $p'$ is a discrete Conduché functor. Taking the notations of lemma 4.2.2.5, $p'$ is equivalent to $\operatorname{colim}_{(\Theta_{/p})^{Cd}} b \to a$ where this colimit is taken in $\mathrm{Psh}^{\infty}(\Theta)_{/a}$. As $\mathrm{Psh}^{\infty}(\Theta)$ is locally cartesian closed and as $\widehat{\mathrm{W}}$ is by definition closed by colimits, we can then reduce to the case where $p'$ is a discrete Conduché functor between globular sums, i.e a globular morphism $b \to a$. In this case, the following canonical square is a pullback

![img-224.jpeg](img-224.jpeg)

and this concludes the proof.

**Lemma 4.2.2.7.** *Consider a cartesian square*

![img-225.jpeg](img-225.jpeg)

*in $\mathrm{Psh}^{\infty}(\Theta)$. The morphism $j$ is in $\widehat{\mathrm{W}}$.*

*Proof.* If we are in the case $n = 0$, this directly follows from the preservation of $\mathrm{W}$ by cartesian product, demonstrated in the proof of proposition 4.2.1.47. We now suppose

205

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

the result is true at stage \( n \), and we first show that for any square

![img-226.jpeg](img-226.jpeg)

in \(\mathrm{Psh}^{\infty}(\Delta[\Theta])\), \(j\) is in \(\widehat{\mathrm{M}}\). As \(\mathrm{Psh}^{\infty}(\Delta[\Theta])\) is locally cartesian closed and \(\widehat{\mathrm{M}}\) closed under colimits, one can suppose that \(Y\) is of shape \([a,k]\) and we denote \(f:[k]\to [1]\) the morphism induced by \(p\). By stability under pullback, \(X\) is then set-valued. Furthermore, we can then check in \(\mathrm{Psh}(\Delta[\Theta])\) that this presheaf fits in a cocartesian square:

![img-227.jpeg](img-227.jpeg)

By induction hypothesis \([\Sigma^n E^{eq} \times_{\mathbf{D}_n} a, l] \to [a, l]\) is in \(\widehat{\mathrm{M}}\) for any integer \(l\). As \(X \to [a, k]\) is the colimit in depth of the diagram

![img-228.jpeg](img-228.jpeg)

this implies that this morphism is in \(\widehat{\mathrm{M}}\).

We now return to  \( \infty \) -presheaves on  \( \Theta \) . We recall that we denote by  \( (i_{!}, i^{*}) \)  the adjunction between  \( \mathrm{Psh}^{\infty}(\Delta[\Theta]) \)  and  \( \mathrm{Psh}^{\infty}(\Theta) \) . Suppose given a cartesian square:

![img-229.jpeg](img-229.jpeg)

This induces two squares

![img-230.jpeg](img-230.jpeg)

206

4.3. GRAY OPERATIONS

Where the cartesianess of the left square comes from the fact that $i^*$ preserves cartesian squares as it is a right adjoint. We just have demonstrated that $i^*j$ is in $\widehat{\mathbf{M}}$. Using proposition 4.2.1.5, and by left cancellation, the right square implies that $j$ is in $\widehat{W}$, which concludes the proof.

**Proposition 4.2.2.8.** *Let $p : C \to D$ be a functor between $(\infty, \omega)$-categories. Then for any globular sums $a$, and any cartesian squares in $\mathrm{Psh}^\infty(\Theta)$:*

$$
\begin{array}{c}
C'' \xrightarrow{j} C' \longrightarrow C \\
\downarrow \quad \downarrow \quad \downarrow \quad \downarrow^p \\
\Sigma^n E^{eq} \longrightarrow \mathbf{D}_n \longrightarrow D
\end{array}
$$

*the morphism $j$ is in $\widehat{W}$.*

*Proof.* This is a direct consequence of lemma 4.2.2.7.

**Theorem 4.2.2.9.** *Let $f : C \to D$ be a discrete Conduché functor. The pullback functor $f^* : (\infty, \omega)\text{-cat}_{/D} \to (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.*

*Proof.* As $\mathrm{Psh}^\infty(\Theta)$ is locally cartesian closed, we can use the corollary 4.1.3.4. The hypotheses are provided by lemmas 4.2.2.6 and proposition 4.2.2.8.

## 4.3 Gray Operations

### 4.3.1 Gray operations on $(\infty, \omega)$-categories

Theorem 3.4.3.14 states that the $(\infty, 1)$-category $(\infty, \omega)$-cat is represented by the model category of marked simplicial sets given in proposition 2.2.1.9 and the functor $\mathrm{N} : (0, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}$ corresponds to the Street nerve $\mathrm{N} : (\infty, \omega)\text{-cat} \to \mathrm{mPsh}(\Delta)$.

An important feature of this model category is that it admits a monoidal structure $\otimes$ given by the *Gray tensor product*. Furthermore, proposition 2.2.2.7 ensures that this operation commutes with colimits in both variables. The induced functor

$$
\_ \otimes [1] : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}
$$

is called the *Gray cylinder*. We will show later, in corollary 4.3.3.21, that we have a natural diagram

$$
\begin{array}{ccc}
(C \otimes \{1\})^\circ & \longrightarrow & (C \otimes [1])^\circ \longleftarrow & (C \otimes \{0\})^\circ \\
\downarrow \sim & & \downarrow \sim & & \downarrow \sim \\
C^\circ \otimes \{0\} & \longrightarrow & C^\circ \otimes [1] \longleftarrow & C^\circ \otimes \{1\}
\end{array}
$$

207

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

We denote by

\[
(\infty , \omega) \text {-cat} \rightarrow (\infty , \omega) \text {-cat}
\]

\[
C \mapsto C ^ {[ 1 ]}
\]

the right adjoint of the Gray cylinder.

Eventually, recall that we have a natural transformation  \( C \otimes [1] \to [C, 1] \)  whose restriction to  \( C \otimes \{0\} \)  (resp. to  \( C \otimes \{1\} \) ) is constant on  \( \{0\} \)  (resp. on  \( \{1\} \) ), and such that the following induced square is cocartesian:

\[
\begin{array}{c} C \otimes \{0, 1 \} \longrightarrow C \otimes [ 1 ] \\ \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \tag {4.3.1.1}
\]

##### 4.3.1.2. We define the Gray cone and the Gray o-cone:

\[
\begin{array}{c c c c c c c c} (\infty , \omega) \text {-cat} & \to & (\infty , \omega) \text {-cat} _ {\bullet} & (\infty , \omega) \text {-cat} & \to & (\infty , \omega) \text {-cat} _ {\bullet} \\ C & \mapsto & C \star 1 & C & \mapsto & 1 \stackrel {c o} {\star} C \end{array}
\]

where \(C\star 1\) and \(1\stackrel {co}{\star}C\) are defined as the following pushout:

\[
\begin{array}{c c} C \otimes \{1 \} \longrightarrow C \otimes [ 1 ] & C \otimes \{0 \} \longrightarrow C \otimes [ 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \qquad \qquad \qquad \qquad \Big \downarrow \\ 1 \longrightarrow C \star 1 & 1 \longrightarrow 1 ^ {c o} \star C \end{array}
\]

The corollary 4.3.3.21 will imply an invertible natural transformation

\[
C \star 1 \sim (1 ^ {c o} \star C ^ {\circ}) ^ {\circ}.
\]

We will denote by

\[
\begin{array}{c c c c c c c c} (\infty , \omega) \text {-cat} _ {\bullet} & \to & (\infty , \omega) \text {-cat} & (\infty , \omega) \text {-cat} _ {\bullet} & \to & (\infty , \omega) \text {-cat} \\ (C, c) & \mapsto & C _ {/ c} & (C, c) & \mapsto & C _ {c /} \end{array}
\]

the right adjoints of the Gray cone and the Gray o-cone, respectively called the slice of C over c and the slice of C under c. The corollary 4.3.3.21 will imply an invertible natural transformation

\[
C _ {/ c} \sim (C _ {c /} ^ {\circ}) ^ {\circ}.
\]

Given an \((\infty, \omega)\)-category \(C\), and two objects \(c, d\), we have by construction two cartesian squares:

\[
\begin{array}{c c} \hom_ {C} (c, d) \longrightarrow C _ {/ d} & \hom_ {C} (c, d) \longrightarrow C _ {c /} \\ \Big \downarrow \qquad \qquad \qquad \Big \downarrow & \Big \downarrow \\ \{c \} \longrightarrow C & \{d \} \longrightarrow C \end{array}
\]

208

4.3. GRAY OPERATIONS

4.3.1.3. As explained in section 2.2.4, the functor \(\pi_0\) induces canonical equivalences

\[
\pi_ {0} (C \otimes [ 1 ]) \cong \pi_ {0} (C) \otimes [ 1 ] \quad \pi_ {0} (C \star 1) \cong \pi_ {0} (C) \star 1 \quad \pi_ {0} (1 \stackrel {c o} {\star} C) \cong 1 \stackrel {c o} {\star} \pi_ {0} (C)
\]

natural in C. We will show in theorem 4.3.3.26 that the nerve  \( N : (0, \omega) \) -cat  \( \rightarrow (\infty, \omega) \) -cat also preserves the Gray operations. As a consequence, we obtain the following examples of Gray operations:

Example 4.3.1.4. The  \( (\infty,\omega) \) -category  \( D_{1}\otimes[1] \)  corresponds to the polygraph

![img-231.jpeg](img-231.jpeg)

The \((\infty, \omega)\)-category \(\mathbf{D}_2 \otimes [1]\) corresponds to the polygraph

![img-232.jpeg](img-232.jpeg)

Example 4.3.1.5. The \((\infty, \omega)\)-categories \(\mathbf{D}_1 \star 1\) and \(1 \stackrel{co}{\star} \mathbf{D}_1\) correspond respectively to the polygraphs:

![img-233.jpeg](img-233.jpeg)

![img-234.jpeg](img-234.jpeg)

The \((\infty, \omega)\)-categories \(\mathbf{D}_2 \star 1\) and \(1 \stackrel{co}{\star} \mathbf{D}_2\) correspond respectively to the polygraphs:

![img-235.jpeg](img-235.jpeg)

![img-236.jpeg](img-236.jpeg)

4.3.1.6. In section 2.3 are shown several equations fulfilled by the Gray cylinder, the Gray cone, and the Gray o-cone, that we recall here. For every  \( (\infty,\omega) \) -category C, there is a natural identification between  \( [C,1]\otimes[1] \)  and the colimit of the following diagram

\[
[ 1 ] \vee [ C, 1 ] \longleftarrow [ C \otimes \{0 \}, 1 ] \longrightarrow [ C \otimes [ 1 ], 1 ] \longleftarrow [ C \otimes \{1 \}, 1 ] \longrightarrow [ C, 1 ] \vee [ 1 ] \tag {4.3.1.7}
\]

There is also a natural identification between \(1 \stackrel{co}{\star} [C, 1]\) and the colimit of the diagram

\[
[ 1 ] \vee [ C, 1 ] \longleftarrow [ C, 1 ] \longrightarrow [ C \star 1, 1 ] \tag {4.3.1.8}
\]

209

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

and $[C, 1] \star 1$ and the colimit of the diagram

$$[1 \stackrel{\text{co}}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1] \quad (4.3.1.9)$$

In each of the three previous diagrams, morphisms $[C, 1] \rightarrow [1] \vee [C, 1]$ and $[C, 1] \rightarrow [C, 1] \vee [1]$ are the unique ones preserving extremal points.

**Remark 4.3.1.10.** It is worth noticing the great similarity of these equations with the one given in theorems 1.2.3.13 and 1.2.3.14

**4.3.1.11.** Let $C$ be an $(\infty, \omega)$-category and $K$ a $(\infty, 1)$-category. There is a canonical morphism $C \otimes K \rightarrow C \times K$. In a way, one can see $C \times K$ as an intelligent truncated version of the Gray tensor product $C \otimes K$. We will make this intuition precise by constructing a hierarchy of Gray tensor products with $(\infty, 1)$-categories. For $k \in \mathbb{N} \cup \{\omega\}$, we define the functor

$$\begin{array}{rcl} (\infty, \omega)\text{-cat} \times (\infty, 1)\text{-cat} & \rightarrow & (\infty, \omega)\text{-cat} \\ (C, K) & \mapsto & C \otimes_k K \end{array}$$

where $C \otimes_k K$ fits in the cocartesian square

$$\begin{array}{ccc} \text{colim}_{n \geq k}(\tau_n C) \otimes K & \longrightarrow & C \otimes K \\ \downarrow & & \downarrow \\ \text{colim}_{n \geq k} \tau_n^i((\tau_n C) \otimes K) & \longrightarrow & C \otimes_k K \end{array}$$

The induced functors $\_ \otimes_k [1] : (\infty, \omega)\text{-cat} \rightarrow (\infty, \omega)\text{-cat}$ are called the *k-Gray cylinder*. Formula (4.3.1.7) implies that for every $(\infty, \omega)$-category $C$, there is a natural identification between $[C, 1] \otimes_{k+1} [1]$ and the colimit of the following diagram

$$[1] \vee [C, 1] \longleftarrow [C \otimes_k \{0\}, 1] \longrightarrow [C \otimes_k [1], 1] \longleftarrow [C \otimes_k \{1\}, 1] \longrightarrow [C, 1] \vee [1] \quad (4.3.1.12)$$

Remark that the endofunctor $\_ \otimes_0 [1]$ is the identity, the first assertion of lemma 2.2.2.8 implies that the endofunctor $\_ \otimes_1 [1]$ is equivalent to $\_ \times [1]$, and the endofunctor $\otimes_\omega [1]$ is just the normal Gray cylinder.

**Proposition 4.3.1.13.** *For any integer $k > 0$, $\_ \otimes_k [1]$ preserves colimits.*

*Proof.* In order to simplify the notation, for a functor $F : (\infty, \omega)\text{-cat} \rightarrow (\infty, \omega)\text{-cat}$, the $\infty$-presheaves $\text{colim}_{\Theta/\Sigma^n E^{eq}} \iota F$, where $\iota$ in the inclusion $(\infty, \omega)\text{-cat} \rightarrow \text{Psh}^\infty(\Theta)$, will just be denoted by $F(\Sigma^n E^{eq})$.

As $\tau$ and $\tau^i$ preserves colimits in $\text{Psh}^\infty(\Theta)$ and $\widehat{\text{W}_{\text{Seg}}}$, and as $\_ \otimes [1]$ preserves colimits, we just have to show that for any $n$, $(\Sigma^n E^{eq}) \otimes_k [1] \rightarrow (\Sigma^n 1) \otimes_k [1]$ is in $\widehat{\text{W}}$.

210

4.3. GRAY OPERATIONS

We then proceed by induction on $k$. The cases $k = 0$ and $k = 1$ are trivial as $\_ \otimes_0 [1]$ is the identity and $\_ \otimes_1 [1]$ is the tensor product with $[1]$.

Suppose the result is true at the stage $k$ for $k > 1$. If $n = 0$, remark that $E^{eq} \otimes_k [1]$ (resp. $1 \otimes_k [1]$) is equivalent to $E^{eq} \otimes [1]$ (resp. $1 \otimes [1]$) and the morphism is then in $\widehat{\mathrm{W}}$. Now, if $n > 0$, formula (4.3.1.12) implies that $(\Sigma^n E^{eq}) \otimes_k [1] \to (\Sigma^n 1) \otimes_k [1]$ is the colimit in depth of the following diagram:

![img-237.jpeg](img-237.jpeg)

by induction hypothesis, and using lemma 1.1.3.6, all the morphisms in depth are in $\widehat{\mathrm{W}}$, and so is their colimit.

The functor $\_ \otimes [1]_k$ then admits a right adjoint

$$(\_)^{[1]_k} : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}.$$

4.3.1.14. We now describe a last operation that will play an essential role in the definition of lax colimit and lax limit. For any $C : (\infty, \omega)\text{-cat}$, we denote by $m_C$ the colimit preserving functor $(\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}$ whose value on a representable $[a, n]$ is $[a \times C, n]$. Remark that the assignation $C \mapsto m_C$ is natural in $C$ and that $m_1$ is the identity. We define the colimit preserving functor:

$$(\infty, \omega)\text{-cat} \times (\infty, \omega)\text{-cat} \quad \to \quad (\infty, \omega)\text{-cat}$$

$$(X, Y) \qquad \mapsto \qquad X \ominus Y$$

where for any $(\infty, \omega)$-category $C$ and any element $[b, n]$ of $\Delta[\Theta]$, $X \ominus [b, n]$ is the following pushout:

$$\coprod_{k \le n} m_b(C \otimes \{k\}) \longrightarrow m_b(C \otimes [n])$$
$$\updownarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$
$$\coprod_{k \le n} m_1(C \otimes \{k\}) \longrightarrow C \ominus [b, n]$$

211

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

By construction, the functor $\_ \ominus \_$ commutes with colimits in both variables. We also have the identification $C \ominus [1] := C \otimes [1]$.

Eventually, formula (4.3.1.7) induces a natural identification between $[C, 1] \ominus [b, 1]$ and the colimit of the following diagram

$$[b, 1] \vee [C, 1] \leftarrow [C \otimes \{0\} \times b, 1] \rightarrow [(C \otimes [1]) \times b), 1] \leftarrow [C \otimes \{1\} \times b, 1] \rightarrow [C, 1] \vee [b, 1] \tag{4.3.1.15}$$

### 4.3.2 Gray deformation retract

4.3.2.1. A left $k$-Gray deformation retract structure for a morphism $i : C \to D$ is the data of a retract $r : D \to C$, a deformation $\psi : D \otimes_k [1] \to D$, and equivalences

$$ri \sim id_C \qquad \psi_{|D \otimes_k \{0\}} \sim ir \qquad \psi_{|D \otimes_k \{1\}} \sim id_D \qquad \psi_{|C \otimes_k [1]} \sim i \operatorname{cst}_C$$

A morphism $i : C \to D$ between $(\infty, \omega)$-categories is a left $k$-Gray deformation retract if it admits a left deformation retract structure. By abuse of language, such data will just be denoted by $(i, r, \psi)$.

We define dually the notion of right $k$-Gray deformation retract structure and of right $k$-Gray deformation retract in exchanging 0 and 1 in the previous definition.

4.3.2.2. A left $k$-Gray deformation retract structure for a morphism $i : f \to g$ in the $(\infty, 1)$-category of arrows of $(\infty, \omega)$-cat is the data of a retract $r : g \to f$, a deformation $\psi : g \otimes_k [1] \to g$ and equivalences

$$ri \sim id_f \qquad \psi_{|g \otimes_k \{0\}} \sim ir \qquad \psi_{|g \otimes_k \{1\}} \sim id_D \qquad \psi_{|f \otimes_k [1]} \sim i \operatorname{cst}_C$$

A morphism $i : C \to D$ between arrows of $(\infty, \omega)$-cat is a left $k$-Gray deformation retract if it admits a left deformation retract structure. By abuse of language, such data will just be denoted by $(i, r, \psi)$.

We define dually the notion of right $k$-Gray deformation retract structure and of right $k$-Gray deformation retract in exchanging 0 and 1 in the previous definition.

Example 4.3.2.3. Let $k \in \mathbb{N} \cup \{\omega\}$ and let $C$ be an $(\infty, k)$-category. We consider the morphism $i : C \otimes \{0\} \to C \otimes [1]$. We define $r : C \otimes [1] \xrightarrow{C \otimes 1} C \otimes \{0\}$. Eventually, we set

$$\psi : C \otimes [1] \otimes [1] \to C \otimes ([1] \times [1]) \xrightarrow{C \otimes \phi} C \otimes [1]$$

where $\phi : [1] \times [1]$ is the morphism sending $(i, j)$ on the minimum of $i$ and $j$.

212

4.3. GRAY OPERATIONS

As $C$ is an $(\infty, k)$-category, $\psi$ factors through $C \otimes [1] \to \tau_k^i(C \otimes [1]) \sim C \otimes_k [1]$. We denote by $\phi : C \otimes_k [1] \to C \otimes \{0\}$ the induced morphism. The triple $(i, r, \phi)$ is a left $k$-Gray deformation retract structure. Conversely, $C \otimes \{1\} \to C \otimes [1]$ is a right deformation retract.

One can show similarly that $1 \to 1 \stackrel{co}{\star} C$ is a left $k$-Gray deformation retract, and $1 \to C \star 1$ is a right $k$-Gray deformation retract.

4.3.2.4. The $\infty$-groupoid of left and right Gray retracts enjoys many stability properties:

Proposition 4.3.2.5. Let $(i_a, r_a, \psi_a)$ be a natural family of left (resp. right) $k$-Gray deformation retract structures indexed by an $(\infty, 1)$-category $A$. The triple $(\operatorname{colim}_A i_a, \operatorname{colim}_A r_a, \operatorname{colim}_A \psi_a)$ is a left (resp. right) $k$-Gray deformation retract structure.

Proof. This is an immediate consequence of the fact that $_\otimes_k [1]$ preserves colimits. $\square$

Proposition 4.3.2.6. Suppose that we have a diagram

$$\begin{array}{c} X \xrightarrow{p} Y \xleftarrow{q} Z \\ \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \\ X \xrightarrow{p'} Y' \xleftarrow{q'} Z' \end{array}$$

such that $p \to p'$ and $q \to q'$ are left (resp. right) $k$-Gray deformation retract. The induced square $q^*p \to (q')^*p'$ is a left (resp. right) $k$-Gray deformation retract.

Proof. The proof is an easy diagram chasing. $\square$

Proposition 4.3.2.7. If $p \to p'$ and $p' \to p''$ are two left (resp. right) $k$-Gray deformation retracts, so is $p \to p''$.

Proof. The proof is an easy diagram chasing. $\square$

4.3.2.8. The two following propositions show how the shifting of dimension preserves Gray transformation retract.

Proposition 4.3.2.9. Let $(i : C \to D, r, \psi)$ be a left (resp. right) $(k + 1)$-Gray deformation structure. For any $x : C$ and $y : D$ (resp. $x : D$ and $y : C$), the morphism

$$\begin{array}{c} \hom_C(x, ry) \xrightarrow{i} \hom_D(ix, iry) \xrightarrow{\psi_{y_i}} \hom_D(ix, y) \\ (resp. \hom_C(rx, y) \xrightarrow{i} \hom_D(irx, iy) \xrightarrow{\psi_{x_i}} \hom_D(x, iy)) \end{array}$$

213

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

is a right (resp. left) \(k\)-Gray deformation retract, whose retract is given by

\[
\hom_ {D} (i x, y) \xrightarrow {r} \hom_ {C} (x, r y)
\]

\[
(r e s p. \hom_ {D} (x, i y) \xrightarrow {r} \hom_ {C} (r x, y))
\]

Proof. By currying \(\psi\), this induces a diagram

![img-238.jpeg](img-238.jpeg)

For any pair of objects \((z,y)\) of \(D\), according to formula (4.3.1.12), this induces a diagram

![img-239.jpeg](img-239.jpeg)

If \(z\) is of shape \(ix\), the diagram becomes

![img-240.jpeg](img-240.jpeg)

By decurrying, this induces a morphism \(\phi : \mathrm{hom}_D(ix, y) \otimes_k [1] \to \mathrm{hom}_D(ix, y)\). We leave the reader verify that the triple \((\psi_{y_1}i, r, \phi)\) is a right \(k\)-Gray deformation retract structure. We proceed similarly for the other case.

Proposition 4.3.2.10. For any left (resp. right) \((k + 1)\)-Gray deformation retract between \(p\) and \(p'\):

![img-241.jpeg](img-241.jpeg)

214

4.3. GRAY OPERATIONS

and for any pair of objects $x : C$ and $y : D$ (resp. $x : D$ and $y : C$), the outer square of the following diagram

$$
\begin{array}{c}
\hom_C(x, ry) \xrightarrow{i} \hom_D(ix, iry) \xrightarrow{\psi_{y!}} \hom_D(ix, y) \\
\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\
\hom_{C'}(px, pr'y) \xrightarrow{i'} \hom_{D'}(p'i'x, p'i'r'y) \xrightarrow{\psi'_{p'y!}} \hom_{D'}(p'i'x, p'y)
\end{array}
$$

(resp.

$$
\begin{array}{c}
\hom_C(rx, y) \xrightarrow{i} \hom_D(irx, iy) \xrightarrow{\psi_{x!}} \hom_D(x, iy) \\
\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\
\hom_{C'}(pr'x, py) \xrightarrow{i'} \hom_{D'}(p'i'r'x, p'i'y) \xrightarrow{\psi'_{p'x!}} \hom_{D'}(p'x, p'i'y)
\end{array}
$$

is a left (resp. right) $(k + 1)$-Gray deformation retract, whose retract is given by

$$
\begin{array}{c}
\hom_D(ix, y) \xrightarrow{r} \hom_C(x, ry) \\
\downarrow \qquad \qquad \qquad \downarrow \\
\hom_{D'}(p'i'x, p'y) \xrightarrow{r'} \hom_{C'}(px, pr'y)
\end{array}
$$

$$
\begin{array}{c}
(\text{resp.} \hom_D(x, iy) \xrightarrow{r} \hom_C(rx, y) \\
\downarrow \qquad \qquad \qquad \downarrow \\
\hom_{D'}(p'x, p'i'y) \xrightarrow{r'} \hom_{C'}(pr'x, py)
\end{array}
$$

Proof. This comes from the fact that the construction of the retraction and the deformation in the previous proposition was functorial. $\square$

**Proposition 4.3.2.11.** If $i$ is a left $k$-Gray deformation retract, $[i, 1]$ is a right $(k + 1)$-Gray deformation retract. Conversely, if $i$ is a right $k$-Gray deformation retract, $[i, 1]$ is a left $(k + 1)$-Gray deformation retract morphism.

Proof. Let $(i : C \to D, r, \phi)$ be a left $k$-Gray deformation retract structure. We define the morphism $\psi : [D, 1] \otimes_{k+1} [1] \to [D, 1]$ as the horizontal colimit of the following diagram:

$$
\begin{array}{c}
[1] \vee [D, 1] \longleftarrow [D \otimes_k \{0\}, 1] \longrightarrow [D \otimes_k [1], 1] \longleftarrow [D \otimes_k \{1\}, 1] \longrightarrow [D, 1] \vee [1] \\
\searrow \xrightarrow{[r, 1] \downarrow} [C, 1] \xrightarrow{[i, 1]} [D, 1] \xleftarrow{[\phi, 1] \downarrow} [D, 1] \xleftarrow{\downarrow [id, 1]} [D, 1]
\end{array}
$$

Eventually, remark that the triple $([i, 1], [r, 1], \psi)$ is a right $(k + 1)$-Gray deformation retract. The other assertion is demonstrated similarly. $\square$

**Proposition 4.3.2.12.** For any integer $n$, if $n$ is even, $i_n^- : \mathbf{D}_n \to \mathbf{D}_{n+1}$ is a left $n$-Gray deformation retract and $i_n^+ : \mathbf{D}_n \to \mathbf{D}_{n+1}$ is a right $n$-Gray deformation retract, and if $n$ is odd, $i_n^-$ is a right $n$-Gray deformation retract and $i_n^+$ is a left $n$-Gray deformation retract.

215

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

Proof. It is obvious that $\{0\} \to [1]$ is a left 1-Gray deformation retract and $\{1\} \to [1]$ is a right 1-Gray deformation retract. A repeated application of 4.3.2.11 proves the assertion. □

Proposition 4.3.2.13. Let $a$ be a globular sum of dimension $(n+1)$. We denote by $s_n(a)$ and $t_n(a)$ the globular sum defined in paragraph 1.1.2.12.

If $n$ is even, $s_n(a) \to a$ is a left $n$-Gray deformation retract and $t_n(a) \to a$ is a right $n$-Gray deformation retract, and if $n$ is odd, $s_n(a) \to a$ is a right $n$-Gray deformation retract and $t_n(a) \to a$ is a left $n$-Gray deformation retract.

Proof. This is a direct consequence of proposition 4.3.2.12 and 4.3.2.5 as $s_n(a) \to a$ is a composition of pushouts of $i_n^- : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$. The other assertion is proved similarly. □

### 4.3.3 Gray operations and strict objects

Recall that we have an adjunction

$$\pi_0 : (\infty, \omega)\text{-cat} \xrightarrow{\perp} (0, \omega)\text{-cat} : \mathrm{N}$$

An $(\infty, \omega)$-category lying in the image of the nerve functor $\mathrm{N}$ is called strict. As explained in example 11 of [Ver06], $\pi_0$ preserves Gray tensor product, and so also the suspension, the Gray cone, and the Gray o-cone.

The strict categories play an important role as they allow us to make explicit calculations. In particular, it will be very useful to know which cocontinuous functors preserve them.

Proposition 4.3.3.1. An $(\infty, \omega)$-category $C$ is strict if and only if $C_0$ is a set and for any pair of objects $x, y$, $\hom_C(x, y)$ is strict.

Proof. By definition, an $(\infty, \omega)$-category is strict if and only if, for any globular sum $[\mathbf{b}, n]$, $\operatorname{Hom}([\mathbf{b}, n], C)$ is a set. However, as $C$ is W-local, we have an equivalence between $\operatorname{Hom}([\mathbf{b}, n], C)$ and

$$\coprod_{x_0, x_1, \dots, x_n \in C_0} \operatorname{Hom}(b_1, \hom_C(x_0, x_1)) \times \dots \times \operatorname{Hom}(b_n, \hom_C(x_{n-1}, x_n))$$

As all the objects of the previous expression are set by hypothesis, and as the inclusion of set into $\infty$-groupoid is stable under coproduct and product, $\operatorname{Hom}([b, n], C)$ is a set. □

Proposition 4.3.3.2. If $C$ is a strict $(\infty, \omega)$-category, so is $[C, 1]$.

Proof. There is an obvious equivalence $[\mathrm{N}_{\_,} 1] \sim \mathrm{N}_{[\_,} 1]$ which directly implies the result. □

216

4.3. GRAY OPERATIONS

**Lemma 4.3.3.3.** *For any $n$, $\mathbf{D}_n \otimes [1]$, $\mathbf{D}_n \star 1$ and $1 \stackrel{co}{\star} \mathbf{D}_n$ are strict.*

*Proof.* We proceed by induction on $n$. The result is obviously true for $n = 0$. Suppose it is true as the stage $n$. According to equation (4.3.1.7), $\mathbf{D}_n \otimes [1]$ is the colimit of the following diagram

$$[1] \vee \mathbf{D}_n \longleftarrow \mathbf{D}_n \longrightarrow [\mathbf{D}_{n-1} \otimes [1], 1] \longleftarrow \mathbf{D}_n \longrightarrow \mathbf{D}_n \vee [1] \tag{4.3.3.4}$$

The induction hypothesis and proposition 4.3.3.2 implies that all the objects are strict. The proposition 1.2.3.15 then implies that the diagram

$$\begin{array}{ccc} \mathbf{D}_{n-1} & \longrightarrow & \mathbf{D}_{n-1} \otimes [1] \longleftarrow \mathbf{D}_{n-1} \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [1] \longleftarrow \{1\} \end{array}$$

verifies the hypothesis of proposition 4.2.1.30. The proposition *op. cit.* then states that the colimit of (4.3.3.4) is special, which implies, according to lemma 4.1.1.6, that its colimit, which is $\mathbf{D}_n \otimes [1]$, is also strict.

We proceed similarly for the Gray cone and the Gray o-cone.

We now recall the following fundamental result of strictification:

**Theorem 4.3.3.5** (Gagna, Ozornova, Rovelli). *For any globular sum $a$, $a \star 1$ and $1 \stackrel{co}{\star} a$ are stricts.*

*Proof.* The fact that $a \star 1$ is strict is a particular case of theorem 5.2 of [GOR21]. For the second assertion, remark that we have a canonical comparison, natural in $a : \Theta$:

$$1 \stackrel{co}{\star} a \to \mathrm{N} \, \pi_0 (1 \stackrel{co}{\star} a) \sim \mathrm{N} \, \pi_0 (a^\circ \star 1)^\circ \sim (\mathrm{N} \, \pi_0 (a^\circ \star 1))^\circ \sim (a^\circ \star 1)^\circ$$

where the first equivalence is a consequence of [AM20, proposition A.22], the second comes from the commutativity of $\pi_0$ and $\mathrm{N}$ with dualities, and the last one is the (already demonstrated) first assertion. The subset of object of $\Theta$ making this comparison an equivalence is closed by colimits and, according to lemma 4.3.3.3, contains globes. This subset then contains all the globular sums. As strict objects are stable by dualities, this concludes the proof of the second assertion.

**Lemma 4.3.3.6.** *Let $\alpha$ be $-$ if $n$ is even (resp. odd) and $+$ if $n$ is odd (resp. even). Consider a cartesian square*

$$\begin{array}{ccc} C_0 & \longrightarrow & D \\ \downarrow_p & \downarrow_{\perp} & \downarrow_{p'} \\ \mathbf{D}_n & \xrightarrow{i_n^\alpha} & \mathbf{D}_{n+1} \end{array} \tag{4.3.3.7}$$

217

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

such that \( p \to p' \) is a left \( (n + 1) \)-Gray deformation retract (resp. a right \( (n + 1) \)-Gray deformation retract). Let \( C_1 \) be the \( (\infty, \omega) \)-category fitting in the pullback

\[
\begin{array}{c} C _ {1} \xrightarrow {} D \\ p \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text {   (4.3.3.8)   } \\ \mathbf {D} _ {n} \xrightarrow [ i _ {n} ^ {1 - \alpha} ]{} \mathbf {D} _ {n + 1} \end{array}
\]

Then if \(C_0\) and \(C_1\) are strict, so is \(D\).

Proof. We denote by  \( (i, r, \phi) \)  the deformation retract structure corresponding to  \( C_{0} \to D \) . We show this result by induction, and let's start with the case n = 0. This corresponds to the case where  \( C_{0} \to D \)  fits in a pullback diagram.

![img-242.jpeg](img-242.jpeg)

Let \( x, y \) be two objects of \( D \). Suppose first that \( x \) and \( y \) are over the same object of [1]. In this case, \( \mathrm{hom}_D(x, y) \) is equivalent to either \( \mathrm{hom}_{C_0}(x, y) \) or \( \mathrm{hom}_{C_1}(x, y) \) and is then strict. If \( x \) is over 1 and \( y \) over 0, the \( \infty \)-groupoid \( \mathrm{hom}_D(x, y) \) is empty. If \( x \) is over 0 and \( y \) is over 1, \( \mathrm{hom}_D(x, y) \) is equivalent to \( \mathrm{hom}_{C_0}(x, ry) \) according to 4.3.2.9 and is then strict by hypothesis. Eventually, \( \tau_0(D) \) is equivalent to \( \tau_0(C_1) \) and is then a set. According to 4.3.3.1, this implies that \( D \) is strict.

Suppose now the result is true at stage  \( (n-1) \) . Let  \( p'\to p \)  be a square verifying the condition. Remark that, at the level of objects, the inclusion  \( C_{0}\to D \) , its retract, and its deformation, are the identity.

Let \( x \) and \( y \) be two objects of \( D \). As before, the only interesting case is when \( x \) is over 0 and \( y \) is over 1. In this case, applying \( \mathrm{hom}(\_, \_) \) to the square (4.3.3.7), we get a cartesian square

![img-243.jpeg](img-243.jpeg)

which is a right n-Gray deformation retract according to proposition 4.3.2.9. Applying  \( \mathrm{hom}(\_, \_) \)  to the square (4.3.3.8), we get a cartesian square

![img-244.jpeg](img-244.jpeg)

218

4.3. GRAY OPERATIONS

As $C_1$ is strict, so is $\hom_{C_1}(x,y)$. We can then apply the induction hypothesis, which implies that $\hom_D(x,y)$ is strict. As $\tau_0 D$ is equivalent to $\tau_0 C_0$, it is a set. We can apply proposition 4.3.3.1 which implies that $D$ is strict. $\square$

### 4.3.3.9. For an integer $n > 0$, we define by induction

- a left $(n + 1)$-Gray retract structure for the inclusion

$$
\mathbf{D}_n \star \emptyset \cup \mathbf{D}_{n-1} \star 1 \rightarrow \mathbf{D}_n \star 1 \tag{4.3.3.10}
$$

where the gluing is performed along $i_n^\alpha : \mathbf{D}_{n-1} \star \emptyset \rightarrow \mathbf{D}_n \star \emptyset$ with $\alpha$ being $+$ if $n$ is odd and $-$ if not,

- a right $(n + 1)$-Gray retract structure for the inclusion

$$
1 \stackrel{co}{\star} \mathbf{D}_{n-1} \cup \emptyset \stackrel{co}{\star} \mathbf{D}_n \rightarrow 1 \stackrel{co}{\star} \mathbf{D}_n \tag{4.3.3.11}
$$

where the gluing is performed along $i_n^\alpha : \emptyset \stackrel{co}{\star} \mathbf{D}_{n-1} \rightarrow \emptyset \stackrel{co}{\star} \mathbf{D}_n$ with $\alpha$ being $-$ if $n$ is odd and $+$ if not.

If $n = 1$, the first morphism corresponds to the inclusion

![img-245.jpeg](img-245.jpeg)

and the second one to the inclusion:

![img-246.jpeg](img-246.jpeg)

The propositions 4.3.2.12 and 4.3.2.5 imply that the first morphism is a left 2-Gray deformation retract and the second one a right 2-Gray deformation retract. Suppose now that these two morphisms are constructed at stage $n$. The formula (4.3.1.8) implies that $\mathbf{D}_{n+1} \star \emptyset \cup \mathbf{D}_n \star 1 \rightarrow \mathbf{D}_{n+1} \star 1$ fits in the cocartesian square

![img-247.jpeg](img-247.jpeg)

The induction hypothesis and the propositions 4.3.2.11 and 4.3.2.5 endow this morphism with a left $(n + 2)$-Gray retract structure. We constructs similarly the right $(n + 2)$-Gray retract structure for the inclusion $1 \stackrel{co}{\star} \mathbf{D}_{n-1} \cup \emptyset \stackrel{co}{\star} \mathbf{D}_n \rightarrow 1 \stackrel{co}{\star} \mathbf{D}_n$.

219

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

Proposition 4.3.3.12. Let $C$ be a strict $(\infty, \omega)$-category, $a$ a globular sum, and $f : a \to C$ any morphism. The $(\infty, \omega)$-categories $C \coprod_{a} a \star 1$ and $1 \stackrel{co}{\star} a \coprod_{a} C$ are strict.

Proof. We will prove the result by induction on the number of non-identity cells of $a$. Remark that for any globular sum $b$, there exists a globular sum $a$, an integer $n$, and a cartesian square composed of globular morphism

![img-248.jpeg](img-248.jpeg)

with $\alpha = +$ if $n$ is odd, and $\alpha = -$ if $n$ is even, and such that $l$ admits a retract $r$. As $i_{n-1}^{\alpha}$ is globular, the pullback along this morphism preserves colimits according to theorem 4.2.2.9. We then have a cartesian square:

![img-249.jpeg](img-249.jpeg)

We also define $a'$ as the pullback:

![img-250.jpeg](img-250.jpeg)

and remark that $a'$ is a globular sum. Eventually, we fix a morphism $b \to C$. As $a$ and $a'$ are sub globular sum of $b$, the number of non-identity cells in each of them is strictly less than the one of $b$. We then suppose that for any strict $(\infty, \omega)$-category $C$, and any morphism $b \to C$, the two induced $(\infty, \omega)$-category $C \coprod_{a} a \star 1$ and $C \coprod_{a'} a' \star 1$ are strict, and we are willing to show that $C \coprod_{b} b \star 1$ also is. We claim that the two following squares are cartesian

![img-251.jpeg](img-251.jpeg)

![img-252.jpeg](img-252.jpeg)

According to theorem 4.3.3.5, proposition 4.3.3.2, and the induction hypothesis, all the objects of these squares are strict. We can show the cartesianess in $(0, \omega)$-cat, where it follows from lemma 1.2.3.16. As morphism $[i_{n-1}^{-}, 1], [i_{n-1}^{+}, 1]$ are globular, the pullback

220

4.3. GRAY OPERATIONS

functors $[i_{n-1}^{-}, 1]^{*}$, $[i_{n-1}^{+}, 1]^{+}$ preserve colimits according to theorem 4.2.2.9. We then have two cartesian squares:

$$\begin{array}{ccc} C \coprod_{a} a \star 1 & \longrightarrow & C \coprod_{b} b \star 1 \\ \downarrow & & \downarrow \\ [\mathbf{D}_{n-1}, 1] & \xrightarrow{[i_{n-1}^{\alpha}, 1]} & [\mathbf{D}_{n}, 1] \end{array} \qquad \begin{array}{ccc} C \coprod_{a'} a' \star 1 & \longrightarrow & C \coprod_{b} b \star 1 \\ \downarrow & & \downarrow \\ [\mathbf{D}_{n-1}, 1] & \xrightarrow{[i_{n-1}^{-\alpha}, 1]} & [\mathbf{D}_{n}, 1] \end{array} \tag{4.3.3.13}$$

and by the induction hypothesis, the two top left objects are strict. Eventually, remark that we have a cocartesian square

$$\begin{array}{ccc} \mathbf{D}_{n} \coprod_{\mathbf{D}_{n-1}} \mathbf{D}_{n-1} \star 1 & \longrightarrow & \mathbf{D}_{n} \star 1 \\ \downarrow & & \downarrow \\ C \coprod_{a} a \star 1 & \longrightarrow & C \coprod_{b} b \star 1 \end{array}$$

and the proposition 4.3.2.5 then implies that the left square of (4.3.3.13) is a left $(n+1)$-Gray retract, and the lemma 4.3.3.6 implies that $C \coprod_{b} b \star 1$ is strict. This proves the first assertion. The second one is proved similarly.

4.3.3.14. We now want to give an analogue of proposition 4.3.3.12 for the Gray cylinder. In what follows, we will use the results of sections 5.2.3 and 5.2.2 (more precisely the proposition 5.2.3.8, the theorem 5.2.3.10 and the corollaries 5.2.3.11, 5.2.3.12). We assure the reader that this is not a tautology, as the proofs of these results are not based on the following propositions and theorems

**Proposition 4.3.3.15.** Let $a$ be a globular sum. The two following canonical squares are cartesian

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \stackrel{co}{\star} a \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [a, 1] \end{array} \qquad \begin{array}{ccc} 1 & \longrightarrow & a \star 1 \\ \downarrow & & \downarrow \\ \{1\} & \longrightarrow & [a, 1] \end{array}$$

The five squares appearing in the following canonical diagram are both cartesian and cocartesian:

$$\begin{array}{ccc} & a \otimes \{0\} & \longrightarrow & 1 \\ & \downarrow & & \downarrow \\ a \otimes \{1\} & \longrightarrow & a \otimes [1] & \longrightarrow & a \star 1 \\ \downarrow & & \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \stackrel{co}{\star} a & \longrightarrow & [a, 1] \end{array}$$

221

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

*Proof.* The five squares of the second diagram are cocartesian by construction. Furthermore, remark that all the objects appearing in the squares

![img-253.jpeg](img-253.jpeg)

are strict according to theorem 4.3.3.5 and proposition 4.3.3.2. One can the show their cartesianess in $(0, \omega)$-cat, where it follows from proposition 1.2.3.15.

By stability by right cancellation of cartesian square, it remains to show that the square

![img-254.jpeg](img-254.jpeg)

is cartesian. Using the fact that pullback along $1 \stackrel{co}{\star} a \rightarrow [a, 1]$ preserves colimits as stated by corollary 5.2.3.12, it is sufficient to show that for any globular morphism $\mathbf{D}_n \rightarrow a$, the outer square of the diagram

![img-255.jpeg](img-255.jpeg)

is cartesian. Remark that this outer square also factors as:

![img-256.jpeg](img-256.jpeg)

The cartesianess of the left square is a consequence of the preservation of colimit of the pullback along the morphism $\mathbf{D}_n \star 1 \rightarrow [\mathbf{D}_n, 1]$, and of the cartesian square provided by proposition 1.2.3.15. We recall that we can indeed use the last proposition, as we already show in lemma 4.3.3.3 that $\mathbf{D}_n \otimes [1]$, $1 \stackrel{co}{\star} \mathbf{D}_n$ and $\mathbf{D}_n \star 1$ are strict.

222

4.3. GRAY OPERATIONS

For the right hand square, all the objects are strict according to proposition 4.3.3.12. We can then show the cartesianess in $(0, \omega)$-cat, where it follows from lemma 1.2.3.16. $\square$

**Lemma 4.3.3.16.** *Let $C$ be an $(\infty, \omega)$-category, $a$ a globular sum, and $a \to C$ any morphism. The following canonical square is cartesian:*

$$\begin{array}{ccc} C \coprod_a a \otimes [1] & \longrightarrow & C \coprod_a a \star 1 \\ \downarrow & & \downarrow \\ 1 \stackrel{co}{\star} a & \longrightarrow & [a, 1] \end{array}$$

*Proof.* For any $(\infty, \omega)$-category $D$, the first square of proposition 4.3.3.15 implies that the following square is cartesian

$$\begin{array}{ccc} D \otimes \{0\} & \longrightarrow & D \otimes \{0\} \\ \downarrow & & \downarrow \\ 1 \stackrel{co}{\star} a & \longrightarrow & [a, 1] \end{array}$$

The statement then follows from proposition *op cit* and the preservation of colimit of the pullback along the morphism $1 \stackrel{co}{\star} a \to [a, 1]$ stated by corollary 5.2.3.12. $\square$

**Proposition 4.3.3.17.** *Let $C$ be a strict $(\infty, \omega)$-category, $a$ a globular sum, and $a \to C$ any morphism. The $(\infty, \omega)$-category $C \coprod_a a \otimes [1]$ is strict. In particular $a \otimes [1]$ is strict.*

*Proof.* According to propositions 4.3.3.2 and 4.3.3.12, the two lower objects and the upper right one of the cartesian square of lemma 4.3.3.16 are strict whenever $C$ is. As strict object are stable under pullback, this concludes the proof. $\square$

**4.3.3.18.** We combine the proposition 4.3.3.12 and 4.3.3.17 in the following theorem:

**Theorem 4.3.3.19.** *Let $C$ be an $(\infty, \omega)$-category, $a$ a globular sum, and $f : a \to C$ any morphism. The $(\infty, \omega)$-categories*

$$1 \stackrel{co}{\star} a \coprod_a C \quad C \coprod_a a \otimes [1] \quad C \coprod_a a \star 1$$

*are strict whenever $C$ is. In particular, $a \otimes [1]$, $a \star 1$ and $1 \stackrel{co}{\star} a$ are strict.*

**Corollary 4.3.3.20.** *Let $a$ be a globular sum, and $K$ an order set, viewed as an $(\infty, 1)$-category. The $(\infty, \omega)$-category $a \otimes K$ is strict.*

223

CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

Proof. If K is [n], an easy induction using proposition 4.3.3.17 shows the result. In the general case, remark that K is the special colimit of the diagram  \( \pi : \Delta_{/K}^{\hookrightarrow} \to \mathrm{Psh}^{\infty}(\Delta) \)  where  \( \Delta_{/K}^{\hookrightarrow} \)  is the category whose objects are monomorphisms  \( [n] \to K \)  and arrows are monomorphisms between domains making the induced triangle commutative, while  \( \pi \)  sends  \( [n] \to K \)  to [n]. We claim that the natural transformation

\[
a \otimes \pi \rightarrow \pi
\]

is cartesian. Proposition 4.2.1.24 then implies that \( a \otimes \pi \) has a special colimit. Moreover, \( a \otimes \pi \) fulfills the hypotheses of the third assertion of lemma 4.1.1.6. Its colimit is then strict, and this concludes the proof of the first assertion.

To demonstrate the cartesianess of the natural transformation  \( a \otimes \pi \to \pi \) , one has to show that for any monomorphism  \( i : [k] \to [l] \) , the induced square

![img-257.jpeg](img-257.jpeg)

is cartesian.

As \([k] \to [l]\) is fully faithful, so is \([k] \times_{[l]} a \otimes [l] \to a \otimes [l]\). If we manage to show that \(a \otimes [k] \to a \otimes [l]\) is fully faithful, it will imply by right cancelation that \(a \otimes [k] \to [l] \coprod_{[k]} a \otimes [l]\) is also fully faithful, and as this morphism is obviously surjective on objects it will conclude the proof.

We then have to show that for any integer n > 0, any square of shape

![img-258.jpeg](img-258.jpeg)

admits a unique lifting. Suppose given such square. Using the Steiner theory recalled in 1.2.1, it is equivalent show that the induced square of augmented directed complexes:

![img-259.jpeg](img-259.jpeg)

admits a unique lifting. We recall that the basis of  \( \lambda D_{n} \)  is given by the graded set:

\[
(B _ {\lambda \mathbf {D} _ {n}}) _ {k} := \left\{ \begin{array}{l l} \{e _ {k} ^ {-}, e _ {k} ^ {+} \} & \text {if k <   n} \\ \{e _ {n} \} & \text {if k = n} \\ \emptyset & \text {if k > n} \end{array} \right.
\]

224

4.3. GRAY OPERATIONS

and that the basis of $\lambda[n]$ also admits is given by the graded set

$$(B_{\lambda\mathbf{D}_n})_k := \begin{cases} \{v_0, v_1, ..., v_n\} & \text{if } k = 0 \\ \{v_{0,1}, v_{1,2}..., v_{n-1,n}\} & \text{if } k = 1 \\ \emptyset & \text{if } k > 1 \end{cases}$$

We will suppose that $n$ is odd as the proof for $n$ even is similar. As the right vertical morphism is an injection, we just have to show the existence of the lifting.

There exists a unique sequence $\{b_0, ..., b_{l-1}\}$ of element of $(\lambda b)_{n-1}$ and a unique sequence $\{c_0, ..., c_l\}$ of element of $(\lambda b)_n$ such that

$$f(e_n) = b_0 \otimes v_{0,1} + ... + b_{l-1} \otimes v_{l-1,l} + c_0 \otimes v_0 + ... + c_l \otimes v_l$$

The commutativity of the square then implies that the cell

$$\partial b_0 \otimes v_{0,1} + ... + \partial b_{l-1} \otimes v_{l-1,l} + (\partial c_0 - b_0) \otimes v_0 + (\partial c_1 + b_0 - b_1) \otimes v_1... + (\partial c_l + b_l) \otimes v_l$$

is in the image of $\lambda a \otimes \lambda i$. As a consequence, for any $j < k$, we have

$$\begin{cases} \partial b_0 = \partial b_1 = ... = \partial b_{i(0)-1} \\ \partial b_{i(j)} = \partial b_{i(j)+1}... = \partial b_{i(j+1)-1} \quad \text{for } j < k \\ \partial b_{i(k)} = \partial b_{i(k)+1} = ... = \partial b_{l-1} \end{cases}$$

and

$$\begin{cases} \partial c_0 - b_0 = 0 & \text{if 0 is not in the image of } i \\ \partial c_p + b_{p-1} - b_p = 0 & \text{if } p > 0 \text{ is not in the image of } i \\ \partial c_l + b_{l-1} = 0 & \text{if } l \text{ is not in the image of } i \end{cases}$$

The first set of equations forces the equalities:

$$\begin{cases} b_0 = b_1 = ... = b_{i(0)-1} \\ b_{i(j)} = b_{i(j)+1}... = b_{i(j+1)-1} \quad \text{for } j < k \\ b_{i(k)} = b_{i(k)+1} = ... = b_{l-1} \end{cases}$$

Combined with the second set of equations this implies that $c_p$ is null whenever $p$ is not in the image of $i$. We then have

$$f(e_n) = b_{i(0)} \otimes \lambda i(v_{0,1}) + ... + b_{i(k)} \otimes \lambda i(v_{k-1,k}) + c_{i(0)} \otimes \lambda i(v_0) + ... + c_i(k) \otimes \lambda i(v_k)$$

We then define the morphism $l$ as the unique morphism extending $g$ and that fulfills

$$l_n(e_n) := b_{i(0)} \otimes v_{0,1} + ... + b_{i(k)} \otimes v_{k-1,k} + c_{i(0)} \otimes v_0 + ... + c_i(k) \otimes v_k$$

This morphism is the wanted lift.

225

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**Corollary 4.3.3.21.** *There is a natural diagram*

$$\begin{array}{c} (C \otimes \{1\})^{\circ} \longrightarrow (C \otimes [1])^{\circ} \longleftarrow (C \otimes \{0\})^{\circ} \\ \downarrow \sim \qquad \qquad \qquad \downarrow \sim \qquad \qquad \downarrow \sim \\ C^{\circ} \otimes \{0\} \longrightarrow C^{\circ} \otimes [1] \longleftarrow C^{\circ} \otimes \{1\} \end{array}$$

*where all vertical arrows are equivalences. There is an invertible natural transformation*

$$C \star 1 \sim (1 \stackrel{co}{\star} C^{\circ})^{\circ}.$$

*Proof.* As these functors preserve colimits, we can define this equivalence on representables. As cylinders (resp. cone) (resp. o-cone) of representables are strict according to theorem 4.3.3.19, and as $(\_)^{\circ}$ preserves strict objects, it is enough to show these equivalences in $(0, \omega)$-cat, where it follows from [AM20, proposition A.22].

**Corollary 4.3.3.22.** *Let $A$ and $B$ two $(\infty, \omega)$-categories. There is an equivalence*

$$(A \ominus B)^{\circ} \sim A^{\circ} \ominus B^{\circ}$$

*natural in $A$ and $B$.*

*Proof.* It is sufficient to construct the equivalence when $A$ is a globular sum $a$ and $B$ is of shape $[b, n]$. Remark first that the corollary 4.3.3.20 implies that $(a \otimes [n])^{\circ}$ and $a^{\circ} \otimes [n]^{\circ}$ are strict objects. The proposition A.22 of [AM20] then implies that these two objects are isomorphic. The results then directly follows from the definition of the operation $\ominus$ and from the equivalence $(m_b(\_))^{\circ} \sim m_{b^{\circ}}((\_)^{\circ})$. $\square$

**Corollary 4.3.3.23.** *Let $F$ be an endofunctor of $(\infty, \omega)$-cat such that the induced functor $(\infty, \omega)$-cat $\to (\infty, \omega)$-cat$_{F(\emptyset)/}$ is colimit preserving, and $\psi$ is an invertible natural transformation between $G^{+} \to (\infty, \omega)$-cat $\xrightarrow{F} (\infty, \omega)$-cat and $G^{+} \to (\infty, \omega)$-cat $\xrightarrow{H} (\infty, \omega)$-cat where $G^{+}$ is obtained from $G$ by adding an initial element $\{\emptyset\}$, and $H$ is either the Gray cylinder, the Gray cone, the Gray o-cone or an iterated suspension.*

*Then, the natural transformation $\psi$ can be extended to an invertible natural transformation between $F$ and $H$.*

*Proof.* We denote by $\Theta^{+}$ the category obtained from $\Theta$ by adding an initial element $\emptyset$. Remark first that the theorem 1.2.3.18 implies that we have an invertible natural transformation

$$\pi_{0} \circ F_{|\Theta^{+}} \to \pi_{0} \circ H_{|\Theta^{+}}.$$

The propositions 4.3.3.12, 4.3.3.17 and 4.3.3.2 imply that the canonical morphism

$$H_{|\Theta^{+}} \to \mathrm{N} \circ \pi_{0} \circ H_{|\Theta^{+}}$$

226

4.3. GRAY OPERATIONS

is an equivalence. The two previous morphisms then induce a comparison:

$$F_{|\Theta^{+}} \to \mathrm{N} \circ \pi_{0} \circ F_{|\Theta^{+}} \to H_{|\Theta^{+}}$$

By extension by colimits, this produces a natural transformation $\phi : F \to H$ extending $\psi$. The full sub $\infty$-groupoid of objects $C$ such that $\phi_{C} : F(C) \to H(C)$ is an equivalence is closed by colimits, contains globes, and so is the maximal sub $\infty$-groupoid. $\square$

The previous corollary implies that the equations (4.3.1.7), (4.3.1.8) and (4.3.1.9) characterize respectively the Gray cylinder, the Gray cone, and the Gray $\circ$-cone.

**Corollary 4.3.3.24.** *The colimit preserving endofunctor $F : (\infty, \omega)$-cat $\to (\infty, \omega)$-cat, sending $[a, n]$ to the colimit of the span*

$$\coprod_{k \leq n} \{k\} \leftarrow \coprod_{k \leq n} a \otimes \{k\} \to a \otimes [n]$$

*is equivalent to the identity.*

*Proof.* The proposition 4.3.3.15 implies that the restriction of $F$ to globes is equivalent to the restriction of the identity to globes. As the identity is the 0-iterated suspension, we can apply corollary 4.3.3.23. $\square$

The last corollary implies that for any $(\infty, \omega)$-category $C$ and any globular sum $a$, the simplicial $\infty$-groupoid

$$\begin{array}{l} \Delta^{op} \to \infty\text{-grd} \\ [n] \mapsto \operatorname{Hom}([a, n], C) \end{array}$$

is a $(\infty, 1)$-category.

**Theorem 4.3.3.25.** *Let $C$ be an $(\infty, \omega)$-category. The two following canonical squares are cartesian:*

$$\begin{array}{ccc} 1 \longrightarrow 1 \stackrel{co}{\star} C & & 1 \longrightarrow C \star 1 \\ \downarrow & \downarrow & \downarrow \\ \{0\} \longrightarrow [C, 1] & & \{1\} \longrightarrow [C, 1] \end{array}$$

*The five squares appearing in the following canonical diagram are both cartesian and cocartesian:*

$$\begin{array}{ccc} & C \otimes \{0\} & \longrightarrow 1 \\ & \downarrow & \downarrow \\ C \otimes \{1\} & \longrightarrow C \otimes [1] & \longrightarrow C \star 1 \\ \downarrow & \downarrow & \downarrow \\ 1 & \longrightarrow 1 \stackrel{co}{\star} C & \longrightarrow [C, 1] \end{array}$$

227

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

*Proof.* The five squares of the second diagram are cocartesian by construction.

If $C$ is empty, all the considered squares are cartesian. We can then suppose that there exists a globular sum $a$, and a morphism $a \to C$. We claim that the two following squares are cartesian.

![img-260.jpeg](img-260.jpeg)

The cartesianess of the left square is a consequence of proposition 4.3.3.15 and of the fact that $\{0\} \to [a, 1]$ and $\{1\} \to [a, 1]$ are discrete Conduché functors and so pullback along them preserves colimits. The cartesianess of the right square is a consequence of the preservation of Gray operations by the full duality stated in corollary 4.3.3.21, and of the cartesian square provided by corollary 5.2.3.11. The two following squares are then cartesian:

![img-261.jpeg](img-261.jpeg)

As the duality $(\_)^\circ$ preserves limits, and combined with corollary 4.3.3.21, this implies that the two following squares are also cartesian:

![img-262.jpeg](img-262.jpeg)

By stability by right cancellation of cartesian square, it remains to show that the square

![img-263.jpeg](img-263.jpeg)

is cartesian. Consider the two following squares

![img-264.jpeg](img-264.jpeg)

We already demonstrate that the right one is cartesian and the lemma 4.3.3.16 states that the left one is also cartesian. The outer square is then cartesian.

228

4.3. GRAY OPERATIONS

Using that pulling back along $C \star 1 \rightarrow [C, 1]$ preserves colimits as shown in corollary 5.2.3.12, and the fact that $1 \stackrel{co}{\star} C$ (resp. $C \otimes [1]$) is the colimit of all the $1 \stackrel{co}{\star} a$ (resp. $a \otimes [1]$) for $a$ ranging over the morphisms $a \rightarrow C$, this concludes the proof. $\square$

**Theorem 4.3.3.26.** *If $C$ is strict, so are $C \star 1$, $1 \stackrel{co}{\star} C$ and $C \otimes [1]$.*

*Proof.* Forgetting the marking, the theorem 5.2.3.10 implies that $1 \stackrel{co}{\star} C$ is equivalent to $[C, 1]_{0/}$ which is strict as $[C, 1]$ is according to proposition 4.3.3.2. The second assertion comes from the fact that the full duality preserves $(0, \omega)$-categories and that $1 \stackrel{co}{\star} C^{\circ} \sim (C \star 1)^{\circ}$.

The theorem 4.3.3.25 implies that we have a cartesian square

$$\begin{array}{ccc} C \otimes [1] & \longrightarrow & 1 \stackrel{co}{\star} C \\ \downarrow & & \downarrow \\ C \star 1 & \longrightarrow & [C, 1] \end{array}$$

As strict objects are stable under pullbacks, this concludes the proof. $\square$

229

CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

230

# Chapter 5

## The $(\infty, 1)$-category of marked $(\infty, \omega)$-categories

### Contents

|  **5.1** | **Marked $(\infty, \omega)$-categories** | **233**  |
| --- | --- | --- |
|  5.1.1 | Definition of marked $(\infty, \omega)$-categories | 233  |
|  5.1.2 | Gray tensor product of marked $(\infty, \omega)$-categories | 241  |
|  5.1.3 | Gray operations on marked $(\infty, \omega)$-categories | 247  |
|  5.1.4 | Marked Gray deformation retract | 254  |
|  **5.2** | **Cartesian fibrations** | **258**  |
|  5.2.1 | Left and right cartesian fibrations | 258  |
|  5.2.2 | Cartesian fibration are exponentiable | 271  |
|  5.2.3 | Colimits of cartesian fibrations | 277  |
|  5.2.4 | Smooth and proper morphisms | 283  |
|  5.2.5 | The **W**-small $(\infty, \omega)$-category of **V**-small left cartesian fibrations | 290  |

This chapter is dedicated to the study of *marked* $(\infty, \omega)$-categories, which are pairs $(C, tC)$, where $C$ is an $(\infty, \omega)$-category and $tC := (tC_n)_{n>0}$ is a sequence of full sub $\infty$-groupoids of $C_n$ that include identities and are stable under composition and whiskering with (possibly unmarked) cells of lower dimensions. There are two canonical ways to mark an $(\infty, \omega)$-category $C$. In the first, denoted by $C^\flat$, we mark as little as possible. In the second, denoted by $C^\sharp$, we mark everything.

231

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

The first section of the chapter defines these objects and establishes analogs of many results from section 4.2 to this new framework. In particular, the *marked Gray cylinder* $\_ \otimes [1]^\sharp$ is defined. If $A$ is an $(\infty, \omega)$-category, the underlying $(\infty, \omega)$-category of $A^\sharp \otimes [1]^\sharp$ is $A \times [1]$, and the underlying $(\infty, \omega)$-category of $A^\flat \otimes [1]^\flat$ is $A \otimes [1]$. By varying the marking, and at the level of underlying $(\infty, \omega)$-categories, we "continuously" move from the cartesian product with the directed interval to the Gray tensor product with the directed interval.

The motivation for introducing markings comes from the notion of *left (and right) cartesian fibrations*. A left cartesian fibration is a morphism between marked $(\infty, \omega)$-categories such that only the marked cells of the codomain have cartesian lifting, and the marked cells of the domain correspond exactly to such cartesian lifting. For example, a left cartesian fibration $X \to A^\sharp$ is just a "usual" left cartesian fibration where we have marked the cartesian lifts of the domain, and every morphism $C^\flat \to D^\flat$ is a left cartesian fibration. This shows that marking plays a very different role here than in the case of marked simplicial sets, where it was there to represent (weak) invertibility. For example, if we had wanted to carry out this work in a complicial-like model category, we would have had to consider bimarked simplicial sets.

After defining and enumerating the stability properties enjoyed by this class of left (and right) cartesian fibration, we give several characterizations of this notion in theorem 5.2.1.26.

The more general subclass of left cartesian fibrations that still behaves well is the class of *classified left cartesian fibrations*. This corresponds to left cartesian fibrations $X \to A$ such that there exists a cartesian square:

![img-265.jpeg](img-265.jpeg)

where the right vertical morphism is a left cartesian fibration and $A^\sharp$ is obtained from $A$ by marking all cells. In the second section, we prove the following fundamental result:

**Theorem 5.2.2.12.** *Let $p : X \to A$ be a classified left cartesian fibration. Then the functor $p^* : (\infty, \omega)\text{-cat}_{\text{m}/A} \to (\infty, \omega)\text{-cat}_{\text{m}/X}$ preserves colimits.*

The third subsection is devoted to the proof of the following theorem

**Theorem 5.2.3.3.** *Let $A$ be an $(\infty, \omega)$-category and $F : I \to (\infty, \omega)\text{-cat}_{\text{m}/A^\sharp}$ be a diagram that is pointwise a left cartesian fibration. The induced morphism $\text{colim}_I F$ is a left cartesian fibration over $A^\sharp$.*

232

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

In the fourth subsection we study *smooth* and *proper* morphisms and we obtain the following expected result:

**Proposition 5.2.4.16.** *For a morphism $X \to A^{\sharp}$, and an object $a$ of $A$, we denote by $X_{/a}$ the marked $(\infty, \omega)$-category fitting in the following cartesian squares.*

![img-266.jpeg](img-266.jpeg)

*We denote by $\bot : (\infty, \omega)$-cat$_{\mathfrak{m}} \to (\infty, \omega)$-cat the functor sending a marked $(\infty, \omega)$-category to its localization by marked cells.*

(1) *Let $E$, $F$ be two elements of $(\infty, \omega)$-cat$_{\mathfrak{m}/A^{\sharp}}$ corresponding to morphisms $X \to A^{\sharp}$, $Y \to A^{\sharp}$, and $\phi : E \to F$ a morphism between them. We denote by $\mathbf{F}E$ and $\mathbf{F}F$ the left cartesian fiborant replacement of $E$ and $F$.*

*The induced morphism $\mathbf{F}\phi : \mathbf{F}E \to \mathbf{F}F$ is an equivalence if and only if for any object $a$ of $A$, the induced morphism*

$$
\bot X_{/a} \to \bot Y_{/a}
$$

*is an equivalence of $(\infty, \omega)$-categories.*

(2) *A morphism $X \to A^{\sharp}$ is initial if and only if for any object $a$ of $A$, $\bot X_{/a}$ is the terminal $(\infty, \omega)$-category.*

Finally, in the last subsection, for a marked $(\infty, \omega)$-category $I$, we define and study a (huge) $(\infty, \omega)$-category $\underline{\mathrm{LCart}}^c(I)$ that has classified left cartesian fibrations as objects and morphisms between classified left cartesian fibrations as arrows.

**Cardinality hypothesis.** We fix during this chapter two Grothendieck universes $\mathbf{V} \in \mathbf{W}$, such that $\omega \in \mathbf{U}$. When nothing is specified, this corresponds to the implicit choice of the cardinality $\mathbf{V}$. We then denote by Set the $\mathbf{W}$-small 1-category of $\mathbf{V}$-small sets, $\infty$-grd the $\mathbf{W}$-small $(\infty, 1)$-category of $\mathbf{V}$-small $\infty$-groupoids and $(\infty, 1)$-cat the $\mathbf{W}$-small $(\infty, 1)$-category of $\mathbf{V}$-small $(\infty, 1)$-categories.

## 5.1 Marked $(\infty, \omega)$-categories

### 5.1.1 Definition of marked $(\infty, \omega)$-categories

**5.1.1.1.** *A marked $(0, \omega)$-category is a pair $(C, tC)$ where $C$ is an $(0, \omega)$-category and $tC := (tC_n)_{n>0}$ is a sequence of subsets of $C_n$, containing identities, stable by composition*

233

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

and by whiskering with (possibly unmarked) cells of lower dimension. A $n$-cell $a : \mathbf{D}_n \to (C, tC)$ is marked if it belongs to $tC_n$.

A marked morphism $f : (C, tC) \to (D, tT)$ is the data of a morphism on the underlying $(0, \omega)$-categories such that $f(tC_n) \subset tD_n$. The category of marked $(0, \omega)$-categories is denoted by $(0, \omega)$-cat$_\text{m}$.

5.1.1.2. There are two canonical ways to mark an $(0, \omega)$-category. For $C \in (0, \omega)$-cat, we define $C^\sharp := (C, (C_n)_{n>0})$ and $C^\flat := (C, (\mathbb{I}(C_{n-1})_{n>0}))$. The first one corresponds to the case where all cells are marked, and the second one where only the identities are marked. These two functors fit in the following adjoint triple:

$$(\_)^\flat : (0, \omega)\text{-cat} \xrightarrow{\perp} (0, \omega)\text{-cat}_\text{m} : (\_)^\sharp \qquad (\_)^\sharp : (0, \omega)\text{-cat}_\text{m} \xrightarrow{\perp} (0, \omega)\text{-cat} : (\_)^\sharp$$

where $(\_)^\sharp$ is the obvious forgetfull functor. To simplify notations, for a marked $(0, \omega)$-category $C$, the marked $(\infty, \omega)$-categories $(C^\sharp)^\flat$ and $(C^\sharp)^\sharp$ will be simply denoted by $C^\flat$ and $C^\sharp$.

Example 5.1.1.3. For $n$ an integer, we denote by $(\mathbf{D}_n)_t$ the marked $(0, \omega)$-category whose underlying $(0, \omega)$-category is $\mathbf{D}_n$ and whose only non-trivial marked cell is the top dimensional one.

Definition 5.1.1.4. We define the category $t\Theta$ as the full subcategory of $(0, \omega)$-cat$_\text{m}$ whose objects are of shape $a^\flat$ for $a$ a globular sum, or $(\mathbf{D}_n)_t$ for an integer $n \in \mathbb{N}$. Remark that this subcategory is dense in $(0, \omega)$-cat$_\text{m}$.

5.1.1.5. We define the $(\infty, 1)$-category of stratified $\infty$-presheaves on $\Theta$, noted by tPsh$^\infty(\Theta)$, as the full sub $(\infty, 1)$-category of Psh$^\infty(t\Theta)$ whose objects correspond to $\infty$-presheaves $X$ such that the induced morphism $X((\mathbf{D}_n)_t) \to X(\mathbf{D}_n)$ is a monomorphism.

Proposition 5.1.1.6. The $(\infty, 1)$-category tPsh$^\infty(\Theta)$ is locally cartesian closed.

Proof. The $(\infty, 1)$-category tPsh$^\infty(\Theta)$ is the localization of the $(\infty, 1)$-category Psh$^\infty(t\Theta)$ along the set of map $\widehat{I}$ with

$$I := \{(\mathbf{D}_n)_t \coprod_{\mathbf{D}_n} (\mathbf{D}_n)_t \to (\mathbf{D}_n)_t\}_n.$$

As Psh$^\infty(t\Theta)$ is locally cartesian closed, we have to show that for any integer $n > 0$ and any cartesian square in Psh$^\infty(t\Theta)$:

$$\begin{array}{c} X' \xrightarrow{\quad} X \\ \downarrow \quad \downarrow \\ (\mathbf{D}_n)_t \coprod_{\mathbf{D}_n} (\mathbf{D}_n)_t \longrightarrow (\mathbf{D}_n)_t \end{array}$$

234

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

the top horizontal morphism is in \(\widehat{I}\). Using once again the locally cartesian closeness of \(\mathrm{Psh}^{\infty}(t\Theta)\), it is sufficient to show that for any integer \(n > 0\) and for any morphism \(j:b\to (\mathbf{D}_n)_t\) between elements of \(t\Theta\), the morphism \(i\) appearing in the following cartesian square of \(\mathrm{Psh}^{\infty}(t\Theta)\) is an equivalence or is in \(I\):

![img-267.jpeg](img-267.jpeg)

Two cases have to be considered. If \( j \) is the identity this is trivially true. If \( j \) is any other morphism, it factors through \( \mathbf{D}_n \to (\mathbf{D}_n)_t \), and the following square is cartesian

![img-268.jpeg](img-268.jpeg)

This implies that \( B \) is equivalent to \( b \coprod_{b} b \sim b \), and \( i \) is then the identity.

5.1.1.7. For a stratified  \( \infty \) -presheaf X on  \( \Theta \) , we denote by  \( tX_{n} \)  the  \( \infty \) -groupoid  \( X((\mathbf{D}_{n})_{t}) \) . A stratified  \( \infty \) -presheaves on  \( \Theta \)  is then the data of a pair  \( (X, tX) \)  such that  \( X \in \mathrm{Psh}^{\infty}(\Theta) \)  and  \( tX := (tX_{n})_{n>0} \)  is a sequence of  \( \infty \) -groupoid such that for any n > 0,  \( tX_{n} \)  is a full sub  \( \infty \) -groupoid of  \( X_{n} \)  including all units.

For  \( X \in \mathrm{Psh}^{\infty}(\Theta) \) , we define  \( X^{\sharp} := (X, (X_{n})_{n>0}) \)  and  \( X^{\flat} := (X, (\mathbb{I}(X_{n-1})_{n>0}) \)  and we have an adjoint triple

\[
(\_) ^ {\flat}: \mathrm{Psh} ^ {\infty} (\Theta) \xrightarrow [ \longleftarrow ]{\perp} \mathrm{tPsh} ^ {\infty} (\Theta): (\_) ^ {\natural} \qquad (\_) ^ {\natural}: \mathrm{tPsh} ^ {\infty} (\Theta) \xrightarrow [ \longleftarrow ]{\perp} \mathrm{Psh} (\Theta): (\_) ^ {\sharp}
\]

where \((\_)^{\natural}\) is the obvious forgetful functor.

5.1.1.8. We define the category \( t\Delta[t\Theta] \) as the pullback

![img-269.jpeg](img-269.jpeg)

The objects of \( t\Delta[t\Theta] \) then are of shape \( [1]^{\sharp} \) or \( [a,n] \) with \( a\in t\Theta \) and \( n\in \Delta \). The \( (\infty ,1) \)-category of stratified presheaves on \( \Delta [\Theta ] \), denoted by \( \mathrm{tPsh}^{\infty}(\Delta [\Theta ]) \), is the full sub \( (\infty ,1) \)-category of \( \mathrm{Psh}^{\infty}(t\Delta [t\Theta ]) \) whose objects correspond to \( \infty \)-presheaves \( X \) such that the induced morphism \( X((\mathbf{D}_n)_t)\to X(\mathbf{D}_n) \) is a monomorphism.

Proposition 5.1.1.9. The \((\infty,1)\)-category \(\mathrm{tPsh}^{\infty}(\Delta[\Theta])\) is locally cartesian closed.

Proof. The proof is almost identical to the one of proposition 5.1.1.6

235

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

5.1.1.10. For a stratified  \( \infty \) -presheaf X on  \( \Delta[\Theta] \) , we denote by  \( tX_{1} \)  the  \( \infty \) -groupoid  \( X([1]^{\sharp}) \) , and for any n > 1, we denote by  \( tX_{n} \)  the  \( \infty \) -groupoid  \( X((\mathbf{D}_{n})_{t}) \) .

A stratified  \( \infty \) -presheaf on  \( \Delta[\Theta] \)  is then the data of a pair  \( (X,tX) \)  such that  \( X\in\mathrm{Psh}^{\infty}(\Delta[\Theta]) \)  and  \( tX:=(tX_{n})_{n>0} \)  is a sequence of  \( \infty \) -groupoid such that for any n>0,  \( tX_{n} \)  is a full sub  \( \infty \) -groupoid of  \( X_{n} \)  including all units.

For  \( X \in \mathrm{Psh}^{\infty}(\Delta[\Theta]) \) , we define once again  \( X^{\sharp} := (X, (X_{n})_{n>0}) \)  and  \( X^{\flat} := (X, (\mathbb{I}(X_{n-1}))_{n>0}) \)  and we still have an adjoint triple

\[
(\_) ^ {\sharp} \mathrm{Psh} ^ {\infty} (\Delta [ \Theta ]) \underset {\leftarrow} {\longrightarrow} \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]): (\_) ^ {\sharp} \qquad (\_) ^ {\sharp}: \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]) \underset {\leftarrow} {\longrightarrow} \mathrm{Psh} ^ {\infty} (\Delta [ \Theta ]): (\_) ^ {\sharp}
\]

where  \( (\_)^{\sharp} \)  is the obvious forgetfull functor.

5.1.1.11. We once again have an adjunction:

\[
i _ {!}: \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]) \xrightarrow [ \longleftarrow ]{} \mathrm{tPsh} ^ {\infty} (\Theta): i ^ {*}
\]

induced by the canonical inclusion  \( t\Delta[t\Theta]\to t\Theta \) . For an integer n, we define the functor  \( (\_)^{\sharp_{n}}:\mathrm{Psh}^{\infty}(\Theta)\to\mathrm{tPsh}^{\infty}(\Theta) \)  and  \( (\_)^{\sharp_{n}}:\mathrm{Psh}^{\infty}(\Delta[\Theta])\to\mathrm{tPsh}^{\infty}(\Delta[\Theta]) \)  sending a  \( \infty \) -presheaf X onto  \( (X,(X_{k}^{n})_{k>0}) \)  where  \( X_{k}^{n}:=\mathbb{I}(X_{k-1}) \)  if k<n, and  \( X_{k}^{n}:=X_{k} \)  if not. We eventually set

\[
\mathrm{tW} := \coprod_ {n} (\mathrm{W} _ {\mathrm{Seg}}) ^ {\sharp_ {n}} \coprod (\mathrm{W} _ {\mathrm{Sat}}) ^ {\flat} \qquad \mathrm{tM} := \coprod_ {n} (\mathrm{M} _ {\mathrm{Seg}}) ^ {\sharp_ {n}} \coprod (\mathrm{M} _ {\mathrm{Sat}}) ^ {\flat}
\]

As  \( i_{!}(tM) \)  is contained in tW, the previous adjunction induces a derived one:

\[
\mathbf {L} i _ {!}: \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]) _ {\mathrm{tM}} \xrightarrow [ \leftarrow ]{\longrightarrow} \mathrm{tPsh} ^ {\infty} (\Theta) _ {\mathrm{tW}}: i ^ {*} \mathbf {R} \tag {5.1.1.12}
\]

Proposition 5.1.1.13. The derived adjunction (5.1.1.12) is an adjoint equivalence.

Proof. It is enough to show that for any element \( a: t\Delta[t\Theta] \) and any \( b: t\Theta \), \( a \to i^{*}i_{!}a \) and \( i_{!}i^{*}b \to b \) are respectively in \( \widehat{\mathrm{tM}} \) and \( \widehat{\mathrm{tW}} \). If \( a \) is of shape \( [b, n]^{\flat} \), this is a direct consequence of proposition 4.2.1.5, and if \( a \) is \( (\mathbf{D}_n)_t \) the unit is the identity. We proceed similarly for \( i_{!}i^{*}b \to b \).

The inclusion  \( t\Theta \rightarrow (0, \omega) \) -cat \( _{m} \)  induces an adjunction

\[
\mathrm{tPsh} (\Theta) \xrightarrow [ \longleftarrow ]{\longrightarrow} (0, \omega) \text {-cat} _ {\mathrm{m}}
\]

and we can easily check that this induces an equivalence between  \( (0,\omega) \) -cat \( _{m} \)  and the sub-category of tPsh( \( \Theta \) ) of tW-local objects. Together with proposition 5.1.1.13, this induces equivalences

\[
\mathrm{tPsh} (\Theta) _ {\mathrm{tM}} \cong \mathrm{tPsh} (\Delta [ \Theta ]) _ {\mathrm{tW}} \cong (0, \omega) \mathrm{-cat} _ {\mathrm{m}}
\]

236

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

5.1.1.14. A marked  \( (\infty,\omega) \) -category is a tW-local stratified  \( \infty \) -presheaves on  \( \Theta \) . We denote by  \( (\infty,\omega) \) -cat \( _{m} \)  the  \( (\infty,1) \) -category of marked  \( (\infty,\omega) \) -categories. Unfolding the definition, a marked  \( (\infty,\omega) \) -category is a pair  \( (C,tC) \)  where C is an  \( (\infty,\omega) \) -category and  \( tC := (tC_{n})_{n>0} \)  is a sequence of full sub  \( \infty \) -groupoids of  \( C_{n} \) , containing identities, stable by composition and by whiskering with cells of lower dimension. A n-cell  \( a : D_{n} \to (C,tC) \)  is marked if it belongs to the image of  \( tC_{n} \) .

There are two obvious ways to mark a  \( (\infty,\omega) \) -category. For  \( C\in(\infty,\omega) \) -cat, we define  \( C^{\sharp}:=(C,(C_{n})_{n>0}) \)  and  \( C^{\flat}:=(C,(\mathbb{I}(C_{n-1})_{n>0})) \) . The first one corresponds to the case where all cells are marked, and the second one where only the identities are marked. These two functors fit in the following adjoint triple:

\[
(\_) ^ {\flat}: (\infty , \omega) \text {-cat} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat} _ {\mathrm{m}}: (\_) ^ {\natural} \qquad (\_) ^ {\natural}: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat}: (\_) ^ {\sharp}
\]

where  \( (\_)^{\sharp} \)  is the obvious forgetful functor. To simplify notations, for a marked  \( (\infty,\omega) \) -category C, the marked  \( (\infty,\omega) \) -categories  \( (C^{\sharp})^{\flat} \)  and  \( (C^{\sharp})^{\sharp} \)  will be simply denoted by  \( C^{\flat} \)  and  \( C^{\sharp} \) .

5.1.1.15. Following paragraph 4.2.1.54, for any subset \(S\) of \(\mathbb{N}^*\), we define the duality

\[
(\_) ^ {S}: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

whose value on  \( (C,tC) \)  is  \( (C^{S},tC) \) . In particular, we have the odd duality  \( (\_)^{op} \) , corresponding to the set of odd integer, the even duality  \( (\_)^{co} \) , corresponding to the subset of non negative even integer, the full duality  \( (\_)^{\circ} \) , corresponding to  \( N^{*} \)  and the transposition  \( (\_)^{t} \) , corresponding to the singleton  \( \{1\} \) . Eventually, we have equivalences

\[
((\_) ^ {c o}) ^ {o p} \sim (\_) ^ {\circ} \sim ((\_) ^ {o p}) ^ {c o}.
\]

5.1.1.16. Given a functor \( F: I \to (\infty, \omega) \)-cat\(_m\), the colimit of \( F \) is given by the marked \( (\infty, \omega) \)-category \( (C, tC) \) with

\[
C := \underset {I} {\operatorname{colim}} F ^ {\natural}
\]

and for any \(n\), \((tC)_n\) is the image of the morphism

\[
\underset {I} {\operatorname{colim}} t F _ {n} \to (\underset {I} {\operatorname{colim}} F) _ {n} ^ {\natural}.
\]

The case of the limit is easier as we have

\[
\lim _ {I} F := (\lim _ {I} F ^ {\natural}, (\lim _ {I} (t F _ {n}) _ {n > 0}).
\]

In particular, if  \( (C,tC) \)  and  \( (D,tD) \)  are two marked  \( (\infty,\omega) \) -categories, we have

\[
(C, t C) \times (D, t D) := (C \times D, (t C _ {n} \times t D _ {n}) _ {n > 0}).
\]

237

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proposition 5.1.1.17. The cartesian product in \((\infty, \omega)\)-cat$_{\mathrm{m}}$ preserves colimits in both variables.

Proof. Let  \( F: I \to (\infty, \omega) \) -cat \( _{m} \)  be a diagram and C a marked  \( (\infty, \omega) \) -category. The underlying  \( (\infty, \omega) \) -categories of  \( \operatorname{colim}_{I}(F \times C) \)  and  \( (\operatorname{colim}_{I} F) \times C \)  are the same as the cartesian product preserves colimits in  \( (\infty, \omega) \) -cat. The equivalence of the two markings is a direct consequence of the fact that the cartesian product in  \( \infty \) -grd preserves both colimits and the formation of image. □

This demonstrates the existence of an internal hom functor that we denote once again by \(\underline{\mathrm{Hom}} (\_, \_)\).

5.1.1.18. We denote again  \( \pi_{0}:\mathrm{tPsh}^{\infty}(\Theta)\to\mathrm{tPsh}(\Theta) \)  colimit preserving sending a stratified  \( \infty \) -presheaf X to the stratified presheaf  \( a\mapsto\pi_{0}(X_{a}) \) . As this functor preserves tW, it induces an adjoint pair:

\[
\pi_ {0}: (\infty , \omega) \text {-cat} \xrightarrow [ \leftarrow ]{\perp} (0, \omega) \text {-cat}: N
\]

where the right adjoint N is fully faithful. A marked  \( (\infty,\omega) \) -category lying in the image of the nerve is called strict. Remark eventually that the following square is cartesian

\[
\begin{array}{c} (0, \omega) \text {-cat} _ {\mathrm{m}} \xrightarrow {\mathrm{N}} (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ (\_) ^ {\natural} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (0, \omega) \text {-cat} \xrightarrow {\mathrm{N}} (\infty , \omega) \text {-cat} \end{array}
\]

A marked \((\infty, \omega)\)-category is then strict if and only if it's underlying \((\infty, \omega)\)-category is.

5.1.1.19. The marked suspension is the colimit preserving functor

\[
[ \_, 1 ]: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m} _ {\bullet , \bullet}}
\]

sending \(a^{\flat}\) onto \([a,1]^{\flat}\) and \((\mathbf{D}_n)_t\) to \(([\mathbf{D}_n,1])_t\). It then admits a right adjoint:

\[
\begin{array}{l} (\infty , \omega) \text {-cat} _ {\mathrm{m} _ {\bullet , \bullet}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ (C, a, b) \qquad \mapsto \hom_ {C} (a, b) \\ \end{array}
\]

With the same computation than the one of paragraph 4.2.1.17, we show that for a marked \((\infty, \omega)\)-category \(C\), any 1-cell \(f: x \to x'\) induces for any object \(y\), a morphism

\[
f _ {!}: \hom_ {C} (x ^ {\prime}, y) \to \hom_ {C} (x, y).
\]

Conversely, a 1-cell \( g: y \to y' \) induces for any object \( x \) a morphism

\[
g _ {!}: \hom_ {C} (x, y) \to \hom_ {C} (x, y ^ {\prime})
\]

238

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

5.1.1.20. In section 4.2.1, we define the notion of fully faithful morphism of \((\infty, \omega)\)-categories. There is an equivalent notion for marked \((\infty, \omega)\)-categories:

Definition 5.1.1.21. A morphism \( f: C \to D \) is fully faithful if for any pair of objects \( x, y \), the morphism of marked \( (\infty, \omega) \)-categories \( \hom_C(x, y) \to \hom_D(fx, fy) \) is an equivalence, and if a 1-cell \( v \) is marked whenever \( f(v) \) is.

We now give some adaptation of the result on fully faithful functors to the case of marked  \( (\infty,\omega) \) -categories without proofs, as they are obvious modifications to this new framework.

Proposition 5.1.1.22. A morphism is fully faithful if and only if it has the unique right lifting property against \(\emptyset \to \mathbf{D}_n\) and \(\mathbf{D}_n \to (\mathbf{D}_n)_t\) for \(n > 0\).

Proposition 5.1.1.23. Fully faithful morphisms are stable under limits.

Proposition 5.1.1.24. A morphism \( f: C \to D \) is an equivalence if and only if it is fully faithful and surjective on objects.

5.1.1.25. A morphism \( f: C \to D \) between marked \( (\infty, \omega) \)-categories is a discrete Conduché functor if for any triplet of integers \( k < n \leq m \), \( f \) has the unique right lifting property against

\[
\mathbb {I} _ {m + 1}: \mathbf {D} _ {m + 1} ^ {\flat} \to \mathbf {D} _ {m} ^ {\flat} \quad \text {and} \quad \nabla_ {k, m} ^ {\sharp_ {n}}: \mathbf {D} _ {m} ^ {\sharp_ {n}} \to \mathbf {D} _ {m} ^ {\sharp_ {n}} \coprod_ {\mathbf {D} _ {k} ^ {\flat}} \mathbf {D} _ {m} ^ {\sharp_ {n}}.
\]

Example 5.1.1.26. If \( f \) is a discrete Conduché functor between marked \( (\infty, \omega) \)-categories, \( f^{\sharp} \) is a discrete Conduché functor. Conversely, if \( g \) is a discrete Conduché functor between \( (\infty, \omega) \)-categories, so are \( g^{\sharp} \), \( g^{\flat} \) and \( g^{\sharp n} \) for any integer \( n \).

5.1.1.27. A marked globular sum is a marked  \( (\infty,\omega) \) -category whose underlying  \( (\infty,\omega) \) -category is a globular sum and such that for any pair of integers  \( k \leq n \) , and any pair of k-composable n-cells  \( (x,y) \) ,  \( x \circ_{k} y \)  is marked if and only if x and y are marked.

A morphism \( i: a \to b \) between marked globular sum is globular if the morphism \( i^{\sharp} \) is globular.

The proposition 1.1.2.11 implies that a morphism \(a \to b\) between marked globular sums is a discrete Conduché functor if and only if it is globular.

Lemma 5.1.1.28. Let \( p: C \to D^b \) be a discrete Conduché functor between marked \( (\infty, \omega) \)-categories. The canonical morphism \( (C^\sharp)^b \to C \) is an equivalence.

239

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proof. Suppose given a marked \(n\)-cell \(v: \mathbf{D}_n \to C^\natural\). As the marking on \(C\) is trivial, this induces a commutative square

![img-270.jpeg](img-270.jpeg)

that admits a lift \( l \) as \( p^{\sharp} \) is a discrete Conduché functor, which concludes the proof.

Proposition 5.1.1.29. Let \( p: C \to D \) be a discrete Conduché functor between marked \( (\infty, \omega) \)-categories. The pullback functor \( p^* \) preserves colimits.

Proof. As  \( \mathrm{tPsh}^{\infty}(\Theta) \)  is locally cartesian closed, one has to show that for any pair of cartesian squares

![img-271.jpeg](img-271.jpeg)

if \(i\) is tW, then \(j\) is in \(\widehat{\mathrm{tW}}\). Suppose first that \(i\) is in \(\mathrm{W}_{\mathrm{Sat}}^{\flat}\). According of the lemma 5.1.1.28 the \((\infty, \omega)\)-categories \(C'\) and \(C''\) are of shape \((E)^{\flat}\) and \((E')^{\flat}\) for \(E\) and \(E'\) two \((\infty, \omega)\)-categories. The proposition 4.2.2.8 then implies that \(i\) is in \(\widehat{\mathrm{W}}^{\flat} \subset \widehat{\mathrm{tW}}\). If \(i\) is in \((\mathrm{W}_{\mathrm{Seg}})^{\sharp_n}\) the proof is an easy adaptation of the one of lemma 4.2.2.6.

5.1.1.30. We now give some adaptation of the result on special colimits stated in paragraph 4.2.1.21 to the case of marked  \( (\infty,\omega) \) -categories without proofs, as they are easy modifications.

We denote by \(\iota\) the inclusion of \((\infty, \omega)\)-cat\(_{\mathrm{m}}\) into tPsh\(^{\infty}(\Theta)\). A functor \(F: I \to (\infty, \omega)\)-cat\(_{\mathrm{m}}\) has a special colimit if the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota F (i) \rightarrow \iota (\underset {i: I} {\operatorname{colim}} F (i)) \tag {5.1.1.31}
\]

is an equivalence of stratified presheaves.

Similarly, we say that a functor \(\psi : I \to \mathrm{Arr}((\infty, \omega)\text{-cat}_{\mathrm{m}})\) has a special colimit if the canonical morphism

\[
\underset {i: I} {\operatorname{colim}} \iota \psi (i) \to \iota (\underset {i: I} {\operatorname{colim}} \psi (i))
\]

is an equivalence in the arrow \((\infty,1)\)-category of \(\mathrm{tPsh}^{\infty}(\Theta)\).

Example 5.1.1.32. Let C be a marked  \( (\infty,\omega) \) -category. The canonical diagram  \( t\Theta_{/C} \to (\infty,\omega) \) -cat has a special colimit, given by C.

240

5.1. MARKED $(\infty, \omega)$-CATEGORIES

**Proposition 5.1.1.33.** *Let $F, G : I \rightarrow (\infty, \omega)$-cat$_m$ be two functors, and $\psi : F \rightarrow G$ a natural transformation. If $\psi$ is cartesian, and $G$ has a special colimit, then $\psi$ and $F$ have special colimits.*

**Proposition 5.1.1.34.** *For any integer $n$, and element $a \in t\Theta$ and $b \in \Theta$, the equalizer diagram*

$$\coprod_{k+l=n-1}[a, k] \vee [a \times b^\sharp, 1] \vee [a, l] \xrightarrow{\quad} \coprod_{k+l=n}[a, k] \vee [b, 1]^\sharp \vee [a, l]$$

*where the top diagram is induced by $[a \times b^\sharp, 1] \rightarrow [a, 1] \vee [b, 1]^\sharp$ and to bottom one by $[a \times b^\sharp, 1] \rightarrow [b, 1]^\sharp \vee [a, 1]$, has a special colimit, which is $[a, n] \times [b, 1]^\sharp$.*

**Proposition 5.1.1.35.** *Any sequence of marked $(\infty, \omega)$-categories has a special colimit.*

**Proposition 5.1.1.36.** *Suppose given a cartesian square*

$$\begin{array}{ccc} B & \longrightarrow & C \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [1]^\sharp \end{array}$$

*The diagram*

$$[1]^\sharp \vee [B, 1] \xleftarrow{\quad} [B, 1] \longrightarrow [C, 1]$$

*has a special colimit.*

**Proposition 5.1.1.37.** *Suppose given two cartesian squares*

$$\begin{array}{ccc} B & \longrightarrow & C \xleftarrow{\quad} D \\ \downarrow & & \downarrow \\ \{0\} & \longrightarrow & [1]^\sharp \xleftarrow{\quad} \{1\} \end{array}$$

*The diagram*

$$[1]^\sharp \vee [B, 1] \xleftarrow{\quad} [B, 1] \longrightarrow [C, 1] \xleftarrow{\quad} [D, 1] \xrightarrow{\quad} [D, 1] \vee [1]^\sharp$$

*has a special colimit.*

### 5.1.2 Gray tensor product of marked $(\infty, \omega)$-categories

We define the *marked Gray tensor product*

$$\_ \otimes (\_)^\sharp : (\infty, \omega)\text{-cat}_m \times (\infty, 1)\text{-cat} \rightarrow (\infty, \omega)\text{-cat}_m$$

241

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

sending a marked \((\infty, \omega)\)-category \(C\) and a \((\infty, 1)\)-category \(K\) to the marked \((\infty, \omega)\)-category \(C \otimes K^{\sharp}\), such that \((C \otimes K^{\sharp})^{\sharp}\) fits in the cocartesian square

![img-272.jpeg](img-272.jpeg)

and such that  \( t(C \otimes K^{\sharp})_{n} \)  consists of n-cells lying in the image of the morphism

\[
\tau_ {n - 1} C \otimes K \coprod (t C) _ {n} \otimes K _ {0} \rightarrow (C \otimes K ^ {\sharp}) ^ {\natural}.
\]

Proposition 5.1.2.1. The functor \(\_ \otimes (\_)^{\sharp} : (\infty, \omega)\text{-cat}_{\mathfrak{m}} \times (\infty, 1)\text{-cat} \to (\infty, \omega)\text{-cat}_{\mathfrak{m}}\) preserves colimits.

Proof. By construction, we have two cocartesian squares:

![img-273.jpeg](img-273.jpeg)

![img-274.jpeg](img-274.jpeg)

By the preservation of colimit by the Gray tensor product for \((\infty, \omega)\)-categories and by the functor \((_{-})^{\natural}\), we have an equivalence

\[
\operatorname{colim} (F ^ {\natural} \otimes K) \sim (\operatorname{colim} F ^ {\natural}) \otimes K
\]

However, the canonical morphism  \( \operatorname{colim} tF \to t(\operatorname{colim} F) \)  is an epimorphism, and according to proposition 4.2.1.62, the following canonical square is cocartesian

![img-275.jpeg](img-275.jpeg)

Combined with the first two cocartesian squares, this implies that that  \( \operatorname{colim}(F \otimes K^{\sharp})^{\sharp} \)  and  \( ((\operatorname{colim} F) \otimes K^{\sharp})^{\sharp} \)  are equivalent.

242

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

According to proposition 4.2.1.60 and by construction, the morphisms

$$\operatorname{colim}(\tau_n^i F^\natural \otimes K) \to \tau_n^i (\operatorname{colim} F^\natural \otimes K) \quad \text{and} \quad \operatorname{colim}(tF \otimes K_0) \to t(\operatorname{colim} F \otimes K_0)$$

are epimorphisms. The marked $(\infty, \omega)$-categories $\operatorname{colim}(F \otimes K^\sharp)$ and $(\operatorname{colim} F) \otimes K^\sharp$ then have the same marked cells. □

**Proposition 5.1.2.2.** *Let $C$ be a $(\infty, \omega)$-category, $D$ a marked $(\infty, \omega)$-category and $K, L$ two $(\infty, 1)$-categories.*

(1) *The underlying $(\infty, \omega)$-category of $C^\flat \otimes K^\sharp$ is $C \otimes K$.*
(2) *The canonical morphism $C^\sharp \otimes K^\sharp \to C^\sharp \times K^\sharp$ is an equivalence.*

*Proof.* The first assertion is obvious.

Let $a$ be a globular sum and $[k]$ an object of $\Delta$. We claim that the following two squares are cocartesian:

$$\coprod_n \coprod_{\mathbf{D}_n \to a} \mathbf{D}_n \otimes [k] \longrightarrow \coprod_n \tau_n a \otimes [k] \longrightarrow a \otimes [k]$$
$$\updownarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$
$$\coprod_n \coprod_{\mathbf{D}_n \to a} \tau_n^i (\mathbf{D}_n \otimes [k]) \longrightarrow \coprod_n \tau_n^i (\tau_n a \otimes [k]) \longrightarrow (a^\sharp \times [k]^\sharp)^\sharp$$

The cocartesianess of the left square is a consequence of propositions 4.2.1.62 and 4.2.1.61. The outer square is cocartesian by definition, and by left cancellation, this implies the cocartesianess of the right square. The lemma 2.2.2.8 then implies that the underlying category of $a^\sharp \otimes [k]^\sharp$ is $a \times [k]$. As every cell of $a^\sharp \otimes [k]^\sharp$ is marked, this concludes the proof of the second assertion. □

**Proposition 5.1.2.3.** *Let $D$ be an $(\infty, \omega)$-category, $C$ a marked $(\infty, \omega)$-category and $K$ an $(\infty, 1)$-category. The canonical morphism $(D^\sharp \times C) \otimes K^\sharp \to D^\sharp \times (C \otimes K^\sharp)$ is an equivalence.*

*Proof.* As $\times$ and $\otimes$ preserve colimits, we can reduce to the case where $D$ is an element of $\Theta$, $C$ of $t\Theta$ and $K$ of $\Delta$, and we proceed by induction on the dimension of $D$. Remark first that if $D$ is $[0]$, the result is obvious, and if it is $(\mathbf{D}_1)_t$, the result follows from the second assertion of proposition 5.1.2.2. Suppose then the result is true at the stage $n$. Using once again the fact that $\times$ and $\otimes$ preserve colimits, we can reduce to the case where $D^\sharp$ is $[a, 1]^\sharp$, $C$ is $[b, 1]$ with $b$ an element of $\Theta_t$ of dimension $n$, and $K^\sharp$ is $[1]^\sharp$.

The formula given in proposition 5.1.1.34 implies that $([a, 1]^\sharp \times [b, 1]) \otimes [1]^\sharp$ is the colimit of the sequence:

$$([a, 1]^\sharp \vee [b, 1]) \otimes [1]^\sharp \longleftarrow [a^\sharp \times b, 1] \otimes [1]^\sharp \longrightarrow ([b, 1] \vee [a, 1]^\sharp) \otimes [1]^\sharp \qquad (5.1.2.4)$$

243

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

The marked $(\infty, \omega)$-category $([a, 1]^\sharp \vee [b, 1]) \otimes [1]^\sharp$ is then the colimit of the diagram

$$[a, 1]^\sharp \times [1]^\sharp \longleftarrow [1]^\sharp \longrightarrow [b, 1] \otimes [1]^\sharp$$

and using the formulas (5.1.3.9) and 5.1.1.34, $([a, 1]^\sharp \vee [b, 1]) \otimes [1]^\sharp$ is the colimit of the diagram

$$\begin{array}{c} [1]^\sharp \vee [a, 1]^\sharp \vee [b, 1] \longleftarrow [a, 1]^\sharp \vee [b, 1] \longrightarrow [a, 1]^\sharp \vee [1]^\sharp \vee [b, 1] \\ \uparrow \\ [a, 1]^\sharp \vee [b \otimes \{0\}, 1] \\ \downarrow \\ [a, 1]^\sharp \vee [b \otimes [1]^\sharp, 1] \\ \uparrow \\ [a, 1]^\sharp \vee [b \otimes \{1\}, 1] \\ \downarrow \\ [a, 1]^\sharp \vee [b, 1] \vee [1]^\sharp \end{array}$$

Similarly, $([b, 1] \vee [a, 1]^\sharp) \otimes [1]^\sharp$ is the colimit of the diagram

$$\begin{array}{c} [1]^\sharp \vee [b, 1] \vee [a, 1]^\sharp \\ \uparrow \\ [b \otimes \{0\}, 1] \vee [a, 1]^\sharp \\ \downarrow \\ [b \otimes [1]^\sharp, 1] \vee [a, 1]^\sharp \\ \uparrow \\ [b \otimes \{1\}, 1] \vee [a, 1]^\sharp \\ \downarrow \\ [b, 1] \vee [1]^\sharp \vee [a, 1]^\sharp \longleftarrow [b, 1] \vee [a, 1] \longrightarrow [b, 1] \vee [a, 1]^\sharp \vee [1]^\sharp \end{array}$$

Eventually, the formulas (5.1.3.9) and the induction hypothesis imply that $[a^\sharp \times b, 1] \otimes [1]^\sharp$

244

5.1. MARKED $(\infty, \omega)$-CATEGORIES

is the colimit of the diagram

![img-276.jpeg](img-276.jpeg)

As all these colimits are special and composed of monomorphisms, the objects $([a, 1]^{\sharp} \vee [b, 1]) \otimes [1]^{\sharp}$, $([b, 1]^{\sharp} \vee [a, 1]^{\sharp}) \otimes [1]^{\sharp}$ and $[a^{\sharp} \times b, 1] \otimes [1]^{\sharp}$ are strict. As the colimit (5.1.2.4) is also special, $([a, 1]^{\sharp} \times [b, 1]) \otimes [1]^{\sharp}$ is strict.

All put together, $([a, 1]^{\sharp} \times [b, 1]) \otimes [1]^{\sharp}$ is the colimit of the diagram

![img-277.jpeg](img-277.jpeg)

Now, using the formula given in proposition 5.1.1.34, and taking the colimit line by

245

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

line of the previous diagram, \(([a,1]^{\sharp}\times [b,1])\otimes [1]^{\sharp}\) is the colimit of the diagram

![img-278.jpeg](img-278.jpeg)

Using for the last times formula (5.1.3.9), \(([a,1]^{\sharp}\times [b,1])\otimes [1]^{\sharp}\) is equivalent to \([a,1]^{\sharp}\times ([b,1]\otimes [1]^{\sharp})\)

Proposition 5.1.2.5. Let \( D \) be a marked \( (\infty, \omega) \)-category and \( K, L \) two \( (\infty, 1) \)-categories. There is a natural equivalence \( (D \otimes K^{\sharp}) \otimes L^{\sharp} \to D \otimes (K \times L)^{\sharp} \).

Proof. Suppose first that \( D \) is of shape \( C^b \). The proposition 4.2.1.61 implies that \( \coprod_{t(C^b \otimes K^\sharp)^\sharp} \mathbf{D}_n \to (C^b \otimes K^\sharp)^\sharp \) and \( (\coprod_n \tau_{n-1} C \otimes K) \to (C^b \otimes K^\sharp)^\sharp \) have the same image. The proposition 4.2.1.62, then implies that the underlying \( (\infty, \omega) \)-category of \( (C^b \otimes K^\sharp) \otimes L^\sharp \) fits in the cocartesian square

![img-279.jpeg](img-279.jpeg)

The second assertion of lemma 2.2.2.8 then implies that \(((C^b\otimes K^\sharp)\otimes L^\sharp)^\sharp\) is equivalent to \(C^b\otimes (K\times L)\). For a general marked \((\infty ,\omega)\)-category \(D\), the underlying \((\infty ,\omega)\)-category of \((D^{b}\otimes K^{\sharp})\otimes L^{\sharp}\) then fits by construction in the cocartesian square

![img-280.jpeg](img-280.jpeg)

Furthermore, the underlying \((\infty ,\omega)\)-category of \(D\otimes (K\times L)^{\sharp}\) fits in the cocartesian

246

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

square

\[
\begin{array}{c} \coprod_ {n} \coprod_ {t C _ {n}} \mathbf {D} _ {n} \otimes (K \times L) \longrightarrow D ^ {\flat} \otimes (K \times L) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \coprod_ {n} \coprod_ {t C _ {n}} \tau_ {n} ^ {i} (\mathbf {D} _ {n} \otimes (K \times L)) \longrightarrow (D \otimes (K \times L) ^ {\sharp}) ^ {\natural} \end{array}
\]

Using the canonical morphism \(\tau_n^i (\mathbf{D}_n\otimes K)\otimes L\to \tau_n^i (\mathbf{D}_n\otimes K\otimes L)\to \tau_n^i (\mathbf{D}_n\otimes (K\times L))\) we have a canonical morphism

\[
((D ^ {\flat} \otimes K ^ {\sharp}) \otimes L ^ {\sharp}) ^ {\natural} \to (D \otimes (K \times L) ^ {\sharp}) ^ {\natural}.
\]

As all these functors preserves colimits, the full sub \(\infty\)-groupoid of elements \((D, K, L)\) of \((\infty, \omega)\)-cat\(_{\mathrm{m}} \times (\infty, 1)\)-cat \(\times (\infty, 1)\)-cat such that this comparison is an equivalence and preserves and detects marking is closed by colimits. It is then sufficient to show that it includes \(([1]^{\sharp}, [1], [1])\) and \(([a, 1], [1], [1])\) for \(a \in t\Theta\). We can then proceed as in the proof of proposition 5.1.2.3, making these two objects explicit thanks to the equations given in paragraph 5.1.3.8. As the proof takes up a lot of space and is very similar to that of proposition op cit, we leave it to the reader.

#### 5.1.3 Gray operations on marked  \( (\infty,\omega) \) -categories

5.1.3.1. The Gray tensor product for marked  \( (\infty,\omega) \) -category restricts to a functor

\[
\_ \otimes [ 1 ] ^ {\sharp}: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

called the marked Gray cylinder. We will denote by

\[
\begin{array}{r c l} (\infty , \omega) \text {-cat} _ {\mathrm{m}} & \to & (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ C & \mapsto & C ^ {[ 1 ] ^ {\sharp}} \end{array}
\]

its right adjoint. The equation (4.3.1.1), establishing a link between the suspension and the Gray cylinder implies that the following diagram is cocartesian for any \( C: (\infty, \omega) \)-cat:

\[
\begin{array}{c} C ^ {\flat} \otimes \{0, 1 \} \longrightarrow C ^ {\flat} \otimes [ 1 ] ^ {\sharp} \\ \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text { (5.1.3.2) } \\ 1 \amalg 1 \longrightarrow [ C, 1 ] ^ {\sharp} \end{array}
\]

Proposition 5.1.3.3. There is diagram

\[
\begin{array}{c} (C \otimes \{1 \}) ^ {\circ} \longrightarrow (C \otimes [ 1 ] ^ {\sharp}) ^ {\circ} \longleftarrow (C \otimes \{0 \}) ^ {\circ} \\ \Big \downarrow^ {\sim} \qquad \qquad \qquad \Big \downarrow^ {\sim} \qquad \qquad \Big \downarrow^ {\sim} \\ C ^ {\circ} \otimes \{0 \} \longrightarrow C ^ {\circ} \otimes [ 1 ] ^ {\sharp} \longleftarrow C ^ {\circ} \otimes \{1 \} \end{array}
\]

247

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

natural in \( C: (\infty, \omega) \)-cat\(_{\mathrm{m}}\), where all vertical arrows are equivalences. There is an invertible natural transformation

\[
C \star 1 \sim (1 ^ {c o} \star C ^ {\circ}) ^ {\circ}.
\]

Proof. The corollary 4.3.3.21 provides an invertible transformation

\[
(C ^ {\circ} \otimes [ 1 ]) ^ {\circ} \sim (C ^ {\circ}) ^ {\circ} \otimes [ 1 ]
\]

The first assertion then follows from the definition of the Gray tensor product for marked  \( (\infty,\omega) \) -categories. The second assertion is a consequence of the definition of the marked Gray cone and o-cone.

Example 5.1.3.4. In all the following diagrams, marked cells are represented by crossed-out arrows.

The object \(\mathbf{D}_1^\flat \otimes [1]^{\sharp}\) corresponds to the diagram

![img-281.jpeg](img-281.jpeg)

the object  \( (\mathbf{D}_{1})^{\sharp} \otimes [1]^{\sharp} \)  corresponds to the diagram

![img-282.jpeg](img-282.jpeg)

the object \(\mathbf{D}_2^\flat \otimes [1]^{\sharp}\) corresponds to the diagram

![img-283.jpeg](img-283.jpeg)

and the object  \( (\mathbf{D}_{2})_{t} \otimes [1]^{\sharp} \)  corresponds to the diagram

![img-284.jpeg](img-284.jpeg)

5.1.3.5. We also define the functors

\[
\_ \star 1: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}} \qquad 1 \stackrel {c o} {\star} \_ : (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}},
\]

248

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

respectively called the marked Gray cone and the marked Gray o-cone, where for any marked  \( (\infty,\omega) \) -category C,  \( C\star1 \)  and  \( 1^{\star c}C \) , fit in the following cocartesian square

![img-285.jpeg](img-285.jpeg)

![img-286.jpeg](img-286.jpeg)

These two functors preserve colimit. The proposition 5.1.3.3 induces an invertible natural transformation

\[
C \star 1 \sim (1 ^ {\star} C ^ {\circ}) ^ {\circ}.
\]

Example 5.1.3.6. In all the following diagrams, marked cells are represented by crossed-out arrows.

The objects \(\mathbf{D}_1^\flat \star 1\) and \(1\stackrel {co}{\star}\mathbf{D}_1^\flat\) correspond respectively the diagrams

![img-287.jpeg](img-287.jpeg)

![img-288.jpeg](img-288.jpeg)

the objects \((\mathbf{D}_1)_t\star 1\) and \(1\stackrel {co}{\star}(\mathbf{D}_1)_t\) correspond respectively the diagrams

![img-289.jpeg](img-289.jpeg)

![img-290.jpeg](img-290.jpeg)

the objects \(\mathbf{D}_2^\flat \star 1\) and \(1\stackrel {co}{\star}\mathbf{D}_2^\flat\) correspond respectively the diagrams

![img-291.jpeg](img-291.jpeg)

![img-292.jpeg](img-292.jpeg)

and the objects \((\mathbf{D}_2)_t\star 1\) and \(1\stackrel {co}{\star}(\mathbf{D}_2)_t\) correspond respectively the diagrams

![img-293.jpeg](img-293.jpeg)

![img-294.jpeg](img-294.jpeg)

We will also denote by

\[
\begin{array}{c c c} (\infty , \omega) \text {-cat} _ {\mathrm{m} _ {\bullet}} & \to & (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ (C, c) & \mapsto & C _ {/ c} \end{array}
\]

\[
\begin{array}{c c c} (\infty , \omega) \text {-cat} _ {\mathrm{m} _ {\bullet}} & \to & (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ (C, c) & \mapsto & C _ {c /} \end{array}
\]

249

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

the right adjoints of Gray cone and of the Gray o-cone, respectively called the *slice of C over c* and the *slice of C under c*. The proposition 5.1.3.3 induces an invertible natural transformation:

$$C_{/c} \sim (C_{c/}^{\circ})^{\circ}.$$

Given an $(\infty, \omega)$-category $C$, and $c, d$ two objects, the cocartesian square (5.1.3.2) induces two cartesian squares:

$$\begin{array}{ccc} \hom_C(c, d)^{\flat} & \longrightarrow & C_{/d}^{\sharp} \\ \downarrow & \downarrow & \downarrow \\ \{c\} & \longrightarrow & C^{\sharp} \end{array} \qquad \begin{array}{ccc} \hom_C(c, d)^{\flat} & \longrightarrow & C_{c/}^{\sharp} \\ \downarrow & \downarrow & \downarrow \\ \{d\} & \longrightarrow & C^{\sharp} \end{array} \quad (5.1.3.7)$$

**5.1.3.8.** The equation given in paragraph 4.3.1.6 induces similar ones for the marked version of these operations. For every marked $(\infty, \omega)$-category $C$, there are a natural identification between $[C, 1] \otimes [1]^{\sharp}$ and the colimit of the following diagram

$$[1]^{\sharp} \vee [C, 1] \longleftarrow [C \otimes \{0\}, 1] \longrightarrow [C \otimes [1]^{\sharp}, 1] \longleftarrow [C \otimes \{1\}, 1] \longrightarrow [C, 1] \vee [1]^{\sharp} \quad (5.1.3.9)$$

There is also a natural identification between $1 \stackrel{\circ\circ}{\star} [C, 1]$ and the colimit of the diagram

$$[1]^{\sharp} \vee [C, 1] \longleftarrow [C, 1] \longrightarrow [C \star 1, 1] \quad (5.1.3.10)$$

and between $[C, 1] \star 1$ and the colimit of the diagram

$$[1 \stackrel{\circ\circ}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1]^{\sharp} \quad (5.1.3.11)$$

**5.1.3.12.** For any $C : (\infty, \omega)$-cat, we denote by $m_{C^{\sharp}}$ the colimit preserving functor $(\infty, \omega)\text{-cat}_m \rightarrow (\infty, \omega)\text{-cat}_m$ whose value on $[a, n]^{\flat}$ is $[a \times C^{\sharp}, n]$, on $[1]^{\sharp}$ is $[C, 1]^{\sharp}$, and on $[(\mathbf{D}_n)_t, 1]$ is $[(\mathbf{D}_n)_t \times C^{\sharp}, 1]$. Remark that the assignation $C \mapsto m_{C^{\sharp}}$ is natural in $C$ and that $m_1$ is the identity. We define the colimit preserving functor:

$$\begin{array}{ccc} (\infty, \omega)\text{-cat}_m \times (\infty, \omega)\text{-cat}_m & \rightarrow & (\infty, \omega)\text{-cat}_m \\ (X, Y) & \mapsto & X \ominus Y^{\sharp} \end{array}$$

where for any marked $(\infty, \omega)$-category $C$ and element $[b, n]$ of $\Delta[\Theta]$, $C \ominus [b, n]^{\sharp}$ is the following pushout:

$$\begin{array}{ccc} \coprod_{k \leq n} m_{b^{\sharp}}(C \otimes \{k\}) & \longrightarrow & m_{b^{\sharp}}(C \otimes [n]^{\sharp}) \\ \downarrow & & \downarrow \\ \coprod_{k \leq n} m_1(C \otimes \{k\}) & \longrightarrow & C \ominus [b, n]^{\sharp} \end{array} \quad (5.1.3.13)$$

250

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

By construction, we then have  \( C \ominus [1]^{\sharp} := C \otimes [1]^{\sharp} \) . The equation (4.3.1.15) implies that for every marked  \( (\infty, \omega) \) -category C, there is a natural identification between  \( [C, 1] \ominus [b, 1]^{\sharp} \)  and the colimit of the following diagram

\[
[ b, 1 ] ^ {\sharp} \vee [ C, 1 ] \leftarrow [ C \otimes \{0 \} \times b ^ {\sharp}, 1 ] \rightarrow [ (C \otimes [ 1 ] ^ {\sharp}) \times b ^ {\sharp}), 1 ] \leftarrow [ C \otimes \{1 \} \times b ^ {\sharp}, 1 ] \rightarrow [ C, 1 ] \vee [ b, 1 ] ^ {\sharp} \tag {5.1.3.14}
\]

Proposition 5.1.3.15. There is an equivalence

\[
(C \ominus B ^ {\sharp}) ^ {\circ} \sim C ^ {\circ} \ominus (B ^ {\circ}) ^ {\sharp}
\]

natural in C and B.

Proof. It is sufficient to construct this equivalence when \( B \) is of shape \( [b, n] \). The corollary 4.3.3.22 induces an equivalence

\[
(C ^ {\sharp} \otimes [ n ]) ^ {\circ} \sim (C ^ {\circ}) ^ {\sharp} \otimes [ n ] ^ {\circ}.
\]

By the construction of the Gray tensor product of marked \((\infty, \omega)\)-categories, we have an equivalence

\[
(C \otimes [ n ] ^ {\sharp}) ^ {\circ} \sim C ^ {\circ} \otimes ([ n ] ^ {\circ}) ^ {\sharp}.
\]

The results then directly follows from the definition of the operation \(\ominus\) and from the equivalence \((m_{b^{\sharp}}(\_))^{\circ} \sim m_{(b^{\sharp})^{\circ}}((\_)^{\circ})\).

Proposition 5.1.3.16. Let \( C \) be a \( (\infty, \omega) \)-category, \( D \) a marked \( (\infty, \omega) \)-category and \( [b, n] \) a globular sum.

(1) The underlying \((\infty, \omega)\)-category of \(C^{\circ} \ominus [b, n]^{\sharp}\) is \(C \ominus [b, n]\).
(2) The canonical morphism \( C^{\sharp} \ominus [b, n]^{\sharp} \to C^{\sharp} \times [b, n]^{\sharp} \) is an equivalence.
(3) The canonical morphism \((C^{\sharp} \times D) \ominus [b, n]^{\sharp} \to C^{\sharp} \times (D \ominus K^{\sharp})\) is an equivalence.

Proof. This is a consequence of propositions 4.2.1.51, 5.1.2.2, 5.1.2.3 and 5.1.2.5 and of the construction of \(\ominus\).

##### 5.1.3.17. We now give some strictification results.

Lemma 5.1.3.18. Let \(C\) be a marked \((\infty, \omega)\)-category. The canonical squares

![img-295.jpeg](img-295.jpeg)

are cartesian.

251

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

*Proof.* As the morphisms $\{\epsilon\} \to [1]$ for $\epsilon \leq 1$ are discrete Conduché functors, pullback along them preserves colimits, and we can then reduce to the case where $C$ is of the shape $[1]^\sharp$ or $[a, 1]$ with $a$ is an element of $t\Theta$. The case $C := [1]^\sharp$ is obvious as we have $[1]^\sharp \otimes [1]^\sharp \sim [1]^\sharp \times [1]^\sharp$ according to the first assertion of proposition 5.1.2.2. We then focus on the case $C := [a, 1]$.

We claim that for any marked $(\infty, \omega)$-category $D$, the square

$$\begin{array}{ccc} \{\epsilon\} & \longrightarrow & [D, 1] \\ \downarrow & & \downarrow \\ \{\epsilon\} & \longrightarrow & [1]^\sharp \end{array} \tag{5.1.3.19}$$

is cartesian. To show this, as the morphisms $\{\epsilon\} \to [1]$, are discrete Conduché functors one can reduce to the case where $D$ is a globular sum, where it is obvious.

We now return to the proof of the assertion. Using the equation (5.1.3.9), the morphism $[a, 1] \otimes [1]^\sharp$ is the horizontal colimit of the following diagram:

$$\begin{array}{ccccccccc} [1]^\sharp \vee [a, 1] & \longleftarrow & [a \otimes \{0\}, 1] & \longrightarrow & [a \otimes [1]^\sharp, 1] & \longleftarrow & [a \otimes \{1\}, 1] & \longrightarrow & [a, 1] \vee [1]^\sharp \\ \downarrow_{a^1} & & \downarrow & & \downarrow & & \downarrow_{a^0} & & \downarrow_{a^0} \\ [1]^\sharp & \longleftarrow & [1]^\sharp & \longrightarrow & [1]^\sharp & \longleftarrow & [1]^\sharp & \longrightarrow & [1]^\sharp \end{array}$$

The results is then a direct application of the cartesian square (5.1.3.19) and of the fact that pullbacks along morphisms $\{\epsilon\} \to [1]$ for $\epsilon \leq 1$ preserves colimits. $\square$

**Proposition 5.1.3.20.** *For any object $a$ of $t\Theta$, the marked $(\infty, \omega)$-categories $a \otimes [1]^\sharp$, $a \star 1$ and $1 \star a$ are strict.*

*Proof.* We will show only the strictness of the object $a \otimes [1]^\sharp$, as the proofs for $a \star 1$ and $1 \star a$ are similar.

Suppose first that $a$ is of shape $b^b$. The first assertion of proposition 5.1.2.2 implies that the underlying $(\infty, \omega)$-categories of $b^b \otimes [1]^\sharp$ is $b \otimes [1]$ which is strict according to proposition 4.3.3.19.

To conclude, we have to show that for any integer $n$, $(\mathbf{D}_n)_t \otimes [1]^\sharp$ is strict. We proceed by induction. Suppose first that $a$ is $(\mathbf{D}_1)_t$. The second assertion of proposition 5.1.2.2 implies that $(\mathbf{D}_1)_t \otimes [1]^\sharp$ is $([1] \times [1])^\sharp$ which is a strict object.

Suppose now that $(\mathbf{D}_n)_t \otimes [1]^\sharp$ is strict. The equation (5.1.3.9) stipulates that $(\mathbf{D}_{n+1})_t \otimes [1]^\sharp$ is the colimit of the diagram.

$$[1]^\sharp \vee [(\mathbf{D}_n)_t, 1] \leftarrow [(\mathbf{D}_n)_t \otimes \{0\}, 1] \rightarrow [(\mathbf{D}_n)_t \otimes [1]^\sharp, 1] \leftarrow [(\mathbf{D}_n)_t \otimes \{1\}, 1] \rightarrow [\mathbf{D}_n)_t, 1] \vee [1]^\sharp$$

The induction hypothesis and the proposition 4.3.3.2 implies that all the objects are strict. According to proposition 5.1.1.37, whose hypotheses are provided by lemma 5.1.3.18, this

252

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

diagram admits a special colimit. As all the morphisms are monomorphism, this implies that  \( (\mathbf{D}_{n+1})_{t} \otimes [1]^{\sharp} \)  is strict, which concludes the proof. □

Proposition 5.1.3.21. If \( C \) is a marked \( (\infty, \omega) \)-category, a a globular sum and \( a^{\flat} \to C \) any morphism, the \( (\infty, \omega) \)-categories \( C \coprod_{a^{\flat}} a^{\flat} \otimes [1]^{\sharp} \), \( C \coprod_{a^{\flat}} \star 1 \) and \( 1 \stackrel{co}{\star} a^{\flat} \coprod_{a} C \) are strict.

Proof. Using the first assertion of proposition 5.1.2.2, the underlying \((\infty, \omega)\)-categories of \(C \coprod_{a^{\flat}} a^{\flat} \otimes [1]^{\sharp}\), \(C \coprod_{a^{\flat}} a^{\flat} \star 1\) and \(1 \stackrel{co}{\star} a^{\flat} \coprod_{a} C\) are respectively \(C^{\natural} \coprod_{a} a \otimes [1]\), \(C^{\natural} \coprod_{a} a \star 1\) and \(1 \stackrel{co}{\star} a \coprod_{a} C^{\natural}\), which are strict objects according to propositions 4.3.3.12 and 4.3.3.17.

Theorem 5.1.3.22. If \( C \) is strict \( (\infty, \omega) \)-category, the marked \( (\infty, \omega) \)-categories \( C^{\flat} \star 1 \), \( 1 \stackrel{co}{\star} C^{\flat} \) and \( C^{\flat} \otimes [1]^{\sharp} \) are strict.

Proof. The first assertion of proposition 5.1.2.2 implies that the underlying \((\infty, \omega)\)-categories of these marked \((\infty, \omega)\)-categories respectively are \(C \star 1\), \(1 \stackrel{co}{\star} C\) and \(C \otimes [1]\). As these objects are strict according to theorem 4.3.3.26, this concludes the proof.

Proposition 5.1.3.23. The colimit preserving endofunctor \(F: (\infty, \omega)\)-cat \(\rightarrow (\infty, \omega)\)-cat\(_{\mathfrak{m}}\), sending \([a, n]\) to the colimit of the span

\[
\coprod_ {k \leq n} \{k \} \leftarrow \coprod_ {k \leq n} a ^ {\flat} \otimes \{k \} \rightarrow a ^ {\flat} \otimes [ n ] ^ {\sharp}
\]

is equivalent to the functor \((\_)^{\sharp}:(\infty ,\omega)\) -cat \(\rightarrow (\infty ,\omega)\) -catm.

Proof. This is a direct consequence of the first assertion of proposition 5.1.2.2, of corollary 4.3.3.24 and of the definition of the marking of the Gray tensor product for marked \((\infty, \omega)\)-categories.

The last proposition implies that for any marked  \( (\infty,\omega) \) -category C and any globular sum a, the simplicial  \( \infty \) -groupoid

\[
\begin{array}{l} \Delta^ {o p} \rightarrow \infty \text {-grd} \\ [ n ] \mapsto \operatorname{Hom} ([ a, n ] ^ {\sharp}, C) \\ \end{array}
\]

is a \((\infty, 1)\)-category.

Theorem 5.1.3.24. Let \( C \) be an \( (\infty, \omega) \)-category. The two following canonical squares are cartesian:

![img-296.jpeg](img-296.jpeg)

253

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

The five squares appearing in the following canonical diagram are both cartesian and cocartesian:

![img-297.jpeg](img-297.jpeg)

Proof. This is a direct consequence of the first assertion of proposition 5.1.2.2, of theorem 4.3.3.25 and of the definition of the marking of the Gray tensor product for marked $(\infty, \omega)$-categories. □

### 5.1.4 Marked Gray deformation retract

We provide analogous results for section 4.3.2, with proofs that are entirely similar and, therefore, omitted.

5.1.4.1. A left Gray deformation retract structure for a morphism $i : C \to D$ between marked $(\infty, \omega)$-categories is the data of a retract $r : D \to C$, a deformation $\psi : D \otimes [1]^\sharp \to D$, and equivalences

$$ri \sim id_C \quad \psi_{|D \otimes \{0\}} \sim ir \quad \psi_{|D \otimes \{1\}} \sim id_D \quad \psi_{|C \otimes [1]^\sharp} \sim i \operatorname{cst}_C$$

A morphism $i : C \to D$ between marked $(\infty, \omega)$-categories is a left Gray deformation retract if it admits a left deformation retract structure. By abuse of language, such data will just be denoted by $(i, r, \psi)$.

We define dually the notion of right Gray deformation retract structure and of right Gray deformation retract in exchanging 0 and 1 in the previous definition.

We define similarly the notion of left or right deformation retract by replacing $\otimes$ by $\times$.

5.1.4.2. A left Gray deformation retract structure for a morphism $i : f \to g$ in the $(\infty, 1)$-category of arrows of $(\infty, \omega)$-cat$_m$ is the data of a retract $r : g \to f$, a deformation $\psi : g \otimes [1]^\sharp \to g$ and equivalences

$$ri \sim id_f \quad \psi_{|g \otimes \{0\}} \sim ir \quad \psi_{|g \otimes \{1\}} \sim id_D \quad \psi_{|f \otimes [1]^\sharp} \sim i \operatorname{cst}_C$$

A morphism $i : C \to D$ between two arrows of $(\infty, \omega)$-cat$_m$ is a left Gray deformation retract if it admits a left deformation retract structure. By abuse of language, such data will just be denoted by $(i, r, \psi)$.

254

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

We define dually the notion of right Gray deformation retract structure and of right Gray deformation retract in exchanging 0 and 1 in the previous definition.

We define similarly the notion of left and right deformation retract by replacing \(\otimes\) by \(\times\).

Example 5.1.4.3. Let C be a marked  \( (\infty,\omega) \) -category. The morphism  \( C\otimes\{0\}\to C\otimes[1]^{\sharp} \)  is a left Gray deformation retract. Indeed, the retract is given by  \( C\otimes\mathbb{I}:C\otimes[1]^{\sharp}\to C\otimes\{0\} \) , and the natural transformation is induced by

\[
(C \otimes [ 1 ] ^ {\sharp}) \otimes [ 1 ] ^ {\sharp} \sim C \otimes ([ 1 ] \times [ 1 ]) ^ {\sharp} \xrightarrow {C \otimes \psi^ {\sharp}} C \otimes [ 1 ] ^ {\sharp}
\]

where the first equivalence is the one of proposition 5.1.2.5, and \(\psi : [1] \times [1] \to [1]\) is the unique morphism sending \((\epsilon, \epsilon')\) to \(\epsilon \wedge \epsilon'\).

Similarly, the morphism \(C \otimes \{1\} \to C \otimes [1]^{\sharp}\) is a right deformation retract.

##### 5.1.4.4. Left and right Gray retracts enjoy many stability properties:

Proposition 5.1.4.5. Let \((i_a, r_a, \psi_a)\) be a natural family of left (resp. right) Gray deformation retract structures indexed by an \((\infty, 1)\)-category \(A\). The triple \((\operatorname{colim}_A i_a, \operatorname{colim}_A r_a, \operatorname{colim}_A \psi_a)\) is a left (resp. right) \(k\)-Gray deformation retract structure.

Proposition 5.1.4.6. Suppose given a diagram

![img-298.jpeg](img-298.jpeg)

such that \( p \to p' \) and \( q \to q' \) are left (resp. right) Gray deformation retract. The induced square \( q^*p \to (q')^*p' \) is a left (resp. right) \( k \)-Gray deformation retract.

Proposition 5.1.4.7. If \( p \to p' \) and \( p' \to p'' \) are two left (resp. right) Gray deformation retracts, so is \( p \to p'' \).

Proposition 5.1.4.8. Let \((i:C\to D,r,\psi)\) be a left (resp. right) Gray deformation structure. For any \(x:C\) and \(y:D\) (resp. \(x:D\) and \(y:C\)), the morphism

\[
\hom_ {C} (x, r y) \stackrel {i} {\rightarrow} \hom_ {D} (i x, i r y) \stackrel {\psi_ {y!}} {\longrightarrow} \hom_ {D} (i x, y)
\]

\[
(r e s p. \hom_ {C} (r x, y) \stackrel {i} {\rightarrow} \hom_ {D} (i r x, i y) \stackrel {\psi_ {y!}} {\longrightarrow} \hom_ {D} (x, i y))
\]

is a right (resp. left) Gray deformation retract, whose retract is given by

\[
\hom_ {D} (i x, y) \xrightarrow {r} \hom_ {C} (x, r y)
\]

\[
(r e s p. \hom_ {D} (x, i y) \stackrel {r} {\rightarrow} \hom_ {C} (r x, y))
\]

255

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

If \((i:C\to D,r,\psi)\) is a left (resp. right) deformation structure, for any \(x:C\) and \(y:D\) (resp. \(x:D\) and \(y:C\)), the two morphisms above are inverses one of each other.

Proposition 5.1.4.9. For any left (resp. right) Gray deformation retracts between \( p \) and \( p' \):

\[
\begin{array}{c} C \xrightarrow {i} D \\ p \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ C ^ {\prime} \xrightarrow [ i ^ {\prime} ]{} D ^ {\prime} \end{array}
\]

and for any pair of objects \( x: C \) and \( y: D \) (resp. \( x: D \) and \( y: C \)), the outer square of the following diagram

\[
\begin{array}{c} \hom_ {C} (x, r y) \xrightarrow {i} \hom_ {D} (i x, i r y) \xrightarrow {\psi_ {y _ {1}}} \hom_ {D} (i x, y) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_ {C ^ {\prime}} (p x, p r ^ {\prime} y) \xrightarrow [ i ^ {\prime} ]{} \hom_ {D ^ {\prime}} (p ^ {\prime} i ^ {\prime} x, p ^ {\prime} i ^ {\prime} r ^ {\prime} y) \xrightarrow [ \psi_ {p ^ {\prime} y _ {1}} ^ {\prime} ]{} \hom_ {D ^ {\prime}} (p ^ {\prime} i ^ {\prime} x, p ^ {\prime} y) \end{array}
\]

(resp.

\[
\begin{array}{c} \hom_ {C} (r x, y) \xrightarrow {i} \hom_ {D} (i r x, i y) \xrightarrow {\psi_ {x _ {1}}} \hom_ {D} (x, i y) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_ {C ^ {\prime}} (p r ^ {\prime} x, p y) \xrightarrow [ i ^ {\prime} ]{} \hom_ {D ^ {\prime}} (p ^ {\prime} i ^ {\prime} r ^ {\prime} x, p ^ {\prime} i ^ {\prime} y) \xrightarrow [ \psi_ {p ^ {\prime} x _ {1}} ^ {\prime} ]{} \hom_ {D ^ {\prime}} (p ^ {\prime} x, p ^ {\prime} i ^ {\prime} y)) \end{array}
\]

is a left (resp. right) Gray deformation retract, whose retract is given by

\[
\begin{array}{c} \hom_ {D} (i x, y) \xrightarrow {r} \hom_ {C} (x, r y) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_ {D ^ {\prime}} (p ^ {\prime} i ^ {\prime} x, p ^ {\prime} y)) \xrightarrow [ r ^ {\prime} ]{} \hom_ {C ^ {\prime}} (p x, p r ^ {\prime} y) \end{array}
\]

\[
\begin{array}{c} (r e s p. \hom_ {D} (x, i y) \xrightarrow {r} \hom_ {C} (r x, y) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_ {D ^ {\prime}} (p ^ {\prime} x, p ^ {\prime} i ^ {\prime} y) \xrightarrow [ r ^ {\prime} ]{} \hom_ {C ^ {\prime}} (p r ^ {\prime} x, p y)) \end{array}
\]

If \( p \to p' \) is a left (resp. right) deformation structure, for any \( x: C \) and \( y: D \) (resp. \( x: D \) and \( y: C \)), the two morphisms above are inverses one of each other.

Proposition 5.1.4.10. If i is a left Gray deformation retract,  \( [i,1] \)  is a right Gray deformation retract. Conversely, if i is a right Gray deformation retract,  \( [i,1] \)  is a left Gray deformation retract morphism.

Proposition 5.1.4.11. Let \( a \) be a globular sum of dimension \( (n + 1) \). We denote by \( s_n(a) \) and \( t_n(a) \) the globular sum defined in 1.1.2.12. If \( n \) is even, \( s_n(a)^{\flat} \to a^{\sharp_n} \) is a left Gray deformation retract, and \( t_n(a)^{\flat} \to a^{\sharp_n} \) is a right Gray deformation retract. Dually, if \( n \) is odd, \( t_n(a)^{\flat} \to a^{\sharp_n} \) is a left Gray deformation retract, and \( s_n(a)^{\flat} \to a^{\sharp_n} \) is a right Gray deformation retract.

256

5.1. MARKED \((\infty, \omega)\)-CATEGORIES

Proposition 5.1.4.12. Let \( i: C \to D \) be a left Gray deformation retract and \( A \) a marked \( (\infty, \omega) \)-category. The morphism \( A \times i \) is a left Gray deformation retract.

Proof. Let \( r \) and \( \psi \) be retracts and deformation of \( i \). We define \( \psi_A \) as the composite

\[
(A \times D) \otimes [ 1 ] ^ {\sharp} \to A \times (D \otimes [ 1 ] ^ {\sharp}) \xrightarrow {A \times \psi} A \times D
\]

Remark that the triple \((A\times i,A\times r,\psi_A)\) is a left Gray deformation retract structure.

Proposition 5.1.4.13. Let \((i:[C,1]\to D,r,\phi)\) be a left deformation retract structure. The following natural square is cartesian:

![img-299.jpeg](img-299.jpeg)

Proof. We set  \( P := [C, 1] \times_{D} \underline{\mathrm{Hom}}([1]^{\sharp}, D) \)  and  \( \psi : D \to P \)  the induced morphism. The proposition 5.1.1.34 implies that  \( \hom_{P}(\psi(x), \psi(y)) \)  is the limit of the diagram:

\[
\hom_ {[ C, 1 ]} (r x, r y) \xrightarrow {i} \hom_ {D} (i r x, i r y) \xrightarrow {\phi_ {y !}} \hom_ {D} (i r x, y) \xleftarrow {\phi_ {x !}} \hom_ {D} (x, y)
\]

The proposition 5.1.4.8 then implies that the canonical morphism

\[
\hom_ {D} (x, y) \to \hom_ {P} (\psi (x), \psi (y))
\]

is an equivalence.

The morphism  \( \psi \)  is then fully faithful. According to proposition 5.1.1.24, it remains to show that it induces a surjection on objects. For this, let  \( v : x \to y \)  be an element of P. As the only marked 1-cells in  \( [C, 1] \)  are equivalences,  \( r(v) \)  is an equivalence. The morphism

\[
[ 1 ] ^ {\sharp} \times [ 1 ] ^ {\sharp} \xrightarrow {v \times [ 1 ] ^ {\sharp}} D \times [ 1 ] ^ {\sharp} \xrightarrow {\phi} D
\]

induces a square in D of shape

![img-300.jpeg](img-300.jpeg)

where all the arrows labeled by  \( \sim \)  are equivalences. This implies that  \( v \sim \phi(y) \)  and the morphism  \( \psi \)  is then surjective on objects. This concludes the proof. ☐

257

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

## 5.2 Cartesian fibrations

### 5.2.1 Left and right cartesian fibrations

**5.2.1.1.** We denote by I the set of morphisms of shape $X \otimes \{0\} \to X \otimes [1]^\sharp$ for $X$ being either $\mathbf{D}_n^b$ or $(\mathbf{D}_n)_t$. A morphism is *initial* if it is in $\widehat{\mathbf{I}}$. Conversely, we denote by F the set of morphisms of shape $X \otimes \{1\} \to X \otimes [1]^\sharp$ for $X$ being either $\mathbf{D}_n^b$ or $(\mathbf{D}_n)_t$. A morphism is *final* if it is in $\widehat{\mathbf{F}}$.

Initial and final morphisms are stable under colimits, retract, composition and left cancellation according to the result of section 4.1.2.

The proposition 5.1.3.3 implies that the full duality $(\_)^\circ$ sends final (resp. initial) morphisms to initial (resp. final) morphisms.

**Example 5.2.1.2.** By stability of initial and final morphisms by colimits, for any marked $(\infty, \omega)$-category $C$, $C \otimes \{0\} \to C \otimes [1]^\sharp$ is initial, and $C \otimes \{1\} \to C \otimes [1]^\sharp$ is final.

**Proposition 5.2.1.3.** *Left Gray deformation retracts (resp. left deformation retract) are initial and right Gray deformation retracts (resp. right deformation retract) are final.*

*Proof.* Let $i : C \to D$ be a left Gray deformation retract. The diagram

$$\begin{array}{ccc} C & \xrightarrow{i} & D \otimes \{0\} & \xrightarrow{r} & C \\ i \downarrow & & \downarrow & & \downarrow \\ D \otimes \{1\} & \longrightarrow & D \otimes [1]^\sharp & \xrightarrow{\psi} & D \end{array}$$

expresses $i$ as a retract of $D \otimes \{0\} \to D \otimes [1]^\sharp$, which is an initial morphism according to example 5.2.1.2. The morphism $i$ is then initial.

As left deformation retracts are left Gray deformation retracts, they are initial. The case of right (Gray) deformation retracts follows by duality. $\square$

**Corollary 5.2.1.4.** *Let $a$ be a globular sum of dimension $(n+1)$. We denote by $s_n(a)$ and $t_n(a)$ the globular sum defined in 1.1.2.12. If $n$ is even, $s_n(a)^b \to a^{\sharp n}$ is initial, and $t_n(a)^b \to a^{\sharp n}$ is final. Dually, if $n$ is odd, $t_n(a)^b \to a^{\sharp n}$ is initial, and $s_n(a)^b \to a^{\sharp n}$ is final*
*Proof.* This is a direct consequence of propositions 5.1.4.11 and 5.2.1.3. $\square$

**Proposition 5.2.1.5.** *For any $n$, the morphism $\mathbb{I}_n : (\mathbf{D}_{n+1})_t \to \mathbf{D}_n^b$ is both initial and final.*

*Proof.* According to lemma 5.2.1.4 there exists $\alpha \in \{-, +\}$ such that $i_n^\alpha : (\mathbf{D}_n)^b \to (\mathbf{D}_{n+1})_t$ is initial. As $\mathbb{I}_n$ is a retraction of this morphism, and as initial morphisms are closed under left cancellation according to proposition 4.1.2.3, $\mathbb{I}_n$ is initial. The second case follows by duality. $\square$

258

5.2. CARTESIAN FIBRATIONS

These morphisms will be called the *marked trivializations*.

**Proposition 5.2.1.6.** *Let $C$ be a marked $(\infty, \omega)$-category. The morphism $C \otimes [1]^{\sharp} \to C$ is in the smallest cocomplete $\infty$-groupoid of morphism containing the marked trivialization. In particular, this morphism is both initial and final.*

*Proof.* We denote $K$ the smallest cocomplete $\infty$-groupoid of morphisms containing the marked trivializations. As the $\infty$-groupoid of objects $C$ fulfilling the wanted property is closed by colimits, it is sufficient to demonstrate the result for $C$ being either $\mathbf{D}_n^b$ or $(\mathbf{D}_{n+1})_t$ for $n$ an integer. We will then proceed by induction. Suppose first that $C$ is $\mathbf{D}_0^b$ or $(\mathbf{D}_1)_t$. The first case is trivial, for the second one, remark that $(\mathbf{D}_1)_t \otimes [1]^{\sharp} \sim [1]^{\sharp} \times [1]^{\sharp} \to [1]^{\sharp}$ is the horizontal colimit of the diagram

![img-301.jpeg](img-301.jpeg)

and is then in $K$. Suppose now the result is true at the stage $(n - 1)$. Let $C$ be $\mathbf{D}_n^b$ (resp. $(\mathbf{D}_{n+1})_t$). We set $D := \mathbf{D}_{n-1}^b$ (resp. $D := (\mathbf{D}_n)_t$). We then have $C \sim [D, 1]$. The equation (5.1.3.9) implies that $C \otimes [1]^{\sharp} \to C$ is the horizontal colimit of the diagram:

![img-302.jpeg](img-302.jpeg)

The leftest and rightest morphisms obviously are in $K$. As marked trivializations are stable by suspension, the induction hypothesis implies that the middle vertical morphisms of the previous diagram are in $K$, which concludes the proof. $\square$

**Proposition 5.2.1.7.** *Let $C$ be a marked $(\infty, \omega)$-category. The morphism $C \otimes [1]^{\sharp} \to C \times [1]^{\sharp}$ is in the smallest cocomplete $\infty$-groupoid of morphism containing the marked trivializations. In particular, this morphism is both initial and final.*

*Proof.* We denote $K$ the smallest cocomplete $\infty$-groupoid of morphisms containing the marked trivializations. As the $\infty$-groupoid of objects $C$ fulfilling the wanted property is closed by colimits, it is sufficient to demonstrate the result for $C$ being either $\mathbf{D}_n^b$ or $(\mathbf{D}_{n+1})_t$ for $n$ an integer. If $C$ is either $(\mathbf{D}_0)^b$ or $(\mathbf{D}_1)_t$ the considered morphism is the identity. We then suppose that $n > 0$. Let $C$ be $\mathbf{D}_n^b$ (resp. $(\mathbf{D}_{n+1})_t$). We set $D := \mathbf{D}_{n-1}^b$ (resp. $D := (\mathbf{D}_n)_t$). We then have $C \sim [D, 1]$. The equation (5.1.3.9) and the equation

259

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

given in 5.1.1.34 imply that $C \otimes [1]^\sharp \to C \times [1]^\sharp$ is the horizontal colimit of the diagram:

![img-303.jpeg](img-303.jpeg)

The proposition 5.2.1.6 then states that the middle vertical morphisms of the previous diagram are in $K$, which concludes the proof. $\square$

**Proposition 5.2.1.8.** *If $i$ is an initial morphism, $[i, 1]$ is a final morphism. Conversely, if $i$ is a final morphism, $[i, 1]$ is an initial morphism.*

*Proof.* As the suspension preserves colimits, we can restrict to the case where $i$ is of shape $C \otimes \{0\} \to C \otimes [1]^\sharp$, and this is then a consequence of propositions 5.1.4.10 and 5.2.1.3. $\square$

**Proposition 5.2.1.9.** *For any marked $(\infty, \omega)$-category $K$, the functor $K \times \_ : (\infty, \omega)\text{-cat}_\text{m} \to (\infty, \omega)\text{-cat}_\text{m}$ preserves initial and final morphisms.*

*Proof.* The functor $K \times \_$ preserves colimits and this is then enough to show that it preserves left and right Gray deformation retracts, which is a consequence of proposition 5.1.4.12. $\square$

**5.2.1.10.** *A left cartesian fibration is a morphism $f : C \to D$ between marked $(\infty, \omega)$-categories having the unique right lifting property against initial morphisms. A right cartesian fibration is a morphism $f : C \to D$ between marked $(\infty, \omega)$-categories having the unique right lifting property against final morphisms.*

Left and right cartesian fibrations are stable under limits, retract, composition and right cancellation according to the result of section 4.1.2.

The proposition 5.1.3.3 implies that the full duality $(\_)^\circ$ sends left (resp. right) cartesian fibrations to right (resp. left) cartesian fibrations.

The construction 4.1.2.14 produces a unique factorization system between initial (resp final) morphisms and left (resp. right) cartesian fibrations. If $f : A \to B$ is any morphism, we will denote by $\mathbf{F}f : A' \to B$ the left cartesian fibration obtained via this factorization system.

**Proposition 5.2.1.11.** *If $f : C \to D^\flat$ is a left cartesian fibration, then the canonical morphism $(C^\flat)^\flat \to C$ is an equivalence. Conversely, any morphism $C^\flat \to D^\flat$ is a left cartesian fibration.*

*Proof.* The first assertion is a consequence of the fact that marked trivializations are initial. The second assertion is a direct consequence of proposition 5.2.1.6. $\square$

260

5.2. CARTESIAN FIBRATIONS

**Proposition 5.2.1.12.** Let $p : X \to C$ be a morphism, and $x, y$ two objects of $X$. Then, if $p$ is a right (resp. left) cartesian fibration, the induced morphism $p : \hom_X(x, y) \to \hom_C(x, y)$ is a left (resp. right) cartesian fibration.

*Proof.* This is a direct consequence of proposition 5.2.1.8.

**Proposition 5.2.1.13.** Consider a cocartesian square

$$
\begin{array}{c}
X'' \xrightarrow{j} X' \longrightarrow X \\
p'' \downarrow \quad \downarrow \quad p' \downarrow \quad \downarrow \quad p \downarrow \\
Y'' \xrightarrow{i} Y' \longrightarrow Y
\end{array}
$$

If $p$ is a left (resp. right) cartesian fibration and $i$ is a right (resp. left) Gray deformation retract, then $p'' \to p'$ is a right (resp. left) Gray deformation retract. Moreover, this left (resp. right) Gray deformation retract structure is functorial in $p$.

Similarly, if $p$ is a left (resp. right) cartesian fibration and $i$ is a right (resp. left) deformation retract, then $p'' \to p'$ is a right (resp. left) deformation retract. This left (resp. right) deformation retract structure is functorial in $p$.

*Proof.* We suppose that $p$ is a right cartesian fibration. By stability under pullbacks, so is $p'$. Let $(i : C \to D, r, \phi)$ be a left Gray deformation retract structure. We define the morphism $\psi$ as the lift of the following commutative square:

$$
\begin{array}{c}
X'' \otimes [1]^{\sharp} \cup X' \otimes \{0\} \xrightarrow{(X'' \otimes \mathbb{I}) \cup id} X' \\
\downarrow \quad \downarrow \quad \psi \quad \downarrow p' \\
X' \otimes [1]^{\sharp} \xrightarrow{} Y'' \otimes [1]^{\sharp} \longrightarrow Y'
\end{array}
$$

Remark that the restriction of $\psi$ to $X' \otimes \{1\}$ factors through $X''$ and then defines a retract $s : Y \to X$ of $j$. This provides a right Gray deformation structure for $p \to p''$. We proceed similarly for the dual case.

The functoriality of the Gray deformation retract structure comes from the fact that only functorial operations were used. Indeed, pullbacks, pushouts and the Gray tensor product are functorial. The formation of the lift $\psi$ is also functorial according to proposition 4.1.2.11.

To verify the second claim, one may utilize the same proof, exchanging $\otimes$ with $\times$. $\square$

**Corollary 5.2.1.14.** Let $p : X \to B^{\sharp}$ and $q : Y \to B^{\sharp}$ be two left cartesian fibrations and $\phi : p \to q$ a morphism over $B^{\sharp}$. The morphism $\phi$ is an equivalence if and only if, for any object $b$ of $B$, the induced morphism $\{b\}^*\phi : \{b\}^*X \to \{b\}^*Y$ is an equivalence.

261

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proof. As  \( \mathrm{tPsh}^{\infty}(\Theta) \)  is locally cartesian closed, pullback commutes with special colimits, and as every  \( (\infty,\omega) \) -category is the special colimit of its k-truncation for  \( k\in N \)  according to proposition 5.1.1.35, one can suppose that B is a marked  \( (\infty,k) \) -category for  \( k<\omega \), and we then proceed by induction on k. Suppose then the result is true for  \( (\infty,k) \) -categories and that B is an  \( (\infty,k+1) \) -category. Remark first that  \( \phi \)  induces an equivalence between  \( \tau_{0}(X) \)  and  \( \tau_{0}(Y) \).

Let \( x \) and \( y \) be two objects of \( X \) and \( v: [1]^{\sharp} \to B^{\sharp} \) be a cell whose source is \( px \) and target \( py \). This induces cartesian squares

![img-304.jpeg](img-304.jpeg)

By hypothesis, \(\phi_1\) is an equivalence. According to proposition 5.2.1.13, \(\phi_1 \to \phi_v\) is a right deformation retract, and according to proposition 5.1.4.8, this induces a cartesian square

![img-305.jpeg](img-305.jpeg)

where horizontal morphisms are equivalences. By hypothesis, the left vertical one is an equivalence, and then, by two out of three, so is the right vertical one.

We then have, for any 1-cell v, the following cartesian squares

![img-306.jpeg](img-306.jpeg)

where the arrow labeled by  \( \sim \)  is an equivalence. As  \( \hom_{B}(px,py)^{\sharp} \)  is an  \( (\infty,k) \) -category, the induction hypothesis implies that  \( \hom_{X}(x,y)\to\hom_{Y}(\psi x,\psi y) \)  is an equivalence. The morphism  \( \phi \)  is then fully faithful, and as we already know that it is essentially surjective, this concludes the proof.

5.2.1.15. We have by construction a factorization system in initial morphism followed by left cartesian fibration, and another one in final morphism followed by right cartesian

262

5.2. CARTESIAN FIBRATIONS

fibration. We are willing to find an explicit expression for such factorization in some easy cases. We then fix  \( i : C^{b} \to D \)  with D being any marked  \( (\infty, \omega) \) -category.

If \( C^b \to D \) is a functor between marked \( (\infty, \omega) \)-categories, we define \( D_{/C^b} \) and \( D_{C^b/} \) as the following pullbacks

![img-307.jpeg](img-307.jpeg)

![img-308.jpeg](img-308.jpeg)

If \( C \) is the terminal \( (\infty, \omega) \)-category, this notation is compatible with the one of the slice over and under introduced in paragraph 5.1.3.5.

Lemma 5.2.1.16. The morphism \(i:C^{b}\to D_{/C^{b}}\) appearing in the following diagram

![img-309.jpeg](img-309.jpeg)

is initial.

Proof. Using proposition 5.1.2.5, we have a natural transformation

\[
(\_ \otimes [ 1 ] ^ {\sharp}) \otimes [ 1 ] ^ {\sharp} \sim \_ \otimes ([ 1 ] ^ {\sharp} \times [ 1 ] ^ {\sharp}) \xrightarrow {\otimes \psi} \_ \otimes [ 1 ] ^ {\sharp}
\]

where \(\psi\) sends \((\epsilon, \epsilon')\) on \(\max(\epsilon, \epsilon')\). This induces a natural transformation \(D^{[1]^{\sharp}} \to (D^{[1]^{\sharp}})^{[1]^{\sharp}}\), corresponding by adjunction to transformation \(\phi: D^{[1]^{\sharp}} \otimes [1]^{\sharp} \to D^{[1]^{\sharp}}\). We set \(r: D_{C^{\flat}/} \to C^{\flat}\) as the canonical projection. Eventually, remark that \((i, r, \phi)\) is a left Gray deformation retract. According to proposition 5.2.1.3, this concludes the proof.

Lemma 5.2.1.17. The composite \(q: D_{C^{\flat}/} \to D^{[1]^{\sharp}} \xrightarrow{(i_0^{+})_{!}} D\) is a left cartesian fibration.

Proof. Consider a commutative diagram

\[
\begin{array}{c} K \otimes \{0 \} \longrightarrow D _ {C ^ {\flat} /} \\ \Big \downarrow \quad \Big \downarrow \\ K \otimes [ 1 ] ^ {\sharp} \longrightarrow D \end{array} \tag {5.2.1.18}
\]

263

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

The \(\infty\)-groupoid of lifts of this previous diagram is equivalent to the \(\infty\)-groupoid of pairs consisting of a commutative triangle

![img-310.jpeg](img-310.jpeg)

where \( f \) is induced by \( K \otimes \{0\} \to D_{C^{\flat}/} \), and a lift in the induced diagram

![img-311.jpeg](img-311.jpeg)

According to proposition 5.2.1.6, the morphism \( K \otimes [1]^{\sharp} \otimes \{0\} \to C^{\flat} \) factors through a morphism \( K \to C^{\flat} \), and is then uniquely determined by \( f: K \otimes \{0\} \otimes \{0\} \to C^{\flat} \), and proposition 5.1.2.5 provides a natural equivalence between \( (K \otimes [1]^{\sharp}) \otimes [1]^{\sharp} \) and \( K \otimes ([1]^{\sharp} \times [1]^{\sharp}) \). The \( \infty \)-groupoid of lifts of the diagram (5.2.1.18) is then equivalent to the \( \infty \)-groupoid of lifts of the left square of the following diagram

![img-312.jpeg](img-312.jpeg)

As \( K \otimes [1]^{\sharp} \coprod_{K \otimes [0]} K \otimes [1]^{\sharp} \to K \otimes [2]^{\sharp} \) is an equivalence, this \( \infty \)-groupoid is contractible.

Proposition 5.2.1.19. The factorisation of \( p: C^b \to D \) in an initial morphism followed by a left cartesian fibration is

\[
C ^ {b} \xrightarrow {i} D _ {C ^ {b} /} \xrightarrow {q} D,
\]

and its factorization in a final morphism and a right cartesian fibration is

\[
C ^ {b} \xrightarrow {i} D _ {/ C ^ {b}} \xrightarrow {q} D.
\]

Proof. This is a direct application of lemma 5.2.1.16 and 5.2.1.16 and of their dual version.

The more important example of the previous proposition is the case  \( C := \{a\} \) . In this case, the corresponding left cartesian fibration is the slice of D under a

\[
D _ {a /} \rightarrow D
\]

264

5.2. CARTESIAN FIBRATIONS

and the corresponding right cartesian fibration is the slice of $D$ over $a$

$$D_{/a} \to D.$$

**5.2.1.20.** Let $p : X \to Y$ be a morphism between $(\infty, \omega)$-categories. A marked 1-cell $v : x \to x'$ is *left cancellable* if for any $y$, the following natural square is cartesian:

$$\begin{array}{ccc} \hom_X(x', y) & \xrightarrow{v_!} & \hom_X(x, y) \\ \downarrow & & \downarrow \\ \hom_Y(px', py) & \xrightarrow{p(v)_!} & \hom_Y(px, py) \end{array}$$

Conversely, a 1-cell $v : y \to y'$ is *right cancellable* if for any $x$, the following natural square is cartesian:

$$\begin{array}{ccc} \hom_X(x, y) & \xrightarrow{v_!} & \hom_X(x, y') \\ \downarrow & & \downarrow \\ \hom_Y(px, py) & \xrightarrow{p(v)_!} & \hom_Y(px, py') \end{array}$$

**Lemma 5.2.1.21.** *Let $p$ be a morphism. The following conditions are equivalent:*

- (1) $p$ has the unique right lifting property against $\{0\} \to [1]^\sharp$ and marked 1-cells are left cancellable.
- (2) $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [1]^\sharp \vee [a, 1]$ for any object $a$ of $t\Theta$.
- (3) $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [1]^\sharp \vee [a, 1]$ and $[1]^\sharp \xrightarrow{\nabla} [1]^\sharp \vee [1]^\sharp$ for any object $a$ of $t\Theta$.

*Conversely, the following are equivalent:*

- (1)' $p$ has the unique right lifting property against $\{1\} \to [1]^\sharp$ and marked 1-cells are right cancellable.
- (2)' $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [a, 1] \vee [1]^\sharp$ for any object $a$ of $t\Theta$.
- (3)' $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [a, 1] \vee [1]^\sharp$ and $[1]^\sharp \xrightarrow{\nabla} [1]^\sharp \vee [1]^\sharp$ for any object $a$ of $t\Theta$.

265

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proof. The fact that 1-cells are left cancellable is equivalent to asking that i has the unique right lifting property against

\[
[ a, 1 ] \amalg_ {\{0 \}} [ 1 ] ^ {\sharp} \to [ 1 ] ^ {\sharp} \vee [ a, 1 ]
\]

for any object \( a \) of \( t\Theta \). Suppose that \( p \) fulfills (1). As the class of morphisms having the unique right lifting property against \( p \) are closed under composition and by left cancellation according to 4.1.2.3, this implies that \( p \) has the unique right lifting property against

\[
[ a, 1 ] \xrightarrow {\nabla} [ 1 ] ^ {\sharp} \vee [ a, 1 ]
\]

and then that (1) \(\Rightarrow\) (2).

Suppose now that \( p \) fulfills (2). Remark that we have a retract

![img-313.jpeg](img-313.jpeg)

and as the class of morphisms having the unique right lifting property against p is closed under retracts, this implies that p has the unique right lifting property against  \( \{0\}\to[1]^{\sharp} \) . By stability by left cancellation, p has the unique right lifting property against

\[
[ a, 1 ] \amalg_ {\{0 \}} [ 1 ] ^ {\sharp} \to [ 1 ] ^ {\sharp} \vee [ a, 1 ].
\]

As remarked above, this implies that 1-cells are left cancellable. We then have (1) \(\Leftrightarrow\) (2).

There is an obvious implication  \( (3) \Rightarrow (2) \) . For the converse, remark that the class of morphisms having the unique right lifting property against p is closed under colimits and then contains  \( \{0\} \rightarrow [1]^{\sharp} \vee [1]^{\sharp} \) , and so by left cancellation, it includes  \( [1]^{\sharp} \xrightarrow{\nabla} [1]^{\sharp} \vee [1]^{\sharp} \) . The proof of the equivalence of  \( (1)' \) ,  \( (2)' \)  and  \( (3)' \)  is symmetrical. ☐

Lemma 5.2.1.22. Let \( p: X \to Y \) be a morphism having the unique right lifting property against marked trivializations, such that for any element \( a \) of \( t\Theta \), and any cartesian squares:

![img-314.jpeg](img-314.jpeg)

the square \( p'' \to p' \) is a right deformation retract. Then, \( p \) has the unique right lifting property against \( [a,1] \xrightarrow{\nabla} [1]^{\sharp} \vee [a,1] \) for any object \( a \) of \( t\Theta \).

266

5.2. CARTESIAN FIBRATIONS

Proof. Suppose given a square

![img-315.jpeg](img-315.jpeg)

and let $p'$ and $p''$ be the morphisms appearing in the following cartesian squares:

![img-316.jpeg](img-316.jpeg)

To show the proposition, one has to demonstrate that the induced diagram

![img-317.jpeg](img-317.jpeg)

admits a unique lifting. We denote by $x_0$ and $x_2$ the image of the object of $[a, 1]$ via the morphism $j$, and $(k : X'' \to X', r, \phi)$ the left deformation retract existing by hypothesis. According to the dual version of proposition 5.1.4.13, the unique marked 1-cell in $X'$ over $[1]^{\sharp} \hookrightarrow [1]^{\sharp} \vee [a, 1]$ with $x_0$ for source is $\phi(x_0) : x_0 \to r(x_0)$. The $\infty$-groupoid of lifts of this diagram is then equivalent to the $\infty$-groupoid of lifts of the following diagram

![img-318.jpeg](img-318.jpeg)

However, the right vertical morphism is an isomorphism according to proposition 5.1.4.8 which concludes the proof.

5.2.1.23. Keeping in mind the last lemma, we define $\mathrm{I}_g$ and $\mathrm{F}_g$ as the smallest sets of morphisms of $(0, \omega)$-cat$_\mathrm{m}$ fulfilling these conditions:

(1) for any $a \in \Theta^{\ell}$, $[a, 1] \hookrightarrow [1]^{\sharp} \vee [a, 1]$ is in $\mathrm{F}_g$ and $[a, 1] \hookrightarrow [a, 1] \vee [1]^{\sharp}$ is in $\mathrm{I}_g$
(2) for any $i$ in $\mathrm{F}_g$, $[i, 1]$ is in $\mathrm{I}_g$, for any $j$ in $\mathrm{I}_g$, $[i, 1]$ is in $\mathrm{F}_g$,

Propositions 5.1.4.5 and 5.1.4.10 then imply that morphisms of $\mathrm{I}_g$ are left Gray deformation retracts and morphisms of $\mathrm{F}_g$ are right Gray deformation retracts.

267

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

5.2.1.24. We extend by induction the definition of right and left cancellable to cells of any dimension as follows: a n-cell v is left or right cancellable (resp. right cancellable) if the corresponding  \( (n-1) \) -cell of  \( \operatorname{hom}_{X}(x,y) \)  is left cancellable (resp. right cancellable) for the morphism  \( \operatorname{hom}_{X}(x,y)\to\operatorname{hom}_{Y}(px,py) \) , where x and y denote the 0-sources and 0-but of v.

Lemma 5.2.1.25. Let \( p': X' \to Y' \) be a morphism such that \( p \) has the unique right lifting property against marked trivializations and suppose that we have a left Gray deformation retract \( p' \to p \). We denote by \( (r: Y' \to Y, i, \phi) \) the left deformation retract structure induced on the codomain, and suppose that the deformation \( \phi: Y \otimes [1]^{\sharp} \to Y \) factors through \( \psi: Y \times [1]^{\sharp} \to Y \). Then, the square \( p' \to p \) is a left deformation retract.

Proof. Proposition 5.2.1.7 states that \( Y \otimes [1]^{\sharp} \to Y \times [1]^{\sharp} \) is a colimit of marked trivializations. There is then a lift in the following diagram:

![img-319.jpeg](img-319.jpeg)

where  \( \phi' \)  is the deformation induced on domains. This endows  \( p' \rightarrow p \)  with a structure of left deformation retract, where the retraction is the same, and the deformation is given by  \( (\psi', \psi) \) . ☐

Theorem 5.2.1.26. Consider the following shape of diagram

\[
\begin{array}{c} X ^ {\prime \prime} \longrightarrow X ^ {\prime} \longrightarrow X \\ p ^ {\prime \prime} \Biggl \downarrow \quad \quad \quad p ^ {\prime} \Biggl \downarrow \quad \quad \quad p \Biggl \downarrow \\ Y ^ {\prime \prime} \xrightarrow [ i ]{} Y ^ {\prime} \longrightarrow Y \end{array} \tag {5.2.1.27}
\]

The following are equivalent:

(1) The morphism \( p \) is a left cartesian fibration.
(2) \( p \) has the unique right lifting property against marked trivialization, and for any diagram of shape (5.2.1.27), if \( i \) is a right Gray deformation retract, so is \( p'' \to p' \).
(3) \( p \) has the unique right lifting property against marked trivialization and, for any diagram of shape (5.2.1.27), if \( i \) is in \( \mathrm{F}_g \), the square \( p'' \to p' \) is a right Gray deformation retract.
(4) For any even integer \( n \), \( p \) has the unique right lifting property against \( i_n^+ : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t \) and marked \( n \)-cells are right cancellable; for any odd integer \( p \) has the unique right lifting property against \( i_n^- : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t \) and marked \( n \)-cells are left cancellable.

268

5.2. CARTESIAN FIBRATIONS

(5) $p$ as the unique right lifting property against $\{0\} \to [1]^{\sharp}$, marked 1-cells are left cancellable, and for any pair of objects $(x, y)$ of $X$, $\hom_X(x, y) \to \hom_Y(px, py)$ is a right cartesian fibration.

Conversely, the following are equivalent:

(1)' The morphism $p$ is a right cartesian fibration.
(2)' $p$ has the unique right lifting property against marked trivialization and for any diagram of shape (5.2.1.27), if $i$ is a left Gray deformation retract, so is $p'' \to p'$.
(3)' $p$ has the unique right lifting property against marked trivialization, and for any diagram of shape (5.2.1.27), if $i$ is in $\mathrm{I}_g$, the square $p'' \to p'$ is a left Gray deformation retract.
(4)' For any even integer $n$, $p$ has the unique right lifting property against $i_n^- : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ and marked $n$-cells are left cancellable; for any odd integer $p$ has the unique right lifting property against $i_n^+ : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ and marked $n$-cells are right cancellable.
(5)' $p$ as the unique right lifting property against $\{1\} \to [1]^{\sharp}$, marked 1-cells are right cancellable, and for any pair of objects $(x, y)$ of $X$, $\hom_X(x, y) \to \hom_Y(px, py)$ is a left cartesian fibration.

Proof. The implication from (1) to (2) and (1)' to (2)' is the content of proposition 5.2.1.13.

The implication from (2) to (3) and (2)' to (3)' comes from the fact that $\mathrm{I}_g$ (resp. $\mathrm{F}_g$) consists of right (resp. left) Gray deformation retracts.

Suppose now that $p$ fulfills condition (3). Lemma 5.2.1.25 implies that if $i$ is of shape $[a, 1] \hookrightarrow [1]^{\sharp} \vee [a, 1]$ for $a : t\Theta$, $p'' \to p'$ is a right deformation retract. Lemma 5.2.1.22 and 5.2.1.21 then imply that $p$ has the unique right lifting property against $\{0\} \to [1]^{\sharp}$ and marked 1-cells are left cancellable.

We are now willing to show that for any pair of objects $(x, y)$, $\hom_X(x, y) \to \hom_Y(px, py)$ fulfills condition (3)', and an obvious induction will complete the proof of (3) $\Rightarrow$ (4). We then consider $x, y$ two objects of $X$, $i : b \to a$ in $\mathrm{I}_g$ and any morphism $a \to \hom_Y(px, py)$. The previous data induces a pullback square

$$\begin{array}{c} X'' \longrightarrow X' \longrightarrow X \\ p'' \downarrow \quad \downarrow \quad p' \downarrow \quad \downarrow \quad p \downarrow \\ [b, 1] \xrightarrow{[i, 1]} [a, 1] \longrightarrow Y \end{array}$$

where the bottom right morphism sends $\{0\}$ to $px$ and $\{1\}$ to $py$. By construction, $[i, 1]$ is in $\mathrm{F}_g$, and so by assumption, the morphism $p' \to p''$ is a right Gray deformation retract.

269

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

Applying the functor $\hom_(\_, \_)$ we get the following pullback diagram:

$$\begin{array}{ccc} \hom_{X''}(x, y) & \longrightarrow & \hom_{X'}(x, y) & \longrightarrow & \hom_X(x, y) \\ \tilde{p}'' \downarrow & & \tilde{p}' \downarrow & & \tilde{p} \downarrow \\ b & \xrightarrow{i} & a & \longrightarrow & \hom_Y(px, py) \end{array}$$

and the dual version of proposition 5.1.4.9 implies that $\tilde{p}'' \to \tilde{p}'$ is a left Gray deformation retract. As this is true for any $i : b \to a$ in $I_g$, for any object of $X$, and any $a \to \hom_Y(px, py)$, this implies that $\hom_X(x, y) \to \hom_Y(px, py)$ fulfills condition (3)'. As mentioned above, an obvious induction induces (3) $\Rightarrow$ (4). We show similarly (3)' $\Rightarrow$ (4)'.

Now let's show (4) $\Rightarrow$ (1) and (4)' $\Rightarrow$ (1)'. We show by induction on $n$ that for any element $a$ of $t\,G_n := \{\mathbf{D}_k\}_{0 \leq k \leq n} \cup \{(\mathbf{D}_k)_l\}_{1 \leq k \leq n}$, if $p$ fulfills (4) (resp. (4)') $p$ has the unique right lifting property against $a \otimes \{0\} \to a \otimes [1]^\sharp$ (against $a \otimes \{1\} \to a \otimes [1]^\sharp$).

Suppose then that this is true at the stage $n$, and suppose that $p$ fulfills (4). Let $a$ be an object of $t\,G_n$. Remark that according to the equation (5.1.3.9), $[a, 1] \otimes \{0\} \to [a, 1] \otimes [1]^\sharp$ fits in the sequence of pushouts

$$\begin{array}{ccc} [0] & \xrightarrow{i_0^+} & [a, 1] \otimes \{0\} \\ \downarrow_{i_0} & & \downarrow \\ [1]^\sharp & \longrightarrow & [a, 1] \vee [1]^\sharp \longleftarrow [a \otimes \{1\}, 1] \\ & & \downarrow \searrow \downarrow \\ [a, 1] & \longrightarrow & [a, 1] \vee [1]^\sharp \cup [a \otimes [1]^\sharp, 1] \longleftarrow [a \otimes [1]^\sharp, 1] \\ \downarrow_{\nabla} & & \downarrow \\ [1]^\sharp \vee [a, 1] & \longrightarrow & [a, 1] \otimes [1]^\sharp \end{array}$$

By induction hypothesis, for any pair of objects $(x, y)$ of $X$, $\hom_X(x, y) \to \hom_Y(px, py)$ has the unique right lifting property against $a \otimes \{1\} \to a \otimes [1]^\sharp$ for $a \in t\,G_n$. Furthermore, lemma 5.2.1.21 implies that $p$ has the unique right lifting property against $\nabla : [a, 1] \to [1]^\sharp \vee [a, 1]$. The morphism $p$ then has the unique right lifting property against $[a \otimes \{1\}, 1] \to [a \otimes [1]^\sharp, 1]$ for $a \in t\,G_n$. The class of morphisms having the unique right lifting property against $p$ being closed under colimits, this implies that it includes $[a, 1] \otimes \{0\} \to [a, 1] \otimes [1]^\sharp$. To conclude, one has to show that $p$ has the unique right lifting property against $[1]^\sharp \times \{0\} \to [1]^\sharp \times [1]^\sharp$. Remark that according to proposition 5.1.1.34, $[1]^\sharp \times \{0\} \to [1]^\sharp \times [1]^\sharp$

270

5.2. CARTESIAN FIBRATIONS

fits in the sequence of pushouts:

$$\begin{array}{c} [0] \xrightarrow{i_0^+} [1]^{\sharp} \times \{0\} \\ i_0^- \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1]^{\sharp} \longleftrightarrow [1]^{\sharp} \vee [1]^{\sharp} \xleftarrow{\nabla} [1]^{\sharp} \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1]^{\sharp} \times [1]^{\sharp} \xleftarrow{\quad} [1]^{\sharp} \vee [1]^{\sharp} \end{array}$$

According to lemma 5.2.1.21, $p$ has the unique right lifting property against $\nabla : [1]^{\sharp} \to [1]^{\sharp} \vee [1]^{\sharp}$ and so also against $[1]^{\sharp} \times \{0\} \to [1]^{\sharp} \times [1]^{\sharp}$. This concludes the proof of the implication $(4) \Rightarrow (1)$. We show similarly $(4)' \Rightarrow (1)'$.

Eventually, the equivalences $(1) \Rightarrow (5)$ and $(1)' \Rightarrow (5)'$ are a consequence of proposition 5.2.1.12 and of the implications $(1) \Rightarrow (4)$ and $(1)' \Rightarrow (4)'$. The implications $(5) \Rightarrow (4)$ and $(5)' \Rightarrow (4)'$ are a consequence of the implications $(1)' \Rightarrow (4)'$ and $(1) \Rightarrow (4)$ applied to the morphisms $\hom_X(x, y) \to \hom_Y(px, py)$ for all objects $x, y$. $\square$

**Corollary 5.2.1.28.** *A morphism $p : X \to A^{\sharp}$ is a left cartesian fibration if and only if for any globular sum $b$ and morphism $j : b \to A$, $j^*p$ is a left cartesian fibration over $b^{\sharp}$.*

*Proof.* This is a direct consequence of the equivalence between conditions (1) and (3) of theorem 5.2.1.26, and the fact that the codomains of marked trivializations and the codomains of morphisms of $F_g$ are marked globular sums. $\square$

### 5.2.2 Cartesian fibration are exponentiable

We recall that a marked globular sum is a marked $(\infty, \omega)$-category whose underlying $(\infty, \omega)$-category is a globular sum and such that for any pair of integers $k \le n$, and any pair of $k$-composable $n$-cells $(x, y)$, $x \circ_k y$ is marked if and only if $x$ and $y$ are marked.

A morphism $i : a \to b$ between marked globular sums is globular if the morphism $i^{\sharp}$ is globular.

A globular morphism $i$ between marked globular sums is then a discrete Conduché functor, which implies according to proposition 5.1.1.29 that the functor $i^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/b} \to (\infty, \omega)\text{-cat}_{\mathrm{m}/a}$ preserves colimits.

**5.2.2.1.** Let $b$ be a globular sum and $f : X \to b^{\sharp}$ a morphism. We say that $f$ is $b$-exponentiable if the canonical morphism

$$\underset{i: \mathrm{Sp}_b^{\sharp}}{\operatorname{colim}} i^* f \to f$$

is an equivalence.

271

CHAPTER 5. THE $$(\infty, 1)$$-CATEGORY OF MARKED $$(\infty, \omega)$$-CATEGORIES

**Proposition 5.2.2.2.** Let $$F : I \to (\infty, \omega)$$-$$\text{cat}_{\text{m}/b^{\sharp}}$$ be a functor which is pointwise $$b$$-exponentiable. The morphism $$\text{colim}_I F$$ is $$b$$-exponentiable

*Proof.* Remark that all morphisms $$\mathbf{D}_n^{\sharp} \to b^{\sharp}$$ in $$\text{Sp}_b^{\sharp}$$ are globular, and so are discrete Conduché functors. We then have a sequence of equivalences

$$\underset{i:\text{Sp}_b^{\sharp}}{\text{colim}} i^* \underset{I}{\text{colim}} F \sim \underset{I}{\text{colim}} \underset{i:\text{Sp}_b^{\sharp}}{\text{colim}} i^* F \sim \underset{I}{\text{colim}} F.$$

□

**Proposition 5.2.2.3.** Let $$a$$ be a globular sum, and $$f : X \to a^{\sharp}$$ be a morphism. The induced morphism $$\text{colim}_{i:\text{Sp}_a^{\sharp}} i^* f$$ is $$a$$-exponentiable.

*Proof.* As marked globular morphisms are marked discrete Conduché functors, for any $$j : \mathbf{D}_n^{\sharp} \to a^{\sharp} \in \text{Sp}_a$$, $$j^* \text{colim}_{i:\text{Sp}_a^{\sharp}} i^* f$$ is equivalent to $$j^* f$$. We then have a sequence of equivalences

$$\underset{j:\text{Sp}_a^{\sharp}}{\text{colim}} j^* \underset{i:\text{Sp}_a^{\sharp}}{\text{colim}} i^* f \sim \underset{j:\text{Sp}_a^{\sharp}}{\text{colim}} j^* f.$$

□

**Proposition 5.2.2.4.** Let $$f : X \to b^{\sharp}$$ be exponentiable in $$b$$ and $$j : a^{\sharp} \to b^{\sharp}$$ a globular morphism. The morphism $$j^* f : X \to a^{\sharp}$$ is exponentiable in $$a$$.

*Proof.* The morphism $$j : a^{\sharp} \to b^{\sharp}$$ is a marked discrete Conduché functor, so $$j^*$$ preserves colimits according to proposition 5.1.1.29. We then have a sequence of equivalences

$$j^* f \sim j^* \underset{i:\text{Sp}_b}{\text{colim}} i^* f \sim \underset{i:\text{Sp}_b}{\text{colim}} (ji)^* f \sim \underset{k:\text{Sp}_a}{\text{colim}} k^* f.$$

□

**Lemma 5.2.2.5.** Let $$i : c \to d$$ be in $$\text{F}_g$$, $$b$$ a globular sum, and $$f : d \to b^{\sharp}$$ any morphism. Then, there exists a commutative square

$$\begin{array}{c} c' \xrightarrow{i'} d' \longrightarrow b^{\sharp} \\ h \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ c \xrightarrow{i} d \end{array}$$

- (1) $$d \to d'$$ is a finite composition of pushouts of morphism of shape $$i_n^{\alpha} : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$$ with $$n$$ an integer and $$\alpha := +$$ if $$n$$ is even, and $$-$$ if not.
- (2) $$d' \to b^{\sharp}$$ is globular.
- (3) $$h \to g$$ is a right Gray deformation retract.

272

5.2. CARTESIAN FIBRATIONS

Proof. We obtain $(d')^{\natural}$ by factorizing $f^{\natural}$ into an algebraic morphism $g^{\natural}$ followed by a globular morphism. The marking $d'$ is the smaller one that makes $g$ a morphism of marked $(0, \omega)$-categories. By construction, $c \to d$ fits in a cocartesian square

$$\begin{array}{c} \mathbf{D}_{n}^{\flat} \longrightarrow c \\ i_{0}^{\alpha} \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (\mathbf{D}_{n+1})_{t} \longrightarrow d \end{array}$$

where all morphisms are globular, and where $\alpha$ is $+$ if $n$ is even, and $-$ if not. As the procedure is similar for any $n$, we will suppose that $n = 0$, and $d$ is then equivalent to $[1]^{\sharp} \vee [a, 1]$ for $a \in t\Theta$. The fact that $g$ is algebraic implies that there exists a marked globular sum $c'$ and an integer $k$, such that $d'$ is of shape $[k]^{\sharp} \vee c'$ and such that $gi$ factors through $c'$. These data verify the desired condition.

**Proposition 5.2.2.6.** Let $p: X \to b^{\sharp}$ be a morphism exponentiable in $b$. Consider also the following shape of diagram

$$\begin{array}{c} X'' \longrightarrow X' \longrightarrow X \\ p'' \Big\downarrow \quad \quad \quad p' \Big\downarrow \quad \quad \quad p \Big\downarrow \\ C \xrightarrow[i]{} C' \xrightarrow[j]{} b^{\sharp} \end{array} \tag{5.2.2.7}$$

The following are equivalent.

(1) For any globular morphism $i: [a, 1]^{\sharp} \to b^{\sharp}$, $i^*p$ is a left cartesian fibration.
(2) For any diagram of shape (5.2.2.7), if $i$ is $i_n^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ with $n$ an integer and $\alpha := +$ if $n$ is even and $-$ if not, and $j$ is globular, then $p'' \to p'$ is a right Gray deformation retract.
(3) For any diagram of shape (5.2.2.7), if $i$ is a finite composition of pushouts of morphism of shape $i_n^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ with $n$ an integer and $\alpha := +$ if $n$ is even and $-$ if not, and $j$ is globular, then $p'' \to p'$ is a right Gray deformation retract.
(4) For any diagram of shape (5.2.2.7), if $i$ is in $\mathrm{F}_g$, then $p'' \to p'$ is a right Gray deformation retract.
(5) The morphism $p$ is a left cartesian fibration.

Proof. The implication $(1) \Rightarrow (2)$ comes from theorem 5.2.1.26 as morphisms of shape $i_n^{\alpha}$ are right Gray deformation retracts according to proposition 5.1.4.11, and as every globular morphism $\mathbf{D}_{n+1} \to b$ factors through a globular morphism $[a, 1] \to b$.

273

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

We suppose that the second condition is fulfilled. As left Gray deformation retracts are stable under composition according to proposition 5.1.4.7, we can restrict to the case where $i': c \to d$ fits in a cocartesian square

![img-320.jpeg](img-320.jpeg)

where all morphisms are globular, and where $\alpha$ is $+$ if $n$ is even, and $-$ if not. Let $p_0$ and $p_1$ be the morphism fitting in cocartesian squares

![img-321.jpeg](img-321.jpeg)

This defines a diagram in the $(\infty, 1)$-category of arrows of $(\infty, \omega)$-cat$_m$:

![img-322.jpeg](img-322.jpeg)

As the proposition 5.2.2.4 implies that $p'$ is $d$-exponentiable, the morphism $p'' \to p'$ is the horizontal colimit of the previous diagram. According to proposition 5.2.1.13, $p_0 \to p_1$ is a left Gray deformation retract, and proposition 5.1.4.5 implies that $p'' \to p'$ also is a left Gray deformation retract. This proves (2) $\Rightarrow$ (3).

Suppose now that condition (3) is fulfilled and let $i$ be in F$_g$. Consider the diagram

![img-323.jpeg](img-323.jpeg)

induced by lemma 5.2.2.5. We denote by $\tilde{p}''$ and $\tilde{p}'$ the morphisms fitting in the following cartesian squares.

![img-324.jpeg](img-324.jpeg)

As $p$ fulfills (3), $\tilde{p}'' \to \tilde{p}'$ is a right Gray deformation retract. By construction, the square $h \to g$ also is a right Gray deformation retract. As $p''$ and $p'$ are respectively the pullback

274

5.2. CARTESIAN FIBRATIONS

of $\tilde{p}''$ along $h$ and the pullback of $\tilde{p}'$ along $g$, the dual version of 5.1.4.6 implies that $p'' \to p'$ is a right Gray deformation retract.

The implication $(4) \Rightarrow (5)$ is induced by theorem 5.2.1.26. Eventually, the implication $(5) \Rightarrow (1)$ is a consequence of the preservation of left cartesian fibration under pullback.

**Corollary 5.2.2.8.** *A fibration $p$ over $a^\sharp$ is $a$-exponentiable.*

*Proof.* We define $q := \operatorname{colim}_{i:\mathrm{Sp}_0^\sharp} i^*p$. This morphism comes with a canonical comparison $q \to p$. According to proposition 5.2.2.3, $q$ is $a$-exponentiable. For any globular morphism $j : [b, 1]^\sharp \to a$, we have $j^*q \sim j^*p$ as $j$ is a discrete Conduché functor. In particular, $j^*q$ is a left cartesian fibration and $q$ then verifies the first condition of proposition 5.2.2.6. This implies that $q$ is a left cartesian fibration.

As all morphisms $j : 1 \to a^\sharp$ are marked globular, and so are discrete Conduché functors, there are equivalences

$$j^* \underset{i:\mathrm{Sp}_0^\sharp}{\operatorname{colim}} i^*p \sim j^*p$$

and the morphism $q \to p$ induces an equivalence on fiber. This morphisms is then an equivalence according to corollary 5.2.1.14.

**Lemma 5.2.2.9.** *Let $f : A \to B^\sharp$ be a left cartesian fibration, $n$ an integer, and consider a diagram of $\mathrm{tPsh}^\infty(\Theta)$ of shape*

$$\begin{array}{c} A'' \xrightarrow{j} A' \longrightarrow A \\ \downarrow f'' \quad \downarrow f' \quad \downarrow f \\ (\Sigma^n E^{eq})^\flat \xrightarrow{i} \mathbf{D}_n^\flat \longrightarrow B^\sharp \end{array}$$

*Then $j$ is in $\widehat{\mathrm{tW}}$.*

*Proof.* As $f'$ and $f''$ are left cartesian fibrations, the only marked cell in $A'$ and $A''$ are the identities according to proposition 5.2.1.11. We can then suppose that the left square lies in $(\infty, \omega)$-cat, and then apply proposition 4.2.2.8.

**Lemma 5.2.2.10.** *Let $b$ be a globular sum, and $n$ an integer. For any cartesian squares in $\mathrm{Psh}^\infty(\Theta)$,*

$$\begin{array}{c} A'' \xrightarrow{j} A' \longrightarrow b^{\sharp n} \\ \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \\ B'' \xrightarrow{i} B' \longrightarrow b^\sharp \end{array}$$

*if $i$ is in $\widehat{\mathrm{tW}}$, so is $j$.*

275

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proof. As  \( \mathrm{tPsh}^{\infty}(\Theta) \)  is cartesian closed, one can suppose that i is in W. In this case the diagram can be seen as a diagram in  \( \mathrm{Psh}(\Theta) \) . The proof is an easy verification of all the possible cases. □

Proposition 5.2.2.11. For any cartesian square of \(\mathrm{tPsh}^{\infty}(\Theta)\),

![img-325.jpeg](img-325.jpeg)

where \( f \) is a left cartesian fibration, if \( i \) is in \( \widehat{\mathrm{tW}} \), so is \( j \).

Proof. As  \( \mathrm{tPsh}^{\infty}(\Theta) \)  is cartesian closed, one can suppose that i is in W. Several cases have to be considered. If i is of shape  \( (\Sigma^{n}E^{eq})^{b}\to\mathbf{D}_{n}^{b} \) , this is lemma 5.2.2.9. Suppose now that i is of shape  \( Sp_{b}^{\sharp_{n}}\to b^{\sharp_{n}} \) . This induces a diagram

![img-326.jpeg](img-326.jpeg)

where all squares are cartesian. Corollary 5.2.2.8 implies that \( j' \) is in \( \widehat{\mathrm{W}} \), and according to lemma 5.2.2.10, so is \( j \).

A left cartesian fibration  \( A \rightarrow B \)  is classified if there exists a cocartesian square:

![img-327.jpeg](img-327.jpeg)

Theorem 5.2.2.12. Let \( p: A \to B \) be a classified left cartesian fibration. The functor \( p^*: (\infty, \omega) \)-cat\(_{\mathrm{m}/B} \to (\infty, \omega) \)-cat\(_{\mathrm{m}/A}\) preserves colimits.

Proof. As  \( \mathrm{tPsh}(\Theta) \)  is locally cartesian closed, it is enough to show that the functor  \( p^{*}: \mathrm{tPsh}^{\infty}(\Theta)_{/B} \to \mathrm{tPsh}^{\infty}(\Delta[\Theta])_{/A} \)  sends tW onto  \( t\widehat{W} \) . As morphisms fulfilling this property are stable under pullback, one can suppose that p is of shape  \( B \to A^{\sharp} \) , then applies proposition 5.2.2.11. □

276

5.2. CARTESIAN FIBRATIONS

Corollary 5.2.2.13. Let $B$ be the colimit of a diagram $F: I \to (\infty, \omega)$-cat, and $p: X \to \operatorname{colim}_i B_i$ a left cartesian fibration. The canonical morphism

$$\underset{i:B_i \to B}{\operatorname{colim}} i^* p \to p$$

is an equivalence.

Proof. This morphism corresponds to the square

$$\begin{array}{c} \operatorname{colim}_{i:I} p^* B_i \longrightarrow X \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow_p \\ \operatorname{colim}_{i:I} B_i \longrightarrow B^\sharp \end{array}$$

The lower horizontal morphism is an equivalence by hypothesis, and the upper one is an equivalence as $p^*$ preserves colimits.

### 5.2.3 Colimits of cartesian fibrations

Through this section, we will identify any marked $(\infty, \omega)$-category $C$ with the canonical induced morphism $C \to 1$. If $f: X \to Y$ is a morphism, $f \times C$ then corresponds to the canonical morphism $X \times C \to Y$.

Lemma 5.2.3.1. Let $b$ be a globular sum and $F: I \to (\infty, \omega)$-cat$_{\mathrm{m}/b^\sharp}$ be a diagram that is pointwise a left cartesian fibration. The induced morphism $\operatorname{colim}_I F$ is a left cartesian fibration over $b^\sharp$.

Proof. We denote $G: I \to (\infty, \omega)$-cat$_{\mathrm{m}}$ the diagram induced by $F$ by taking the domain. Remark first that proposition 5.2.2.2 implies that $\operatorname{colim}_I F$ is $b$-exponentiable. Let $n$ be an integer. Suppose given cartesian squares

$$\begin{array}{c} Y' \xrightarrow{f} Y \xrightarrow{} \operatorname{colim}_I X \\ \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \operatorname{colim}_I F \\ \mathbf{D}_n^\flat \xrightarrow[i_n^\alpha]{} (\mathbf{D}_{n+1})_t \xrightarrow[j]{} b^\sharp \end{array}$$

where $\alpha$ is $+$ is $n$ is even and $-$ if not and with $j$ globular. According to proposition 5.2.2.6, we have to show that $f$ is a right Gray deformation retract to conclude. As $F$ is pointwise a left cartesian fibration, proposition 5.2.1.13 implies that for any $i: I$, the morphism $f(i)$ appearing in the cartesian squares:

$$\begin{array}{c} Y' \xrightarrow{f(i)} Y \xrightarrow{} X(i) \\ \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow_{F(i)} \\ \mathbf{D}_n^\flat \xrightarrow[i_n^\alpha]{} (\mathbf{D}_{n+1})_t \xrightarrow[j]{} b^\sharp \end{array}$$

277

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

is a right Gray deformation retract, and that the corresponding Gray deformation retract structure is functorial in $i : I$. As $j$ and $ji_n^\alpha$ are marked globular, they are discrete Conduché functors, and so exponentiable according to proposition 5.1.1.29. The following canonical morphism

$$\underset{I}{\operatorname{colim}} f(i) \to f$$

is then an equivalence. As right Gray deformation retract structures are stable by colimits, this concludes the proof.

**Lemma 5.2.3.2.** *Let $A$ be an $(\infty, \omega)$-category and $F : I \to (\infty, \omega)\text{-cat}_{\mathrm{m}/A^\sharp}$ be a diagram that is pointwise a left cartesian fibration. Let $i : a^\sharp \to b^\sharp$ be a morphism between globular sums and $i : b^\sharp \to A^\sharp$ any morphism. The canonical comparison*

$$\underset{I}{\operatorname{colim}}(ji)^* F \to i^* \underset{I}{\operatorname{colim}} j^* F$$

*is an equivalence.*

*Proof.* Lemma 5.2.3.1 implies that the two morphisms are left cartesian fibrations. As equivalences between these morphisms are detected on fibers, we can suppose that $a$ is [0]. In this case, the morphism $i$ is a discrete Conduché functor, and is then exponentiable according to proposition 5.1.1.29. This directly concludes the proof.

**Theorem 5.2.3.3.** *Let $A$ be an $(\infty, \omega)$-category and $F : I \to (\infty, \omega)\text{-cat}_{\mathrm{m}/A^\sharp}$ be a diagram that is pointwise a left cartesian fibration. The induced morphism $\operatorname{colim}_I F$ is a left cartesian fibration over $A^\sharp$.*

*Proof.* Consider the functor $\psi : \Theta_{/A} \to \operatorname{Arr}((\infty, \omega)\text{-cat}_\mathrm{m})$ whose value on $j : b \to A$ is $\operatorname{colim}_I j^* F$. As $F$ is pointwise a left cartesian fibration, the corollary 5.2.2.13 induces equivalences

$$\underset{\Theta_{/A}}{\operatorname{colim}} \psi := \underset{j:b \to A}{\operatorname{colim}} \underset{I}{\operatorname{colim}} j^* F \sim \underset{I}{\operatorname{colim}} \underset{j:b \to A}{\operatorname{colim}} j^* F \sim \underset{I}{\operatorname{colim}} F$$

The functor $\psi$ is cartesian according to lemma 5.2.3.2, and as $\operatorname{codom} \psi$ as a special colimit (given by $A^\sharp$), so has $\psi$ according to proposition 5.1.1.33. In particular, this implies that for any $j : b \to A$, the following canonical morphism

$$\underset{I}{\operatorname{colim}} j^* F =: \psi(j) \to j^* \underset{\Theta_{/A}}{\operatorname{colim}} \psi \sim j^* \underset{I}{\operatorname{colim}} F$$

is an equivalence. As the left object is a left cartesian fibration according to lemma 5.2.3.1, so is the right one. As this is true for any $j : b \to A$, the corollary 5.2.1.28 implies that $\operatorname{colim}_I F$ is a left cartesian fibration.

278

5.2. CARTESIAN FIBRATIONS

Corollary 5.2.3.4. Let A be an  \( (\infty,\omega) \) -category. The inclusion  \( \mathrm{LCart}(A^{\sharp})\to(\infty,\omega)\text{-cat}_{\mathrm{m}/A^{\sharp}} \)  preserves both colimits and limits.

Proof. The preservation of limits is a consequence of the fact that that this inclusion is a right adjoint. The preservation of colimits is a direct consequence of the theorem 5.2.3.3. \(\square\)

5.2.3.5. We now use the last theorem to provide an alternative explicit expression of the left cartesian fibration  \( Fh_{[C,1]}^{0} \) . We obtain this in the theorem 5.2.3.10.

Proposition 5.2.3.6. Let C be an  \( (0,\omega) \) -category with an atomic and loop free basis. The canonical projection  \( \gamma:1\stackrel{\circ}{\star}C^{\flat}\to[C,1]^{\sharp} \)  is a left cartesian fibration.

Proof. Let C be such  \( (0,\omega) \) -category. The corollary 4.3.3.21, the theorem 4.3.3.5 and the proposition 4.3.3.2 imply that both the domain and the codomain of  \( \gamma \)  are strict. We can then show the result in  \( (0,\omega) \) -cat \( _{m} \) . By construction, the basis of  \( 1\stackrel{\circ}{\star}\lambda C \)  is given by the graduated set:

\[
(B _ {1 \stackrel {\circ} {\star} \lambda C}) _ {n} := \left\{ \begin{array}{l l} \{\emptyset^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {0} \} \cup \{\emptyset^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {0} \} & \text {if n = 0} \\ \{1 ^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {n - 1} \} \cup \{\emptyset^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {n} \} & \text {if n > 0} \end{array} \right.
\]

where \(B_{C}\) is the basis of \(C\). The derivative is induced by:

\[
\partial (1 \stackrel {\circ} {\star} c) := 1 \stackrel {\circ} {\star} \partial c + (- 1) ^ {| c |} \emptyset \otimes c \qquad \partial (\emptyset \star c) := \emptyset \stackrel {\circ} {\star} \partial c
\]

where we set the convention  \( \partial c := 0 \)  if  \( |c| = 0 \) . Let n be an integer and x an element of  \( (1 \stackrel{\circ}{\star} \lambda C)_n \) . The induced morphism  \( D_n \to 1 \stackrel{\circ}{\star} C^\flat \)  is marked if and only if there is no element of shape  \( \emptyset \star c \)  in the support of x.

For an integer \( n > 0 \), we define \( s_n: (\Sigma \lambda C)_n \to (1^{\circ} \star \lambda C)_n \) as the unique group morphism fulfilling

\[
s _ {n} (\Sigma c) := 1 \stackrel {\circ} {\star} c
\]

for \(c\) any element of \(\lambda C_{n - 1}\). Remark that for any non negative integer \(n\), and any element \(d\) of \((1^{\circ} \star \lambda C)_n\), \(s_n(d)\) is contained in \(d\). However, the family of morphism \(\{s_n\}_{n \in \mathbb{N}}\) does not commute with the derivative. Let \(n\) be an integer and \(x\) an element of \((1^{\circ} \star \lambda C)_n\). The induced morphism \(\mathbf{D}_n \to 1^{\circ} \star C^\flat\) is therefore marked if and only if \(x\) is equal to \(s_n \gamma_n(x)\).

Eventually, we recall that  \( (\mathbf{D}_{n})_{t} \otimes [1]^{\sharp} \)  is the colimit of the diagram:

\[
(\mathbf {D} _ {n}) _ {t} \otimes \{0 \} \coprod (\mathbf {D} _ {n}) _ {t} \otimes \{1 \} \longleftarrow \mathbf {D} _ {n} ^ {\flat} \otimes \{0 \} \coprod \mathbf {D} _ {n} ^ {\flat} \otimes \{1 \} \longrightarrow \tau_ {n} ^ {i} (\mathbf {D} _ {n} ^ {\flat} \otimes [ 1 ] ^ {\sharp})
\]

279

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

We then have to show that for any integer $n$, any diagram of shape

$$\begin{array}{c} \lambda \mathbf {D} _ {n} \otimes \{0 \} \cup \lambda \partial \mathbf {D} _ {n} \otimes [ 1 ] \xrightarrow {g} 1 \stackrel {{\circ}} {{\star}} \lambda C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \lambda \mathbf {D} _ {n} \otimes [ 1 ] \xrightarrow [ f ]{} \Sigma \lambda C \end{array}$$

with $f(e_n \otimes [1])$ and $f(e_k^\alpha \otimes [1])$ for $\alpha \in \{-, +\}$ and $k < n$ corresponding to a marked cell, admits a unique lifting $l$ with the following extra condition: if $n > 0$, if $f(e_n \otimes [1])$ is null and if $g(e_n \otimes \{0\})$ corresponds to a marked cell, then $l(e_n \otimes [1])$ is null and $l(e_n \otimes \{1\})$ corresponds to a marked cell.

Suppose first that $n = 0$. We set $l_0: \lambda(\mathbf{D}_0 \otimes [1])_0 \to (1 \stackrel{\circ}{\star} \lambda C)_0$ as the unique group morphism extending $g_0$ and such that

$$l _ {0} (e _ {0} \otimes \{1 \}) := \partial s _ {1} (f _ {1} (e _ {0} \otimes [ 1 ]) + g _ {0} (e _ {0} \otimes \{1 \}).$$

We also define $l_1: \lambda(\mathbf{D}_0 \otimes [1])_1 \to (1 \stackrel{\circ}{\star} \lambda C)_1$ as the group morphism characterized by:

$$l _ {1} (e _ {0} \otimes [ 1 ]) := s _ {1} (f _ {1} (e _ {0} \otimes [ 1 ])).$$

For $k > 1$, we set $l_k: \lambda(\mathbf{D}_0 \otimes [1])_k \to (1 \stackrel{\circ}{\star} \lambda C)_k$ as the constant morphism on 0. We directly deduce the equality $\partial l = l\partial$. We then have defined the desired lifting, which is obviously the unique one possible.

Suppose now that $n > 0$. We set $l_k := g_k: \lambda(\mathbf{D}_n \otimes [1])_k \to (1 \stackrel{\circ}{\star} \lambda C)_k$ for $k < n$ and $l_n: \lambda(\mathbf{D}_n \otimes [1])_n \to (1 \stackrel{\circ}{\star} \lambda C)_n$ as the unique group morphism extending $g_n$ and such that

$$l _ {n} (e _ {n} \otimes \{1 \}) := (- 1) ^ {\alpha} \partial s _ {n + 1} (f (e _ {n} \otimes [ 1 ])) - (- 1) ^ {\alpha} s _ {n} (f ((\partial e _ {n}) \otimes [ 1 ])) + g _ {n} (e _ {n} \otimes \{0 \})$$

where $\alpha$ is $+$ if $n$ is even and $-$ if not. We define $l_{n+1}: \lambda(\mathbf{D}_n \otimes [1])_{n+1} \to (1 \stackrel{\circ}{\star} \lambda C)_{n+1}$ as the group morphism characterized by:

$$l _ {n + 1} (e _ {n} \otimes [ 1 ]) := s _ {n + 1} (f _ {n + 1} (e _ {n} \otimes [ 1 ])).$$

Eventually, for $k > n$, we set $l_k: \lambda(\mathbf{D}_n \otimes [1])_k \to (1 \stackrel{\circ}{\star} \lambda C)_k$ as the constant morphism on 0.

For an integer $k < n$ and $\alpha \in \{-, +\}$, as the $(k + 1)$-cell corresponding to $g_{k + 1}(e_k^\alpha \otimes [1])$ is marked, we have an equality

$$g _ {k + 1} (e _ {k} ^ {\alpha} \otimes [ 1 ]) = s _ {k + 1} f _ {k + 1} (e _ {k} ^ {\alpha} \otimes [ 1 ]).$$

This then implies the equalities

$$\partial (l _ {n + 1} (e _ {n} \otimes [ 1 ])) = l _ {n + 1} (\partial (e _ {n} \otimes [ 1 ]))$$

$$\partial (l _ {n} (e _ {n} \otimes \{1 \})) = g _ {n - 1} (\partial e _ {n} \otimes \{1 \})$$

280

5.2. CARTESIAN FIBRATIONS

As it was the only non trivial case, we have $l\partial = \partial l$. We then have defined the desired lifting, which is obviously the unique one possible. Moreover, if we suppose that $f(e_n \otimes [1])$ is null and $g(e_n \otimes \{0\})$ corresponds to a marked cell, this implies that $s_{n+1}(f(e_n \otimes [1])) = 0$ and that the $g_n(e_n \otimes \{0\})$ is in the image of $s_n$. The object $f(e_n \otimes [1])$ also is in the image of $s_n$ and so corresponds to a marked cell.

**Lemma 5.2.3.7.** *There is a unique morphism $1 \stackrel{\mathrm{co}}{\star} C^{\flat} \to [C, 1]_{0/}^{\sharp}$ fitting in a square*

![img-328.jpeg](img-328.jpeg)

*This morphism is an equivalence whenever $C$ is a globular sum.*

*Proof.* We have by construction a cocartesian square

![img-329.jpeg](img-329.jpeg)

which implies that $1 \to 1 \stackrel{\mathrm{co}}{\star} C^{\flat}$ is initial. This directly implies the first assertion. We now prove the second assertion. We suppose that $C$ is a globular sum $a$. The $(\infty, \omega)$-categories $1 \stackrel{\mathrm{co}}{\star} a^{\flat}$ is strict according to proposition 5.1.3.20. Proposition 5.2.3.6 states that the canonical morphism $1 \stackrel{\mathrm{co}}{\star} a^{\flat} \to [a, 1]^{\sharp}$ is a left cartesian fibration. As the comparison map is initial by left cancellation, this concludes the proof.

**Proposition 5.2.3.8.** *Let $b$ be a globular form and $j : b \to C$ a morphism between $(\infty, \omega)$-categories. The following diagram is cartesian*

![img-330.jpeg](img-330.jpeg)

*Proof.* The lemma 5.2.3.7 implies that the morphism $1 \stackrel{\mathrm{co}}{\star} b^{\flat} \to [b, 1]^{\sharp}$ is equivalent to $\mathbf{F} h_0^{[b,1]}$. We then have to check that the canonical morphism

$$\mathbf{F} h_0^{[b,1]} \coprod_{b^{\flat}} C^{\flat} \to [j, 1]^* \mathbf{F} h_0^{[C,1]} \tag{5.2.3.9}$$

281

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

is an equivalence. According to theorem 5.2.3.3, the two objects are left cartesian fibrations, and we then have to check that this morphism induce equivalences on fibers. Remark furthermore that the two morphisms $\{0\} \rightarrow [b, 1]^{\sharp}$ and $\{1\} \rightarrow [b, 1]^{\sharp}$ are discrete Conduché functors and then exponentiable according to proposition 5.1.1.29. The fibers on 0 and 1 of the morphism (5.2.3.9) then corresponds to the equivalences

$$1 \coprod_{\emptyset} \emptyset \sim 1 \quad \text{and} \quad b \coprod_b C \sim C.$$

**Theorem 5.2.3.10.** *Let $C$ be a $(\infty, \omega)$-category. The left cartesian fibration $\mathbf{F}h^0_{[C,1]}$ is equivalent to the projection $1 \stackrel{co}{\star} C^{\flat} \rightarrow [C, 1]^{\sharp}$.*

*Proof.* Let $i : [b, 1]^{\sharp} \rightarrow [C, 1]^{\sharp}$ be any morphism. The proposition 5.2.3.8 states that the following square is cartesian:

$$\begin{array}{ccc} 1 \stackrel{co}{\star} b^{\flat} \coprod_{b^{\flat}} C^{\flat} & \longrightarrow & [C, 1]_{0/}^{\sharp} \\ \downarrow & & \downarrow \\ [b, 1]^{\sharp} & \longrightarrow & [C, 1]^{\sharp} \end{array}$$

Eventually, remark that we have an equivalence

$$\underset{b \rightarrow C}{\operatorname{colim}}[b, 1] \sim [C, 1].$$

The theorem 5.2.2.12 then induces equivalences

$$[C, 1]_{0/}^{\sharp} \sim \underset{i:b \rightarrow C}{\operatorname{colim}} 1 \stackrel{co}{\star} b^{\flat} \coprod_{b^{\flat}} C^{\flat} \sim 1 \stackrel{co}{\star} C^{\flat} \coprod_{C^{\flat}} C^{\flat} \sim 1 \stackrel{co}{\star} C^{\flat}$$

over $[C, 1]^{\sharp}$. This concludes the proof.

**Corollary 5.2.3.11.** *Let $b$ be a globular form and $j : b \rightarrow C$ any morphism. The following square is cartesian:*

$$\begin{array}{ccc} 1 \stackrel{co}{\star} b \coprod_b C & \longrightarrow & 1 \stackrel{co}{\star} C \\ \downarrow & & \downarrow \\ [b, 1] & \longrightarrow & [C, 1] \end{array}$$

*Proof.* We apply the functor $(\_)^{\sharp}$ to the cartesian square given in proposition 5.2.3.8 and the equivalence given in theorem 5.2.3.10.

**Corollary 5.2.3.12.** *Let $C$ be an $(\infty, \omega)$-category. We denote by $\gamma : C \star 1 \rightarrow [C, 1]$ and $\gamma' : 1 \stackrel{co}{\star} C \rightarrow [C, 1]$ the two canonical projections. The functors $\gamma^* : (\infty, \omega)\text{-cat}_{/[C,1]} \rightarrow (\infty, \omega)\text{-cat}_{/C \star 1}$ and $\gamma^* : (\infty, \omega)\text{-cat}_{/[C,1]} \rightarrow (\infty, \omega)\text{-cat}_{/1 \stackrel{co}{\star} C}$ preserve colimits.*

282

5.2. CARTESIAN FIBRATIONS

Proof. We have a cocartesian square

![img-331.jpeg](img-331.jpeg)

The theorem 5.2.3.10 implies that the right hand morphism is a left cartesian fibration, and $\gamma^b$ is then a classified left cartesian fibration. The result is then a direct consequence of theorem 5.2.2.12. The other assertion follows by duality. □

### 5.2.4 Smooth and proper morphisms

5.2.4.1. For a marked $(\infty, \omega)$-category $C$, we denote by $\mathrm{LCart}(C)$ (resp. $\mathrm{RCart}(C)$) the full sub $(\infty, 1)$-category of $(\infty, \omega)\text{-}\mathrm{cat}_{\mathrm{m}/C}$ whose objects are left cartesian fibrations. We can equivalently define $\mathrm{LCart}(C)$ as the localization of $(\infty, \omega)\text{-}\mathrm{cat}_{\mathrm{m}/C}$ along $\widehat{\mathrm{I}/C}$. For $E, F$ two objects of $\mathrm{LCart}(C)$ corresponding respectively to two left cartesian fibrations $p: X \to C$ and $q: X \to C$, we denote by $\mathrm{Map}(E, F)$ the $(\infty, \omega)$-category fitting in the cocartesian square:

![img-332.jpeg](img-332.jpeg)

5.2.4.2. We recall that a left cartesian fibration $X \to C$ is classified when there exists a cartesian square:

![img-333.jpeg](img-333.jpeg)

We denote by $\mathrm{LCart}^c(C)$ the full sub $(\infty, 1)$-category of $\mathrm{LCart}(C)$ whose objects are classified left cartesian fibrations.

5.2.4.3. Remark that every morphism $f: C \to D$ induces an adjunction

$$f_! : (\infty, \omega)\text{-}\mathrm{cat}_{/C} \xleftarrow{\quad} (\infty, \omega)\text{-}\mathrm{cat}_{/D} : f^*$$

where the left adjoint $f_!$ is the composition and the right one is the pullback. This induces an adjunction at the level of localized $(\infty, 1)$-category:

$$\mathbf{L}f_! : \mathrm{LCart}(C) \xleftarrow{\quad} \mathrm{LCart}(D) : \mathbf{R}f^* = f^*$$

283

CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

**5.2.4.4.** A morphism $f : C \rightarrow D$ is *smooth* if $f^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/D} \rightarrow (\infty, \omega)\text{-cat}_{\mathrm{m}/C}$ preserves colimits, and for every cartesian square of the form

$$\begin{array}{ccc} C'' & \xrightarrow{v'} & C' & \longrightarrow & C \\ \downarrow & \downarrow & \downarrow & \downarrow & \downarrow_f \\ D'' & \xrightarrow{v} & D' & \longrightarrow & D \end{array} \tag{5.2.4.5}$$

if $v$ is initial, so is $v'$. When $f$ is smooth, the functor $f^*$ admits a left adjoint

$$f^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/D} \xleftarrow{\perp} (\infty, \omega)\text{-cat}_{\mathrm{m}/C} : f_*$$

and as $f^*$ preserves initial morphisms, this induces a derived adjunction:

$$\mathbf{L}f^* : \mathrm{LCart}(D) \xleftarrow{\perp} \mathrm{LCart}(C) : \mathbf{R}f_*$$

where $\mathbf{R}f_*$ is just the restriction of $f_*$.

**Proposition 5.2.4.6.** *Let $I, J$ be two marked $(\infty, \omega)$-categories. The projection $I \times J \rightarrow I$ is smooth.*

*Proof.* This is a direct consequence of the fact that cartesian product preserves colimits and initial morphisms. $\square$

**Proposition 5.2.4.7.** *Classified right cartesian fibrations are smooth.*

*Proof.* The theorem 5.2.2.12 states that $f^*$ preserves colimits. Suppose given a diagram of shape (5.2.4.5). As initial morphisms are the smallest cocomplete class containing morphism $I$, and as $f^*$ preserves colimits, one can suppose that $v$ belongs to $I$, and then is a left Gray deformation retract. To conclude, one applies proposition 5.2.1.13. $\square$

**5.2.4.8.** A morphism $f : C \rightarrow D$ is *proper* if $f^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/D} \rightarrow (\infty, \omega)\text{-cat}_{\mathrm{m}/C}$ preserves colimits and for every cartesian square of the form

$$\begin{array}{ccc} C'' & \xrightarrow{v'} & C' & \longrightarrow & C \\ \downarrow & \downarrow & \downarrow & \downarrow & \downarrow_f \\ D'' & \xrightarrow{v} & D' & \longrightarrow & D \end{array} \tag{5.2.4.9}$$

if $v$ is final, so is $v'$. A morphism $f$ is then proper if and only if $f^\circ$ is smooth. Propositions 5.2.4.6 and 5.2.4.7 then imply that projections and classified right cartesian fibrations are proper.

284

5.2. CARTESIAN FIBRATIONS

5.2.4.10. We denote by $\perp : (\infty, \omega)\text{-cat}_{\mathrm{m}} \to (\infty, \omega)\text{-cat}$ the left Kan extension of the functor $t\Theta \to (\infty, \omega)\text{-cat}$ that sends $a^{\flat}$ on $a$ and $(\mathbf{D}_{n+1})_t$ on $\mathbf{D}_n$. Roughly speaking, $\perp$ sends a marked $(\infty, \omega)\text{-category}$ to it's localization by marked cells. By abuse of notation, we also denote $\perp : \operatorname{Arr}((\infty, \omega)\text{-cat}_{\mathrm{m}}) \to (\infty, \omega)\text{-cat}$, the composite functor

$$
\operatorname{Arr}((\infty, \omega)\text{-cat}_{\mathrm{m}}) \xrightarrow{\mathrm{dom}} (\infty, \omega)\text{-cat}_{\mathrm{m}} \xrightarrow{\perp} (\infty, \omega)\text{-cat}
$$

This functor preserves colimits and sends initial and final morphisms to equivalences. For any object $E$ of $\operatorname{LCart}(A)$ and for any morphism $i: A \to B$, we then have a canonical equivalence

$$
\perp \mathbf{L} i_{!} E \sim \perp E. \tag{5.2.4.11}
$$

Let $A$ be an $(\infty, \omega)$-category and $a: 1 \to A^{\sharp}$ an object of $A$. According to proposition 5.2.1.19, the factorisation of $a: 1 \to A^{\sharp}$ in a final morphism followed by a right cartesian fibration is given by the canonical inclusion $\{a\} \to A_{a/}^{\sharp}$ and the canonical projection $\pi_a: A_{a/}^{\sharp} \to A^{\sharp}$. Let $E$ be an object of $\operatorname{LCart}(A^{\sharp})$ corresponding to a left cartesian fibration $p: X \to A^{\sharp}$. We then have a diagram

$$
\begin{array}{ccc}
X_a & \xrightarrow{i} & X_{/a} & \longrightarrow & X \\
\downarrow & \downarrow & \downarrow & \downarrow & \downarrow_p \\
\{a\} & \longrightarrow & A_{a/}^{\sharp} & \xrightarrow{\pi_a} & A^{\sharp}
\end{array}
$$

and the morphism $i$ is final as $p$ is proper. As $\perp$ sends final morphisms to equivalences, we then have an invertible natural transformation:

$$
\mathbf{R} a^* E \sim \perp \mathbf{R} a^* E \sim \perp \mathbf{R} \pi_a^* E \tag{5.2.4.12}
$$

**Proposition 5.2.4.13.** *The functor $\mathbf{R} a^*: \operatorname{LCart}(A^{\sharp}) \to \operatorname{LCart}(1) \sim (\infty, \omega)\text{-cat preserves colimits}$.*

*Proof.* As $\pi_a$ is a right cartesian fibration, it is smooth and $\mathbf{R} \pi_a^*$ then preserves colimits. The functor $\perp$ also preserves them. The result then follows from the equivalence (5.2.4.12).

5.2.4.14. Let $E$ be an object of $(\infty, \omega)\text{-cat}_{\mathrm{m}/A^{\sharp}}$ corresponding to a morphism $X \to A^{\sharp}$. We denote $\tilde{X} \to A^{\sharp}$ the left fibrant replacement of $E$. We then have a diagram

$$
\begin{array}{ccc}
X_{a/} & \longrightarrow & \tilde{X}_{a/} & \longrightarrow & A_{a/}^{\sharp} \\
\downarrow & \downarrow & \downarrow & \downarrow & \downarrow_{\pi_a} \\
X & \longrightarrow & \tilde{X} & \xrightarrow{\mathbf{F}E} & A^{\sharp}
\end{array}
$$

285

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

As \(\pi_{a}\) is smooth, the canonical morphism \(X_{a / }\to \hat{X}_{a / }\) is initial. Combined with (5.2.4.12), this induces an equivalence:

\[
\mathbf {R} a ^ {*} (\mathbf {F} E) \sim \bot X _ {/ a} \tag {5.2.4.15}
\]

Proposition 5.2.4.16. For a morphism \( X \to A^{\sharp} \), and an object \( a \) of \( A \), we denote by \( X_{/a} \) the marked \( (\infty, \omega) \)-category fitting in the following cartesian square:

![img-334.jpeg](img-334.jpeg)

We denote by \(\bot : (\infty, \omega)\)-cat\(_{\mathrm{m}} \to (\infty, \omega)\)-cat the functor sending a marked \((\infty, \omega)\)-category to its localization by marked cells.

(1) Let \( E, F \) be two elements of \( (\infty, \omega) \)-cat\(_{\mathrm{m/A}^{\sharp}}\) corresponding to morphisms \( X \to A^{\sharp} \), \( Y \to A^{\sharp} \), and \( \phi : E \to F \) a morphism between them. The induced morphism \( \mathbf{F}\phi : \mathbf{F}E \to \mathbf{F}F \) is an equivalence if and only if for any object \( a \) of \( A \), the induced morphism

\[
\bot X _ {/ a} \to \bot Y _ {/ a}
\]

is an equivalence of \((\infty, \omega)\)-categories.

(2) A morphism \( X \to A^{\sharp} \) is initial if and only if for any object \( a \) of \( A \), \( \bot X_{/a} \) is the terminal \( (\infty, \omega) \)-category.

Proof. The first assertion is a direct consequence of the equation (5.2.4.15) and of the fact that equivalences between left cartesian fibrations are detected on fibers.

A morphism \( p: X \to A \) is initial if and only if \( \mathbf{F}p \) is equivalent to the identity of \( A^{\sharp} \), and according to the first assertion, if and only if for any object \( a \) of \( A \), the canonical morphism \( \bot X_{a/} \to \bot A_{a/}^{\sharp} \) is an equivalence. However, the canonical morphism \( \{a\} \to A_{/a}^{\sharp} \) is final, and \( \bot A_{a/}^{\sharp} \) is then the terminal \( (\infty, \omega) \)-category. This concludes the proof of the second assertion.

5.2.4.17. Suppose given a commutative square of marked  \( (\infty,\omega) \) -categories:

\[
\begin{array}{c} A \xrightarrow {j} C \\ v \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text { (5.2.4.18) } \\ B ^ {\sharp} \xrightarrow [ i ]{} D ^ {\sharp} \end{array}
\]

286

5.2. CARTESIAN FIBRATIONS

This induces a square

$$\begin{array}{c} \operatorname{LCart}^{c}(C) \xrightarrow{\mathbf{R}j^{*}} \operatorname{LCart}^{c}(A) \\ \downarrow_{\mathbf{L}u} \quad \swarrow \quad \downarrow_{\mathbf{L}v} \\ \operatorname{LCart}(D^{\sharp}) \xrightarrow{\mathbf{R}i^{*}} \operatorname{LCart}(B^{\sharp}) \end{array} \tag{5.2.4.19}$$

that commutes up to a natural transformation

$$\begin{array}{l} \mathbf{L}v_{!} \circ \mathbf{R}j^{*} \rightarrow \mathbf{L}v_{!} \circ \mathbf{R}j^{*} \circ \mathbf{R}u^{*} \circ \mathbf{L}u_{!} \\ \quad \sim \quad \mathbf{L}v_{!} \circ \mathbf{R}v^{*} \circ \mathbf{R}i^{*} \circ \mathbf{L}u_{!} \\ \quad \rightarrow \quad \mathbf{R}i^{*} \circ \mathbf{L}u_{!} \end{array} \tag{5.2.4.20}$$

A square (5.2.4.26) verifies the *Beck-Chevaley condition* if this natural transformation (5.2.4.20) is an equivalence. This square verifies the *weak Beck-Chevaley condition* if the natural transformation once composed with $\perp$ becomes an equivalence.

**Proposition 5.2.4.21.** *If the square (5.2.4.26) is cartesian and $i$ is smooth, then it verifies the Beck-Chevaley condition.*

*Proof.* By construction, $\mathbf{L}v_{!} \circ \mathbf{R}j^{*}$ sends an object $E$ of $\operatorname{LCart}^{c}(C)$ onto the fibrant replacement of $v_{!}j^{*}E$. As $i$ is smooth, $\mathbf{R}i^{*} \circ \mathbf{L}u_{!}$ sends an object $E$ of $\operatorname{LCart}(C)$ onto the fibrant replacement of $i^{*}u_{!}E$. As pullbacks are stable under composition, we have $i^{*}u_{!} \sim v_{!}j^{*}$. $\square$

**Lemma 5.2.4.22.** *A square (5.2.4.26) where both $j$ and $i$ are final verifies the weak Beck-Chevaley condition.*

*Proof.* As $\perp$ sends initial and final morphisms to equivalences, for any $E: \operatorname{LCart}^{c}(A)$ and any $F: \operatorname{LCart}^{c}(C)$, we have equivalences

$$\perp\mathbf{L}v_{!}E \sim \perp E \quad \text{and} \quad \perp\mathbf{L}v_{!}F \sim \perp F.$$

Moreover, as classified left cartesian fibrations are proper, for any $G: \operatorname{LCart}^{c}(C)$ and $H: \operatorname{LCart}(D^{\sharp})$, we have equivalences

$$\perp\mathbf{L}j^{*}G \sim \perp G \quad \text{and} \quad \perp\mathbf{L}i^{*}H \sim \perp H.$$

This implies the result. $\square$

**Lemma 5.2.4.23.** *Suppose given a cartesian square*

$$\begin{array}{c} A \xrightarrow{j} C \\ v \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B^{\sharp} \xrightarrow{i} D^{\sharp} \end{array}$$

287

CHAPTER 5. THE (∞, 1)-CATEGORY OF MARKED (∞, ω)-CATEGORIES

such that for any object b of B♯, the outer square of the induced diagram

$$\begin{array}{ccc} A_{b/} & \xrightarrow{\pi'_b} & A & \xrightarrow{j} & C \\ v' \downarrow & & v \downarrow & & \downarrow^u \\ B_{/b}^\sharp & \xrightarrow{\pi_b} & B^\sharp & \xrightarrow{i} & D^\sharp \end{array}$$

verifies the weak Beck Chevaley condition. Then the right hand square verifies the Beck Chevaley condition.

Proof. Let E be an element of LCart(C). Using the hypothesis, the fact that πₐ is a right cartesian fibration, and so smooth, we have a sequence of equivalences:

$$\begin{array}{rcl} \perp \mathbf{R} \pi_b^* \mathbf{L} v_{!} \mathbf{R} j^* E & \sim & \perp \mathbf{L} v_{!}' \mathbf{R} \pi_b'^* \mathbf{R} j^* E & (5.2.4.21) \\ & \sim & \perp \mathbf{R} \pi_b^* \mathbf{R} i \mathbf{L} u_{!} E & (\text{hypothesis}) \end{array}$$

Using the equivalence (5.2.4.12), this implies that for any element b of B, we have an equivalence

$$\mathbf{R} b^* \mathbf{L} v_{!} \mathbf{R} j^* E \rightarrow \mathbf{R} b^* \mathbf{R} i \mathbf{L} u_{!} E$$

which concludes the proof as equivalences between left cartesian fibrations are detected fiberwise. □

Proposition 5.2.4.24. Let i : I → A♯ and j : C♯ → D♯ be two morphisms. The square

$$\begin{array}{ccc} C^\sharp \times I & \longrightarrow & D^\sharp \times I \\ \downarrow & & \downarrow \\ C^\sharp \times A^\sharp & \longrightarrow & D^\sharp \times A^\sharp \end{array}$$

verifies the Beck-Chevaley condition.

Proof. According to lemma 5.2.4.23, one has to show that for any pair (a, c) where a is an object of A♯ and c of C♯, the induced cartesian square

$$\begin{array}{ccc} C_{c/}^\sharp \times I_{a/} & \longrightarrow & D^\sharp \times I \\ \downarrow & & \downarrow \\ C_{c/}^\sharp \times A_{a/}^\sharp & \longrightarrow & D^\sharp \times A^\sharp \end{array}$$

verifies the weak Beck-Chevaley condition. Remark that this square factors as two cartesian squares:

$$\begin{array}{ccc} C_{c/}^\sharp \times I_{a/} & \longrightarrow & D_{j(c)/}^\sharp \times I_{a/} & \longrightarrow & D^\sharp \times I \\ \downarrow & & \downarrow & & \downarrow \\ C_{c/}^\sharp \times A_{a/}^\sharp & \longrightarrow & D_{j(c)/}^\sharp \times A_{a/}^\sharp & \longrightarrow & D^\sharp \times A^\sharp \end{array}$$

288

5.2. CARTESIAN FIBRATIONS

The two morphisms $\{c\} \to C_{c/}^{\sharp}$ and $\{c\} \to D_{j(c)/}^{\sharp}$ are initial, and by stability by left cancellation, so is $C_{c/}^{\sharp} \to D_{j(c)/}^{\sharp}$. By stability by cartesian product, the two horizontal morphisms of the left square are initial. Lemma 5.2.4.22 then implies that the left square verifies the weak Beck-Chevaley condition. According to proposition 5.2.4.21, the right square fulfills the Beck-Chevaley condition, and so *a fortiori*, the weak one. The outer square then verified the weak Beck-Chevaley condition, which concludes the proof. $\square$

**5.2.4.25.** Suppose given a commutative square of marked $(\infty, \omega)$-categories:

$$
\begin{array}{c}
A \xrightarrow{j} C^{\sharp} \\
v \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(5.2.4.26)} \\
B \xrightarrow{i} D^{\sharp}
\end{array}
$$

where $j$ and $i$ are smooth. This induces a square

$$
\begin{array}{c}
\operatorname{LCart}^{c}(B) \xrightarrow{\mathbf{R} i_{*}} \operatorname{LCart}(D^{\sharp}) \\
\mathbf{L} v^{*} \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(5.2.4.27)} \\
\operatorname{LCart}^{c}(A) \xrightarrow{\mathbf{R} j_{*}} \operatorname{LCart}(C^{\sharp})
\end{array}
$$

that commutes up to a natural transformation

$$
\begin{array}{l}
\mathbf{L} u^{*} \circ \mathbf{R} i_{*} \quad \rightarrow \quad \mathbf{R} j_{*} \circ \mathbf{L} j^{*} \circ \mathbf{L} u^{*} \circ \mathbf{R} i_{*} \\
\quad \sim \quad \mathbf{R} j_{*} \circ \mathbf{L} v^{*} \circ \mathbf{L} i^{*} \circ \mathbf{R} i_{*} \\
\quad \rightarrow \quad \mathbf{R} j_{*} \circ \mathbf{L} v^{*}
\end{array}
\tag{5.2.4.28}
$$

A square (5.2.4.26) verifies the *opposed Beck-Chevaley condition* if $i$ and $j$ are smooth and the natural transformation (5.2.4.28) is an equivalence.

**Proposition 5.2.4.29.** *If the square (5.2.4.28) is cartesian, and $i$ and $j$ are smooth, then it verifies the opposed Beck-Chevaley condition.*

*Proof.* By adjunction, it is sufficient to show that the induced natural transformation

$$
\mathbf{L} v_{!} \circ \mathbf{R} j^{*} \to \mathbf{R} i^{*} \circ \mathbf{L} u_{!}: \operatorname{LCart}(C^{\sharp}) \to \operatorname{LCart}(B)
$$

is an equivalence. By construction, $\mathbf{L} v_{!} \circ \mathbf{R} j^{*}$ sends an object $E$ of $\operatorname{LCart}(C^{\sharp})$ onto the fibrant replacement of $v_{!} j^{*} E$. As $i$ is smooth, $\mathbf{R} i^{*} \circ \mathbf{L} u_{!}$ sends an object $E$ of $\operatorname{LCart}(C^{\sharp})$ onto the fibrant replacement of $i^{*} u_{!} E$. As pullbacks are stable under composition, we have $i^{*} u_{!} \sim v_{!} j^{*}$. $\square$

289

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

Proposition 5.2.4.30. Let \( i: I \to A^{\sharp} \) be a smooth morphism and \( j: C^{\sharp} \to D^{\sharp} \) any morphism. The square

![img-335.jpeg](img-335.jpeg)

verifies the opposed Beck-Chevaley condition.

Proof. As  \( id_{C^{\sharp}} \times i \)  and  \( id_{D^{\sharp}} \times i \)  are pullbacks of i, they are smooth. The result is then follows from proposition 5.2.4.29. □

#### 5.2.5 The W-small  \( (\infty,\omega) \) -category of V-small left cartesian fibrations

5.2.5.1. Let \( I \) be a marked \( (\infty, \omega) \)-category, and \( a \) a globular sum. We recall that the pullback along the canonical projection \( \pi_a: I \times a^\flat \to I \) induces an adjunction

\[
\pi_ {a!} \colon (\infty , \omega) \text {-cat} _ {/ I \times a ^ {\flat}} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat} _ {\mathrm{m} / I}: \pi_ {a} ^ {*}
\]

Lemma 5.2.5.2. Let \(E\) and \(F\) be two objects of \((\infty, \omega)\)-\(\mathrm{cat}_{\mathrm{m}/I}\) and \(\psi: \pi_{[a,1]}^{*}E \to \pi_{[a,1]}^{*}F\) an equivalence. The exists a unique commutative diagram of shape

![img-336.jpeg](img-336.jpeg)

Moreover, the arrow \(\phi\) is an equivalence.

Proof. Unfolding the definition, we have to show the existence and unicity of commutative diagrams of shape

![img-337.jpeg](img-337.jpeg)

where the two vertical morphisms are the projection and where X and Y correspond respectively to the domain of E and F. As  \( \operatorname{dom}\psi \)  is a morphism over  \( I \times [a,1]^{b} \) , we already have a commutative diagram of shape:

![img-338.jpeg](img-338.jpeg)

290

5.2. CARTESIAN FIBRATIONS

By the universal property of cartesian product, this directly implies that if a square of shape (5.2.5.3) exists, it has to be unique, and that the morphism $\phi$ will be an equivalence. It then remains to show the existence.

Let $\psi'$ be an inverse of $\psi$. We denote $\tilde{\psi}: X \times [a, 1]^b \to Y$ and $\tilde{\psi}': Y \times [a, 1]^b \to X$ the morphisms induce by the adjunction from $\psi$ and $\psi'$. For $\epsilon \in \{0, 1\}$, we denote by $\psi_\epsilon: X \times \{\epsilon\} \to Y$ and $\psi'_\epsilon: Y \times \{\epsilon\} \to X$ the induced morphisms. In particular $\psi_\epsilon$ and $\psi'_\epsilon$ are inverse one of the other.

By construction, we have a commutative diagram

$$\begin{array}{c} X \times [a, 1]^b \times [a, 1]^b \xrightarrow{\tilde{\psi} \times [a, 1]^b} Y \times [a, 1]^b \\ X \times \nabla \Bigg\uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \times [a, 1]^b \xrightarrow[\pi]{\quad} X \end{array}$$

where $\nabla$ is the diagonal and $\psi$ the canonical projection. This corresponds to a commutative diagram in the $(\infty, 1)$-category $[n] \mapsto \operatorname{Hom}(X \times [a, n]^b, X)$:

$$\begin{array}{c} i d_X \xrightarrow{\psi'_0 * \tilde{\psi}} i d_X \\ \tilde{\psi}' * \psi_0 \Big\downarrow \quad \searrow i d_{i d_X} \quad \Big\downarrow \tilde{\psi}' * \psi_1 \\ i d_X \xrightarrow{\psi'_1 * \tilde{\psi}} i d_X \end{array}$$

Remark that in the $(\infty, 1)$-category $[n] \mapsto \operatorname{Hom}(X \times [a, n]^b, Y)$, we have equivalences

$$\tilde{\psi} \sim \psi'_0 * \psi_0 * \psi \quad \text{and} \quad \tilde{\psi} \sim \psi'_1 * \psi_1 * \psi$$

and the previous diagram then induces two commutative triangles

$$\begin{array}{c} \psi_1 \\ \psi_1 * \tilde{\psi}' * \psi_0 \Big\downarrow \quad \searrow i d_{\psi_1} \\ \psi_0 \xrightarrow{\tilde{\psi}} \psi_1 \end{array}$$

$$\begin{array}{c} \psi_0 \xrightarrow{\tilde{\psi}} \psi_1 \\ \searrow i d_{\psi_0} \quad \Big\downarrow \psi_0 * \tilde{\psi}' * \psi_1 \\ \psi_0 \end{array}$$

View as a 1-cell of $[n] \mapsto \operatorname{Hom}(X \times [a, n]^b, Y)$, $\tilde{\psi}$ is then an equivalence. This implies the existence of a lifts in the following diagram

$$\begin{array}{c} [a, 1]^b \xrightarrow{\tilde{\psi}} \underline{\operatorname{Hom}}(X, Y) \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ 1 \end{array}$$

291

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

which induces the wanted square:

![img-339.jpeg](img-339.jpeg)

Lemma 5.2.5.4. Let \( I \) be a marked \( (\infty, \omega) \)-category and a globular form. The canonical morphisms of \( \infty \)-groupoids:

\[
\pi_ {[ a, 1 ]} ^ {*}: \tau_ {0} (\infty , \omega) \text {-cat} _ {\mathrm{m} / I} \to \tau_ {0} (\infty , \omega) \text {-cat} _ {\mathrm{m} / I \times [ a, 1 ] ^ {\flat}}
\]

\[
\pi_ {[ a, 1 ]} ^ {*}: \tau_ {0} \operatorname{Arr} ((\infty , \omega) \text {-cat} _ {\mathrm{m} / I}) \to \tau_ {0} \operatorname{Arr} ((\infty , \omega) \text {-cat} _ {\mathrm{m} / I \times [ a, 1 ] ^ {\flat}})
\]

are fully faithful.

Proof. Let \( E \) and \( F \) be two objects of \( (\infty, \omega) \)-cat\(_{\mathrm{m}/I}\). The morphism

\[
\mathrm{Hom} _ {\tau_ {0} (\infty , \omega) \text {-cat} _ {\mathrm{m} / I}} (E, F) \to \mathrm{Hom} _ {\tau_ {0} (\infty , \omega) \text {-cat} _ {\mathrm{m} / I \times [ a, 1 ] ^ {\flat}}} (\pi_ {[ a, 1 ]} ^ {*} E, \pi_ {[ a, 1 ]} ^ {*} F)
\]

has an inverse that sends \(\psi : \pi_{[a,1]}^{*}E \to \pi_{[a,1]}^{*}F\) onto the morphism \(\phi : E \to F\) appearing in the commutative square provided by lemma 5.2.5.2.

The second assertion is demonstrated similarly.

Proposition 5.2.5.5. Let \( I \) be a marked \( (\infty, \omega) \)-category and a globular form. We denote by \( \pi_a : I \times a^\flat \to I \) the canonical projection. The canonical morphisms of \( \infty \)-groupoids:

\[
\mathbf {R} \pi_ {a} ^ {*}: \tau_ {0} \mathrm{LCart} ^ {c} (I) \to \tau_ {0} \mathrm{LCart} ^ {c} (I \times a ^ {\flat})
\]

\[
\mathbf {R} \pi_ {a} ^ {*}: \tau_ {0} \operatorname{Arr} (\mathrm{LCart} ^ {c} (I)) \to \tau_ {0} \operatorname{Arr} (\mathrm{LCart} ^ {c} (I \times a ^ {\flat}))
\]

are fully faithful.

Proof. Let  \( [b, n] := a \) . Considere first the adjunction:

\[
\begin{array}{c} \operatorname{LCart} ^ {c} (I \times [ b _ {0}, 1 ] ^ {\flat}) \times_ {\operatorname{LCart} ^ {c} (I)} \dots \times_ {\operatorname{LCart} ^ {c} (I)} \operatorname{LCart} ^ {c} (I \times [ b _ {n - 1}, 1 ] ^ {\flat}) \\ \Big \uparrow \vdash \Big \downarrow \operatorname{colim} _ {I} \\ \operatorname{LCart} ^ {c} (I ^ {\flat} \times [ \mathbf {b}, n ]) \end{array}
\]

The corollary 5.2.2.13 implies that the counit of this adjunction is an equivalence. This implies that the right adjoint

\[
\operatorname{LCart} ^ {c} (I ^ {\flat} \times [ \mathbf {b}, n ]) \to \operatorname{LCart} ^ {c} (I \times [ b _ {0}, 1 ] ^ {\flat}) \times_ {\operatorname{LCart} ^ {c} (I)} \dots \times_ {\operatorname{LCart} ^ {c} (I)} \operatorname{LCart} ^ {c} (I \times [ b _ {n - 1}, 1 ] ^ {\flat})
\]

292

5.2. CARTESIAN FIBRATIONS

is fully faithful. By right cancellation and using the fact that fully faithful functors are stable by limits, it is sufficient to show that for any $k < n$,

$$\mathbf{R}\pi_{[b_k,1]}^*: \tau_0\mathrm{LCart}^c(I) \to \tau_0\mathrm{LCart}^c(I \times [b_k,1]^b)$$

is fully faithful. Moreover, for any such $k$, we have a commutative square

$$\begin{array}{ccc} \tau_0\mathrm{LCart}^c(I) & \xrightarrow{\mathbf{R}\pi_{[b_k,1]}^*} & \tau_0\mathrm{LCart}^c(I \times [b_k,1]^b) \\ \downarrow & & \downarrow \\ \tau_0(\infty,\omega)\text{-}\mathrm{cat}_{\mathrm{m}/I} & \xrightarrow{\pi_{[b_k,1]}^*} & \tau_0(\infty,\omega)\text{-}\mathrm{cat}_{\mathrm{m}/I \times [b_k,1]^b} \end{array}$$

whose vertical morphisms are fully faithful by construction. The results the follows from lemma 5.2.5.4 by right cancellation.

The second assertion is demonstrated similarly.

5.2.5.6. For an $(\infty,\omega)$-category $A$ and a globular sum $a$, we define $\mathrm{LCart}(A^\sharp; a)$ as the full sub $(\infty,1)$-category of $\mathrm{LCart}^c(A^\sharp \times a^b)$ whose objects are of shape $E \times id_a^b$ for $E$ an object of $\mathrm{LCart}(A^\sharp)$. The proposition 5.2.5.5 implies that the canonical morphism

$$\tau_0\mathrm{LCart}(A^\sharp) \to \tau_0\mathrm{LCart}(A^\sharp; a)$$

is an equivalence of $\infty$-groupoid. We define $\underline{\mathrm{LCart}}(A^\sharp)$ as the $\mathbf{W}$-small $(\infty,\omega)$-category whose value on $[a,n]$ is given by:

$$\underline{\mathrm{LCart}}(A^\sharp)([a,n]) := \mathrm{Hom}([n], \mathrm{LCart}(A^\sharp; a)).$$

For a marked $(\infty,\omega)$-category $I$ and a globular sum $a$, we define similarly $\mathrm{LCart}^c(I; a)$ as the full sub $(\infty,1)$-category of $\mathrm{LCart}^c(I \times a^b)$ whose objects are of shape $E \times id_a^b$ for $E$ an object of $\mathrm{LCart}^c(I)$. The proposition 5.2.5.5 implies that the canonical morphism

$$\tau_0\mathrm{LCart}^c(I) \to \tau_0\mathrm{LCart}^c(I; a)$$

is an equivalence of $\infty$-groupoid. We define $\underline{\mathrm{LCart}}^c(I)$ as the $\mathbf{W}$-small $(\infty,\omega)$-category whose value on $[a,n]$ is given by:

$$\underline{\mathrm{LCart}}^c(I)([a,n]) := \mathrm{Hom}([n], \mathrm{LCart}^c(I; a)).$$

These two definitions are compatible as we have an equivalence between $\underline{\mathrm{LCart}}^c(A^\sharp)$ and $\underline{\mathrm{LCart}}(A^\sharp)$.

293

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

5.2.5.7. Let E and F be two objects of  \( \underline{\mathrm{LCart}}^{c}(I) \) , and a a globular sum. Remark that a morphism  \( [a,1]\to\underline{\mathrm{LCart}}^{c}(I) \)  corresponds to a morphism  \( E\times id_{a}\to F\times id_{a} \) , and so to a morphism  \( X\times a\to Y \)  over I where X and Y are respectively the domain of E and F. We then have an equivalence:

\[
\hom_ {\underline {{\mathrm{LCart}}} (I)} (E, F) \sim \operatorname{Map} _ {I} (E, F). \tag {5.2.5.8}
\]

This then implies that  \( \mathrm{LCart}^{c}(I) \)  is locally V-small.

5.2.5.9. Let  \( i: I \to J \)  be a morphism between marked  \( (\infty, \omega) \) -category, a a globular sum, and p a classified left cartesian fibration over  \( a^{\flat} \times J \) . Remark that we have a canonical equivalence

\[
\mathbf {R} (i \times i d _ {a ^ {\flat}}) ^ {*} (p \times i d _ {a ^ {\flat}}) \sim (\mathbf {R} i ^ {*} p) \times i d _ {a ^ {\flat}}
\]

natural in \(a:\Theta^{op}\). The functor \(\mathbf{R}(i\times id_{a^{\flat}})^*\) then restricts to a functor

\[
(i _ {a}) ^ {*}: \mathrm{LCart} ^ {c} (J; a) \to \mathrm{LCart} ^ {c} (I; a)
\]

natural in  \( a : \Theta^{op} \) , and then to a morphism of  \( (\infty, \omega) \) -categories:

\[
i ^ {*}: \underline {{\mathrm{LCart}}} ^ {c} (J) \rightarrow \underline {{\mathrm{LCart}}} ^ {c} (I) \tag {5.2.5.10}
\]

5.2.5.11. Let  \( i: I \to A^{\sharp} \)  be a morphism between marked  \( (\infty, \omega) \) -categories. We are now willing to construct a morphism  \( i_{!}: \underline{\mathrm{LCart}}^{c}(I) \to \underline{\mathrm{LCart}}(A^{\sharp}) \)  which corresponds to  \( \mathbf{L}i_{!}: \mathrm{LCart}^{c}(I) \to \mathrm{LCart}(A^{\sharp}) \)  on the maximal sub  \( (\infty, 1) \) -category.

We denote by  \( E_{0} \)  and  \( E_{1} \)  the  \( (\infty,1) \) -categories fitting in the cartesian square:

![img-340.jpeg](img-340.jpeg)

![img-341.jpeg](img-341.jpeg)

where  \( \operatorname{Arr}^{fib}((\infty,\omega)\text{-cat}_{\mathrm{m}}) \)  is the full sub  \( (\infty,1) \) -category of  \( \operatorname{Arr}((\infty,\omega)\text{-cat}_{\mathrm{m}}) \)  whose objects are classified left cartesian fibrations, and where  \( \psi_{0} \)  and  \( \psi_{1} \)  send respectively a on  \( I\times a^{\flat} \)  and  \( A^{\sharp}\times a^{\flat} \) . The morphism i induces an adjunction

\[
i _ {!}: E _ {0} \xrightarrow [ \leftarrow ]{\perp} E _ {1}: i ^ {*} \tag {5.2.5.12}
\]

where the left adjoint sends a left cartesian fibration p over  \( I \times a^{\flat} \)  to  \( \mathbf{L}(i \times id_{a})_{!}p \)  and the right adjoint sends a left cartesian fibration q over  \( A^{\sharp} \times a^{\flat} \)  to  \( \mathbf{R}(i \times id_{a})^{*}q \) .

294

5.2. CARTESIAN FIBRATIONS

Lemma 5.2.5.13. Let p be a left cartesian fibration over I². We have an equivalence

$$\mathbf{L}(i \times id_{a^b})_!(p \times id_{a^b}) \sim (\mathbf{L}i_!p) \times id_{a^b}.$$

Let q be a left cartesian fibration over A². We have an equivalence

$$\mathbf{R}(i \times id_{a^b})^*(q \times id_{a^b}) \sim (\mathbf{R}i^*q) \times id_{a^b}.$$

Proof. The first assertion is straightforward as the cartesian product with aᵇ preserves initial morphisms and left cartesian fibrations. The second assertion is obvious. □

We define $\tilde{E}_0$ and $\tilde{E}_1$ as the full sub $(\infty, 1)$-categories of $E_0$ and $E_1$ whose objects are respectively of shape $p \times id_a$ and $q \times id_a$ for p and q classified left cartesian fibrations over I and A². The last lemma implies that (5.2.5.12) restricts to an adjunction

$$i_! : \tilde{E}_0 \xrightarrow{\perp} \tilde{E}_1 : i^* \tag{5.2.5.14}$$

# Lemma 5.2.5.15.

(1) Let $q \to q'$ be a morphism in $\tilde{E}_0$ corresponding to a cartesian square. The induced morphism $i_!(q) \to i_!(q')$ also corresponds to a cartesian square.
(2) Let $q \to q'$ be a morphism in $\tilde{E}_1$ corresponding to a cartesian square. The induced morphism $i^*(q) \to i^*(q')$ also corresponds to a cartesian square.

Proof. Cartesian morphisms in $\tilde{E}_0$ corresponds to cartesian squares

$$\begin{array}{c} X \times a^b \longrightarrow X \times b^b \\ \downarrow_{p \times id_a} \qquad \qquad \qquad \qquad \downarrow_{p \times id_b} \\ I \times a^b \longrightarrow I \times b^b \end{array}$$

and cartesian morphisms in $\tilde{E}_1$ corresponds to cartesian squares

$$\begin{array}{c} Y \times a^b \longrightarrow Y \times b^b \\ \downarrow_{q \times id_a} \qquad \qquad \qquad \qquad \downarrow_{q \times id_b} \\ A^\sharp \times a^b \longrightarrow A^\sharp \times b^b \end{array}$$

The results directly follows from lemma 5.2.5.13. □

The canonical projection $\tilde{E}_0 \to \Theta$ and $\tilde{E}_1 \to \Theta$ are Grothendieck fibrations in $(\infty, 1)$-categories. The cartesian lifting is given by cartesian squares. Moreover, their Grothendieck deconstructions correspond respectively to $a \mapsto \mathrm{LCart}^c(I; a)$ and $a \mapsto$

295

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

LCart(A\( ^{\sharp} \); b). As both \( i_{!} \) and \( i^{*} \) preserve cartesian lifting according to lemma 5.2.5.15, they induce by Grothendieck deconstruction a family of adjunction

\[
(i _ {a}) _ {!}: \operatorname{LCart} ^ {c} (I; a) \xrightarrow [ \leftarrow ]{\perp} \operatorname{LCart} \left(A ^ {\sharp}; a\right): \left(i _ {a}\right) ^ {*} \tag {5.2.5.16}
\]

natural in \(a:\Theta^{op}\). The family of functors \((i_a)_!\) then induces a morphism of \((\infty ,\omega)\)-category

\[
i _ {!}: \underline {{\mathrm{LCart}}} ^ {c} (I) \rightarrow \underline {{\mathrm{LCart}}} (A ^ {\sharp}) \tag {5.2.5.17}
\]

which corresponds to  \( \mathbf{L}i_{!}:\mathrm{LCart}^{c}(I)\to\mathrm{LCart}(A^{\sharp}) \)  on the maximal sub  \( (\infty,1) \) -category. The unit and counit of adjunction (5.2.5.16) induce morphisms

\[
\mu : i d \rightarrow i ^ {*} i _ {!} \quad \epsilon : i _ {!} i ^ {*} \rightarrow i d \tag {5.2.5.18}
\]

and equivalences \((\epsilon \circ_0 i_!) \circ_1 (i_! \circ_0 \mu) \sim id_{i_!}\) and \((i^* \circ_0 \epsilon) \circ_1 (\mu \circ_0 i^*) \sim id_{i^*}\).

5.2.5.19. Let \( j: C^{\sharp} \to D^{\sharp} \) be a morphism between \( (\infty, \omega) \)-categories. We claim that the commutative square

\[
\begin{array}{c} \underline {{\mathrm{LCart}}} (D ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(i d _ {D ^ {\sharp}} \times i) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (D ^ {\sharp} \times I) \\ (j \times i d _ {A ^ {\sharp}}) ^ {*} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (j \times i d _ {I}) ^ {*} \\ \underline {{\mathrm{LCart}}} (C ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(i d _ {C ^ {\sharp}} \times i) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (C ^ {\sharp} \times I) \end{array}
\]

induces a commutative square

\[
\begin{array}{c} \underline {{\mathrm{LCart}}} ^ {c} (D ^ {\sharp} \times I) \xrightarrow {(j \times i d _ {I}) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (C ^ {\sharp} \times I) \\ (i d _ {D ^ {\sharp}} \times i)! \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (i d _ {C ^ {\sharp}} \times i)! \\ \underline {{\mathrm{LCart}}} (D ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(j \times i d _ {A ^ {\sharp}}) ^ {*}} \underline {{\mathrm{LCart}}} (C ^ {\sharp} \times A ^ {\sharp}) \end{array} \tag {5.2.5.20}
\]

A priori, the natural transformations (5.2.5.18) implies that this square commutes up the natural transformation:

\[
\begin{array}{l} (i d _ {C ^ {\sharp}} \times i) _ {!} \circ (j \times i d _ {I}) ^ {*} \rightarrow (i d _ {C ^ {\sharp}} \times i) _ {!} \circ (j \times i d _ {I}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {!} \\ \sim \quad (i d _ {C ^ {\sharp}} \times i) _ {!} \circ (i d _ {C ^ {\sharp}} \times i) ^ {*} \circ (j \times i d _ {A ^ {\sharp}}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {!} \\ \rightarrow (j \times i d _ {A ^ {\sharp}}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i)! \\ \end{array}
\]

Proposition 5.2.4.24 implies that this natural transformation is pointwise an equivalence, and so is globally an equivalence.

296

5.2. CARTESIAN FIBRATIONS

5.2.5.21. We now suppose that the morphism $i : I \to A^{\sharp}$ is smooth, and we are willing to construct a morphism $i_* : \underline{\mathrm{LCart}}(A^{\sharp}) \to \underline{\mathrm{LCart}}(I)$ which corresponds to $\mathbf{R}i_* : \mathrm{LCart}^c(I) \to \mathrm{LCart}(A^{\sharp})$ on the sub maximal $(\infty, 1)$-categories..

As smooth morphisms are stable by pullback, the maps $i \times id_b^b$ are smooth for any $b : \Theta$. The morphism $i^* : E_0 \to E_1$ then preserves colimits and fits into an adjunction

$$ i^* : E_1 \underset{\perp}{\overset{\longrightarrow}{\longleftarrow}} E_0 : i_* \tag{5.2.5.22} $$

where the left adjoint sends a left cartesian fibration $p$ over $A^{\sharp} \times a^{\flat}$ to $(i \times id_a)^*p$ and the right adjoint sends a left cartesian fibration $q$ over $I \times a^{\flat}$ to $\mathbf{R}(i \times id_a)_*q$.

Lemma 5.2.5.23. Let $p$ be a left cartesian fibration over $I$. We have an equivalence

$$ \mathbf{R}(i \times id_{a^{\flat}})_*(p \times id_{a^{\flat}}) \sim (\mathbf{R}i_*p) \times id_{a^{\flat}}. $$

Proof. The morphism $p \times id_{a^{\flat}}$ is the limit of the cospan

$$ p \to id_I \leftarrow id_I \times id_{a^{\flat}} $$

The result is then a direct consequence of the fact that $\mathbf{R}i_*$ preserves limits as it is a right adjoint.

We recall that $\tilde{E}_0$ and $\tilde{E}_1$ are defined as the full sub $(\infty, 1)$-categories of $E_0$ and $E_1$ whose objects are respectively of shape $p \times id_a$ and $q \times id_a$ for $p$ and $q$ classified left cartesian fibrations over $I$ and $A^{\sharp}$. The lemma 5.2.5.23 and the second assertion of lemma 5.2.5.13 imply that (5.2.5.22) restricts to an adjunction

$$ i^* : \tilde{E}_1 \underset{\perp}{\overset{\longrightarrow}{\longleftarrow}} \tilde{E}_0 : i_* \tag{5.2.5.24} $$

Lemma 5.2.5.25. Let $q \to q'$ be a morphism in $\tilde{E}_0$ corresponding to a cartesian square. The induced morphism $i_*(q) \to i_*(q')$ also corresponds to a cartesian square.

Proof. The proof is similar to that of the lemma 5.2.5.15, using lemma 5.2.5.23 instead of lemma 5.2.5.13.

The lemmas 5.2.5.15 and 5.2.5.25 imply that the two adjoints of (5.2.5.24) preserve the cartesian cells of the Grothendieck fibrations $\tilde{E}_0 \to \Theta$ and $\tilde{E}_1 \to \Theta$. These two adjoints then induce by Grothendieck deconstruction a family of adjunction

$$ (i_a)^* : \mathrm{LCart}(A^{\sharp}; a) \underset{\perp}{\overset{\longrightarrow}{\longleftarrow}} \mathrm{LCart}^c(I; a) : (i_a)_* \tag{5.2.5.26} $$

natural in $a : \Theta^{op}$. The family of functors $(i_a)_*$ then induces a morphism of $(\infty, \omega)$-categories

$$ i_* : \underline{\mathrm{LCart}}^c(I) \to \underline{\mathrm{LCart}}(A^{\sharp}) \tag{5.2.5.27} $$

297

CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

which is equivalent to \(\mathbf{R}i_{*}:\mathrm{LCart}^{c}(I)\to \mathrm{LCart}(A^{\sharp})\) on the sub maximal \((\infty ,1)\)-categories. The unit and counit of adjunction (5.2.5.26) induce natural transformation

\[
\mu : i d \rightarrow i _ {*} i ^ {*} \quad \epsilon : i ^ {*} i _ {*} \rightarrow i d \tag {5.2.5.28}
\]

and equivalences \((\epsilon \circ_0 i^*) \circ_1 (i^* \circ_0 \mu) \sim id_{i^*}\) and \((i_* \circ_0 \epsilon) \circ_1 (\mu \circ_0 i_*) \sim id_{i_*}\).

5.2.5.29. Let \( j: C^{\sharp} \to D^{\sharp} \) be a morphism between \( (\infty, \omega) \)-categories. We claim that the commutative square

\[
\begin{array}{c} \underline {{\mathrm{LCart}}} (D ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(i d _ {D ^ {\sharp}} \times i) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (D ^ {\sharp} \times I) \\ (j \times i d _ {A ^ {\sharp}}) ^ {*} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (j \times i d _ {I}) ^ {*} \\ \underline {{\mathrm{LCart}}} (C ^ {\sharp} \times A ^ {\sharp}) \xrightarrow {(i d _ {C ^ {\sharp}} \times i) ^ {*}} \underline {{\mathrm{LCart}}} ^ {c} (C ^ {\sharp} \times I) \end{array}
\]

induces a commutative square

\[
\begin{array}{c} \underline {{\mathrm{LCart}}} ^ {c} (D ^ {\sharp} \times I) \xrightarrow {(i d _ {D ^ {\sharp}} \times i) _ {*}} \underline {{\mathrm{LCart}}} (D ^ {\sharp} \times A ^ {\sharp}) \\ (j \times i d _ {I}) ^ {*} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (j \times i d _ {A ^ {\sharp}}) ^ {*} \\ \underline {{\mathrm{LCart}}} ^ {c} (C ^ {\sharp} \times I) \xrightarrow {(i d _ {C ^ {\sharp}} \times i) _ {*}} \underline {{\mathrm{LCart}}} (C ^ {\sharp} \times A ^ {\sharp}) \end{array} \tag {5.2.5.30}
\]

A priori, the natural transformations (5.2.5.28) implies that this square commutes up the natural transformation:

\[
\begin{array}{l} (j \times i d _ {A ^ {\sharp}}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {*} \rightarrow (i d _ {C ^ {\sharp}} \times i) _ {*} \circ (i d _ {C ^ {\sharp}} \times i) ^ {*} \circ (j \times i d _ {A ^ {\sharp}}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {*} \\ \sim \quad (i d _ {C ^ {\sharp}} \times i) _ {*} \circ (j \times i d _ {I}) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) ^ {*} \circ (i d _ {D ^ {\sharp}} \times i) _ {*} \\ \rightarrow \quad (i d _ {C ^ {\sharp}} \times i) _ {*} \circ (j \times i d _ {I}) ^ {*} \\ \end{array}
\]

Proposition 5.2.4.30 implies that this natural transformation is pointwise an equivalence, and so is globally an equivalence.

298

# Chapter 6

## The $(\infty, \omega)$-category of small $(\infty, \omega)$-categories

### Contents

|  **6.1** | **Univalence** | **302**  |
| --- | --- | --- |
|  6.1.1 | Internal category | 302  |
|  6.1.2 | Grothendieck construction | 310  |
|  6.1.3 | Univalence | 320  |
|  6.1.4 | $(\infty, \omega)$-Functorial Grothendieck construction | 330  |
|  **6.2** | **Yoneda lemma and applications** | **336**  |
|  6.2.1 | Yoneda lemma | 336  |
|  6.2.2 | Adjoint functors | 343  |
|  6.2.3 | Lax colimits | 349  |
|  6.2.4 | Kan extensions | 360  |

This chapter aims to establish analogs of the fundamental categorical constructions to the $(\infty, \omega)$ case. In the first section, we define the $(\infty, \omega)$-category of small $(\infty, \omega)$-categories $\underline{\omega}$ (paragraph 6.1.1.15), and we prove a first incarnation of the Grothendieck construction:

**Corollary 6.1.2.21.** *Let $\underline{\omega}$ be the $(\infty, \omega)$-category of small $(\infty, \omega)$-categories, and $A$ an*

299

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

\((\infty ,\omega)\) -category. There is an equivalence

\[
\int_ {A}: \mathrm{Hom} (A, \underline {{\omega}}) \to \tau_ {0} \mathrm{LCart} (A ^ {\sharp}).
\]

where \(\tau_0\mathrm{LCart}(A^\sharp)\) is the \(\infty\)-groupoid of left cartesian fibrations over \(A^\sharp\) with small fibers.

Given a functor \( f: A \to \underline{\omega} \), the left cartesian fibration \( \int_A f \) is a colimit (computed in \( (\infty, \omega) \)-cat\(_{\mathrm{m}/A^{\sharp}}\)) of a simplicial object whose value on \( n \) is of shape

\[
\coprod_ {x _ {0}, \dots , x _ {n}: A _ {0}} X (x _ {0}) ^ {\flat} \times \hom_ {A} (x _ {0}, \dots , x _ {n}) ^ {\flat} \times A _ {x _ {n /}} ^ {\sharp} \to A ^ {\sharp}
\]

This formula is similar to the one given in [GHN] for \((\infty, 1)\)-categories, and to the one given in [War11] for strict \(\omega\)-categories.

We also prove a univalence result:

Corollary 6.1.3.31. Let \( I \) be a marked \( (\infty, \omega) \)-category. We denote by \( I^{\sharp} \) the marked \( (\infty, \omega) \)-category obtained from \( I \) by marking all cells and \( \iota : I \to I^{\sharp} \) the induced morphism. There is a natural correspondence between

(1) functors \(f:I\otimes [1]^{\sharp}\to \underline{\omega}^{\sharp},\)
(2) pairs of small left cartesian fibration \(X \to I^{\sharp}\), \(Y \to I^{\sharp}\) together with diagrams

![img-342.jpeg](img-342.jpeg)

Recall that if \( I \) is of shape \( B^{\sharp} \), then the underlying \( (\infty, \omega) \)-category of \( B^{\sharp} \otimes [1]^{\sharp} \) is \( B \times [1] \), and if \( I \) is of shape \( B^{\flat} \), the underlying \( (\infty, \omega) \)-category of \( B^{\flat} \otimes [1]^{\sharp} \) is \( B \otimes [1] \). On the other hand, if \( I \) is \( B^{\sharp} \), \( \iota \) is the identity, and \( \phi \) then preserves all cartesian liftings, and if \( I \) is \( B^{\flat} \), \( \phi \) doesn't need to preserve cartesian liftings.

By varying the marking, we can continuously move from the cartesian product with the interval to the Gray product with the interval on one side, and on the other side, we can continuously move from morphisms between left cartesian fibrations that preserve the marking to the ones that do not preserve it a priori.

Eventually, we also get an \((\infty, \omega)\)-functorial Grothendieck construction, expressed by the following corollary:

300

**Corollary 6.1.4.3.** *Let $A$ be a $\mathbf{U}$-small $(\infty, \omega)$-category. Let $\underline{\mathrm{LCart}}(A^{\sharp})$ be the $(\infty, \omega)$-category of small left cartesian fibrations over $A^{\sharp}$. There is an equivalence*

$$\underline{\mathrm{Hom}}(A, \underline{\omega}) \sim \underline{\mathrm{LCart}}(A^{\sharp})$$

*natural in $A$.*

In the second section of this chapter, for a locally small $(\infty, \omega)$-category $C$, we construct the Yoneda embedding, which is a functor $y : C \to \widehat{C}$ where $\widehat{C} := \underline{\mathrm{Hom}}(C^t, \underline{\omega})$. We prove the Yoneda lemma:

**Theorem 6.2.1.16.** *The Yoneda embedding is fully faithful.*

**Theorem 6.2.1.18.** *Let $C$ be an $(\infty, \omega)$-category. There is an equivalence between the functor*

$$\mathrm{hom}_{\widehat{C}}(y_\_, \_) : C^t \times \widehat{C} \to \underline{\omega}$$

*and the functor*

$$ev : C^t \times \widehat{C} \to \underline{\omega}.$$

In the last three sections, we use these results to study and demonstrate the basic properties of adjunctions, lax (co)limits, and left Kan extensions.

We begin by studying adjunctions, and we establish the following expected result.

**Theorem 6.2.2.9.** *Let $u : C \to D$ and $v : D \to C$ be two functors between locally $\mathbf{U}$-small $(\infty, \omega)$-categories. The two following are equivalent.*

(1) The pair $(u, v)$ admits an adjoint structure.
(2) Their exists a pair of natural transformations $\mu : id_C \to vu$ and $\epsilon : uv \to id_D$ together with equivalences $(\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u$ and $(v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v$.

In the next subsection, given a morphism $f : I \to C^{\sharp}$ between marked $(\infty, \omega)$-categories, we define the notion of lax colimit and lax limit for the functor $f$. If $f$ admits such a lax colimit, for any 1-cell $i : a \to b$ in $I$, we have a triangle

![img-343.jpeg](img-343.jpeg)

If $i$ is marked, the preceding 2-cell is an equivalence. For any 2-cell $u : i \to j$, we have a diagram

![img-344.jpeg](img-344.jpeg)

301

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

If $u$ is marked, the 3-cell is an equivalence. We can continue these diagrams in higher dimensions and we have similar assertions for lax limits. The marking therefore allows us to play on the "lax character" of the universal property that the lax colimit must verify.

After providing several characterizations of lax colimits and limits, we prove the following result:

**Theorem 6.2.3.24.** *Let $C$ be a $\mathbf{U}$-small $(\infty, \omega)$-category. Let $f$ be an object of $\widehat{C}$. We define $C_{/f}^{\sharp}$ as the following pullback*

![img-345.jpeg](img-345.jpeg)

*The colimit of the functor $\pi : C_{/f}^{\sharp} \to C^{\sharp} \xrightarrow{y^{\sharp}} \widehat{C}^{\sharp}$ is $f$.*

We conclude this chapter by studying Kan extensions.

**Cardinality hypothesis.** We fix during this chapter three Grothendieck universes $\mathbf{U} \in \mathbf{V} \in \mathbf{W}$, such that $\omega \in \mathbf{U}$. All defined notions depend on a choice of cardinality. When nothing is specified, this corresponds to the implicit choice of the cardinality $\mathbf{V}$. We denote by Set the $\mathbf{W}$-small 1-category of $\mathbf{V}$-small sets, $\infty$-grd the $\mathbf{W}$-small $(\infty, 1)$-category of $\mathbf{V}$-small $\infty$-groupoids and $(\infty, 1)$-cat the $\mathbf{W}$-small $(\infty, 1)$-category of $\mathbf{V}$-small $(\infty, 1)$-categories.

## 6.1 Univalence

### 6.1.1 Internal category

**6.1.1.1.** For $X$ an object of $\mathrm{Psh}^{\infty}(\Theta)$ and $K$ a simplicial $\infty$-groupoid, we define the simplicial object $\langle X, K \rangle$ of $(\infty, \omega)$-cat whose value on $n$ is given by

$$\langle X, K \rangle_n := X \times K_n$$

If $K$ is the representable $[n]$, this object is simply denoted by $\langle X, n \rangle$. We also define the following set of morphism of $\mathrm{Psh}^{\infty}(\Delta \times \Theta)$:

$$\mathrm{T} := \{\langle a, f \rangle, \ a \in \Theta, f \in \mathrm{W}_1\} \cup \{\langle g, n \rangle, \ g \in \mathrm{W}, [n] \in \Delta\}$$

302

6.1. UNIVALENCE

6.1.1.2. A  \( (\infty,\omega,1) \) -category is a T-local  \( \infty \) -presheaf  \( C\in\mathrm{Psh}^{\infty}(\Theta\times\Delta) \) . We then naturally define

\[
(\infty , \omega , 1) \text {-cat} := \mathrm{Psh} ^ {\infty} (\Theta \times \Delta) _ {\mathrm{T}}.
\]

Unfolding the definition, an  \( (\infty,\omega,1) \) -category is a simplicial object  \( C:\Delta^{op}\to(\infty,\omega) \) -cat such that the induced morphisms

\[
C _ {0} \to \lim _ {[ k ] \to E ^ {e q}} C _ {k} \quad \text { and } \quad C _ {n} \to C _ {1} \times_ {C _ {0}} \times \ldots \times_ {C _ {0}} C _ {1} n \in \mathbb {N}
\]

are equivalences. Remark that we have a cartesian square

![img-346.jpeg](img-346.jpeg)

where the lower horizontal morphism is induced by the canonical inclusion of  \( (\infty,\omega) \) -category onto  \( \infty \) -presheaves on  \( \Theta \) , and the right vertical one is induced by the functor that maps an  \( (\infty,1) \) -category to the pair consisting of the  \( \infty \) -groupoid of objects and the  \( \infty \) -groupoid of arrows.

6.1.1.3. A morphism  \( p: X \to A \)  between two  \( \infty \) -presheaves on  \( \Theta \times \Delta \)  is a left fibration if it has the unique right lifting property against the set of morphism

\[
\mathrm{J} := \{\langle a, \{0 \} \rangle \rightarrow \langle a, n \rangle , a \in \Theta , [ n ] \in \Delta \} \cup \{\langle g, 0 \rangle , g \in \mathrm{W} \}
\]

Unfolding the notation, this is equivalent to asking that  \( X_{0} \rightarrow A_{0} \)  is W-local, and that the natural square

![img-347.jpeg](img-347.jpeg)

is cartesian.

Proposition 6.1.1.4. We have an inclusion \( T \subset \widehat{J} \).

Proof. Let \(a\) be an object of \(\Theta\). The \(\infty\)-groupoid of morphisms \(i\) of \(\mathrm{Psh}^{\infty}(\Delta)\) such that \(\langle a, i \rangle\) is in \(\widehat{J}\) contains by definition \(\{0\} \to [n]\), and is closed by colimits and left cancelation. This \(\infty\)-groupoid then contains all initial morphism between \(\infty\)-presheaves on \(\Delta\). As morphisms of \(\mathrm{W}_1\) are initial, \(\widehat{J}\) includes morphisms of shape \(\langle a, f \rangle\) for \(a \in \Theta\) and \(f \in \mathrm{W}_1\).

303

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Let \( g: a \to b \) be a morphism of W and n an integer. We have a commutative square

\[
\begin{array}{c} \langle a, \{0 \} \rangle \longrightarrow \langle a, n \rangle \\ \langle g, \{0 \} \rangle \Big \downarrow \qquad \qquad \qquad \qquad \Big \downarrow \langle g, n \rangle \\ \langle b, \{0 \} \rangle \longrightarrow \langle b, n \rangle \end{array}
\]

The two horizontal morphisms are in \(\widehat{J}\). By left cancellation, this implies that \(\langle g, n \rangle\) is in \(\widehat{J}\) which concludes the proof.

If  \( X \to A \)  is a left fibration, with A a  \( (\infty, \omega, 1) \) -category, the last proposition implies that X is also a  \( (\infty, \omega, 1) \) -category. We denote by  \( \operatorname{LFib}(A) \)  the full sub  \( (\infty, 1) \) -category of  \( (\infty, \omega, 1) \) -cat/A whose objects are left fibrations.

Proposition 6.1.1.5. There is a canonical equivalence:

\[
\operatorname{LFib} (\langle a, C \rangle) \sim \operatorname{Fun} (C, (\infty , \omega) \text {-cat} _ {/ a})
\]

natural in \(a:\Theta^{op}\) and \(C:(\infty ,1)\)-cat\(^{op}\).

Proof. Let \( a \) be an object of \( \Theta^{op} \) and \( C \) an \( (\infty, 1) \)-category. We have a canonical equivalence

\[
\mathrm{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ \langle a, C \rangle} \sim \mathrm{Psh} ^ {\infty} (\Theta_ {/ a} \times \Delta_ {/ C}) \sim \mathrm{Fun} (\Theta_ {/ a} ^ {o p}, \mathrm{Psh} ^ {\infty} (\Delta) _ {/ C})
\]

The previous equivalence induces an equivalence

\[
(\mathrm{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ \langle a, C \rangle}) _ {\{\langle b, \{0 \} \rangle \to \langle b, [ n ] \rangle \} / \langle a, C \rangle} \sim \mathrm{Fun} (\Theta_ {/ a} ^ {o p}, (\mathrm{Psh} ^ {\infty} (\Delta) _ {/ C}) _ {\mathrm{I} _ {/ C} ^ {0}})
\]

where \(\mathrm{I}_{/C}^{0}\) corresponds to the \(\infty\)-groupoid of morphisms of \(\mathrm{Psh}^{\infty}(\Delta)_{/C}\) of shape

![img-348.jpeg](img-348.jpeg)

for n any integer. The  \( (\infty,1) \) -category  \( (\mathrm{Psh}^{\infty}(\Delta)_{/C})_{\mathrm{I}_{/C}^{0}} \)  is equivalent to the  \( (\infty,1) \) -category of Grothendieck V-small opfibrations fibered in  \( \infty \) -groupoid over C, which is itself equivalent to  \( \operatorname{Fun}(C,\infty\text{-grd}) \)  according to the Grothendieck construction. We then have an equivalence

\[
\left(\mathrm{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ \langle a, C \rangle}\right) _ {\{\langle b, \{0 \} \rangle \rightarrow \langle b, [ n ] \rangle \} / \langle a, C \rangle} \sim \operatorname{Fun} \left(\Theta_ {/ a} ^ {o p}, \operatorname{Fun} (C, \infty - \operatorname{grd})\right) \sim \operatorname{Fun} (C, \mathrm{Psh} ^ {\infty} (\Theta) _ {/ a}) \tag {6.1.1.6}
\]

304

6.1. UNIVALENCE

By definition, $\mathrm{LFib}(\langle a,C\rangle)$ is the fully faithful sub $(\infty,1)$-category of the left hand $(\infty,1)$-category corresponding to objects that are local with respect to the image of set of morphism $\{\langle g,0\rangle,g\in\mathrm{W}\}_{/\langle a,C\rangle}$ by the localization functor

$$(\mathrm{Psh}^{\infty}(\Theta\times\Delta)_{/\langle a,C\rangle})\to(\mathrm{Psh}^{\infty}(\Theta\times\Delta)_{/\langle a,C\rangle})_{\{\langle b,\{0\}\rangle\to\langle b,[\mathrm{n}]\rangle\}_{/\langle a,C\rangle}}.$$

Such $\infty$-presheaves corresponds via the equivalence (6.1.1.6) to functors $C\to\mathrm{Psh}^{\infty}(\Theta)_{/a}$ that are pointwise $\mathrm{W}_{/a}$-local. As $\mathrm{W}_{/a}$-local $\infty$-presheaves on $\Theta_{/a}$ corresponds to elements of $(\infty,\omega)$-cat$_{/a}$, we have an equivalence

$$\mathrm{LFib}(\langle a,C\rangle)\sim\mathrm{Fun}(C,(\infty,\omega)\text{-cat}_{/a}).$$

6.1.1.7. A morphism $f:A\to B$ between two $\infty$-presheaves on $\Theta\times\Delta$ induces an adjunction

$$f_{!}:(\infty,\omega,1)\text{-cat}/A\xrightleftharpoons{\quad}(\infty,\omega,1)\text{-cat}_{/B}:f^{*}\tag{6.1.1.8}$$

where $f_{!}$ is the composition and $f^{*}$ is the pullback. As $\mathrm{LFib}(A)$ is the localization of $(\infty,\omega,1)\text{-cat}_{/A}$ along the class of morphisms $\widehat{\mathrm{J}_{/A}}$, the previous adjunction induces a derived adjunction:

$$\mathbf{L}f_{!}:\mathrm{LFib}(A)\xrightleftharpoons{\quad}\mathrm{LFib}(B):\mathbf{R}f^{*}\tag{6.1.1.9}$$

where $\mathbf{L}f_{!}$ sends $E$ onto $\mathbf{F}f_{!}E$ and $\mathbf{R}f^{*}$ is just the restriction of $f^{*}$ to $\mathrm{LFib}(B)$.

6.1.1.10. We denote by $\pi_{!}:\mathrm{Fun}(\Delta^{op},\mathrm{Psh}^{\infty}(\Theta))\to\mathrm{Psh}^{\infty}(\Delta[\Theta])$ the functor induced by extension by colimits by the canonical morphism $\pi:\Delta\times\Theta\to\Delta[\Theta]$. We also define $\mathrm{N}_{(\omega,1)}:\mathrm{Psh}^{\infty}(\Delta[\Theta])\to\mathrm{Fun}(\Delta^{op},\mathrm{Psh}^{\infty}(\Theta))$ as the right adjoint of $\pi_{!}$. As $\pi_{!}$ preserves representable, $\mathrm{N}_{(\omega,1)}$ preserves colimits. Remark that the image of $T$ by $\pi_{!}$ is contained in $\widehat{\mathrm{M}}$, and $\mathrm{N}_{(\omega,1)}$ induces then by restriction a functor

$$\mathrm{N}_{(\omega,1)}:(\infty,\omega)\text{-cat}\to(\infty,\omega,1)\text{-cat}.$$

If $C$ is an $(\infty,\omega)$-category, $\mathrm{N}_{(\omega,1)}C$ corresponds to the simplicial object in $(\infty,\omega)$-cat:

$$\dots\qquad\coprod_{x_{0},x_{1},x_{2}:\tau_{0}C}\mathrm{hom}_{C}(x_{0},x_{1},x_{2})\xrightleftharpoons{\quad}\coprod_{x_{0},x_{1}:\tau_{0}C}\mathrm{hom}_{C}(x_{0},x_{1})\xrightleftharpoons{\quad}\coprod_{x_{0}:\tau_{0}C}1$$

If $p:X\to\mathrm{N}_{(\omega,1)}C$ is a left fibration, and $x$ an object of $C$, we will denote by $X(x)$ the fiber of $p_{0}:X_{0}\to\mathrm{N}_{(\omega,1)}C$ on $x$, and $E(x)$ the canonical morphism $X(x)\to 1$. Unfolding the definitions, and using corollary 4.2.1.50, we then have for any integer $n$ a canonical equivalence:

$$X_{n}\sim\coprod_{x_{0},\dots,x_{n}}X(x_{0})\times\mathrm{hom}_{C}(x_{0},\dots,x_{n})$$

305

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Proposition 6.1.1.11. Let C be an  \( (\infty,\omega) \) -category, and E, F two objects of  \( \mathrm{LFib}(\mathrm{N}_{(\omega,1)}C) \)  corresponding to morphisms  \( X\to\mathrm{N}_{(\omega,1)}C \) ,  \( Y\to\mathrm{N}_{(\omega,1)}C \) . Let  \( \phi:E\to F \)  be a morphism. The following are equivalent:

(1) \(\phi\) is an equivalence,
(2) for any object \( x \) of \( C \), the induced morphism \( \mathbf{R}x^{*}\phi : \mathbf{R}x^{*}E \to \mathbf{R}x^{*}E \) is an equivalence,
(3) for any object \( x \) of \( C \), the induced morphism \( \phi(x): X(x) \to Y(x) \) is an equivalence,

Proof. The implication  \( (1) \Rightarrow (2) \)  is direct. The implication  \( (2) \Rightarrow (3) \)  comes from the fact that for any object x of C, the value on 0 of the simplicial object  \( Rx^{*}E \)  (resp.  \( Rx^{*}F \) ) is  \( X(x) \to 1 \)  (resp.  \( Y(x) \to 1 \) ).

Suppose now that \(\phi\) fulfills the last condition. As \(\mathrm{N}_{(\omega,1)}C\) is \(C_0\sim \coprod_{C_0}1\), we have equivalences

\[
X _ {0} \sim \coprod_ {x: C _ {0}} X (x) \quad Y _ {0} \sim \coprod_ {x: C _ {0}} Y (x).
\]

The morphism \(\phi_0: X_0 \to Y_0\) is then an equivalence. Eventually, as \(E\) and \(F\) are left fibrations, we have

\[
X _ {n} \sim X _ {\{0 \}} \times_ {(\mathrm{N} _ {(\omega , 1)} C) _ {\{0 \}}} (\mathrm{N} _ {(\omega , 1)} C) _ {n} \sim Y _ {\{0 \}} \times_ {(\mathrm{N} _ {(\omega , 1)} C) _ {\{0 \}}} (\mathrm{N} _ {(\omega , 1)} C) _ {n} \sim Y _ {n}.
\]

This implies  \( (3) \Rightarrow (1) \) , which concludes the proof.

Proposition 6.1.1.12. There is an equivalence natural in \(C: (\infty, \omega)\)-cat\(_{\mathrm{m}}^{op}\) between LFib(N\(_{(\omega,1)}[C,1]\)) and the \((\infty,1)\)-category whose objects are arrows of shape

\[
X (0) \times C \rightarrow X (1)
\]

and morphisms are natural transformations such that the induced morphism \( X(0) \times C \to Y(0) \times C \) is of shape \( f \times id_C \).

For a left fibration \( E \) corresponding to a morphism \( X \to [C,1] \), this arrow is the one appearing in the diagram:

![img-349.jpeg](img-349.jpeg)

where the left and the right squares are cartesian.

306

6.1. UNIVALENCE

Proof. Left fibrations are detected on pullback along representable. The functor  \( \mathrm{LFib}(\_) \)  then sends colimits of  \( \mathrm{Psh}^{\infty}(\Theta \times \Delta) \)  to limits. Remark that we have a cocartesian square

![img-350.jpeg](img-350.jpeg)

According to proposition 6.1.1.5, and as \(\mathrm{LFib}(\_)\) send colimits to limits, \(\mathrm{LFib}(\mathrm{N}_{(\omega,1)}[C,1])\) fits in the cartesian square

![img-351.jpeg](img-351.jpeg)

Using the adjunction

\[
\operatorname{dom}: (\infty , \omega) \text {-cat} _ {/ C} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat}: _ {-} \times C
\]

the \((\infty,1)\)-category \(\mathrm{LFib}(\mathrm{N}_{(\omega,1)}[C,1])\) fits in the cartesian square

![img-352.jpeg](img-352.jpeg)

The first assertion then follows from the last cartesian square and the proposition 5.2.5.5 applied to \( I := 1 \). The second is obtained by walking through the equivalences used in the proof of proposition 6.1.1.5.

Proposition 6.1.1.13. There is an equivalence natural in \(C: (\infty, \omega)\)-cat\(_{\mathrm{m}}^{op}\) between LFib(([C, 1] \(\otimes\) [1]\(^{\sharp}\))\(^{\sharp}\)) and the \((\infty, 1)\)-category whose objects are diagrams of shape

![img-353.jpeg](img-353.jpeg)

such that \( X(0,0) \times C^{\sharp} \otimes \{0\} \to X(0,1) \times C^{\sharp} \) is of shape \( f \times id_{C^{\sharp}} \). Morphisms are natural transformations such that the induced morphisms \( X(0,1) \times C^{\sharp} \to Y(0,1) \times C^{\sharp} \) and \( X(0,0) \times (C \otimes [1]^{\sharp})^{\sharp} \to Y(0,0) \times (C \otimes [1]^{\sharp})^{\sharp} \) are of shape \( g \times C^{\sharp} \) and \( h \times (C \otimes [1]^{\sharp})^{\sharp} \).

307

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Proof. The equation (5.1.3.9) implies that \(([C,1]\otimes [1]^{\sharp})^{\natural}\) is the colimit of the diagram

\[
[ 1 ] \vee [ C, 1 ] ^ {\natural} \longrightarrow [ C \otimes^ {\natural} \{0 \}, 1 ] \longleftarrow [ C \otimes [ 1 ] ^ {\sharp}, 1 ] ^ {\natural} \longleftarrow [ C ^ {\natural} \otimes \{1 \}, 1 ] \longrightarrow [ C, 1 ] ^ {\natural} \vee [ 1 ]
\]

According to proposition 5.1.1.37 and lemma 5.1.3.18, this colimit is special, and the \((\infty,1)\)-category \(\mathrm{N}_{(\omega,1)}([C,1] \otimes [1]^{\sharp})^{\natural}\) is then colimit, computed in \(\mathrm{Psh}(\Theta \times \Delta)\), of the diagram

![img-354.jpeg](img-354.jpeg)

We then deduce the result from the proposition 6.1.1.5 in the same way as in the previous proof.

Proposition 6.1.1.14. Let \( F: I \to (\infty, \omega) \)-cat be a W-small diagram. The canonical functor

\[
\operatorname{LFib} \left(\mathrm{N} _ {(\omega , 1)} \operatorname{colim} _ {I} F\right)\rightarrow \lim _ {I} \operatorname{LFib} \left(\mathrm{N} _ {(\omega , 1)} F\right)
\]

is an equivalence, where \(\operatorname{colim}_I F\) denotes the colimit taken in \((\infty, \omega)\)-cat.

Proof. Let \( C \) be an object of \( \mathrm{Psh}^{\infty}(\Theta) \). As left fibrations are detected by unique right lifting property against morphisms whose codomains are of shape \( \langle a, n \rangle \), a morphism \( p: X \to \mathrm{N}_{(\omega,1)}C \) is a left fibration if and only if for any \( i: [a, n] \to C \), \( (\mathrm{N}_{(\omega,1)}i)^{*}p \) is a left fibration. The functor

\[
\begin{array}{r c l} \mathrm{Psh} (\Delta [ \Theta ]) ^ {o p} & \to & (\infty , 1) \text {-cat} _ {\mathbf {W}} \\ X & \mapsto & \mathrm{LFib} (\mathrm{N} _ {(\omega , 1)} X) \end{array}
\]

then sends colimits to limits, where  \( (\infty,1) \) -cat \( _{W} \)  denotes the (huge)  \( (\infty,1) \) -category of W-small  \( (\infty,1) \) -categories. To conclude the proof, we then have to show that it sends any morphism  \( f \in M \)  to an equivalence. If f is of shape  \( [g,1] \)  for  \( g \in W \), this directly follows from proposition 6.1.1.12. Suppose now that f is  \( [a,Sp_{n}] \to [a,n] \). Remark that we have a cocartesian square:

![img-355.jpeg](img-355.jpeg)

The morphism \(\mathrm{LFib}(\mathrm{N}_{(\omega,1)}[a,\mathrm{Sp}_n])\to \mathrm{LFib}(\mathrm{N}_{(\omega,1)}[a,n])\) then fits in the cartesian square:

![img-356.jpeg](img-356.jpeg)

308

6.1. UNIVALENCE

According to proposition 6.1.1.5, we have equivalences

$$\mathrm{LFib}(\langle a, \mathrm{Sp}_n \rangle) \sim \lim_{[k] \to \mathrm{Sp}_n} \mathrm{Fun}([k], (\infty, \omega)\text{-cat}_{/a}) \sim \mathrm{Fun}([n], (\infty, \omega)\text{-cat}_{/a}) \sim \mathrm{LFib}(\langle a, n \rangle)$$

It remains the case $f := E^{eq} \to 1$. We have equivalences $\mathrm{N}_{(\omega,1)} E^{eq} \sim \langle [0], E^{eq} \rangle$ and $\mathrm{N}_{(\omega,1)} 1 \sim 1$. The proposition 6.1.1.5 induces equivalences

$$\mathrm{LFib}(\langle [0], E^{eq} \rangle) \sim \lim_{[k] \to E^{eq}} \mathrm{Fun}([k], (\infty, \omega)\text{-cat}) \sim \mathrm{Fun}(1, (\infty, \omega)\text{-cat})$$

which concludes the proof.

6.1.1.15. Let $A$ be an $(\infty, \omega, 1)$-category. An object $E : (\infty, \omega, 1)\text{-cat}_{/A}$ is **U-small** if for any morphism $i : \langle b, n \rangle \to A$, the space of morphism between $i$ and $E$ is **U-small**. Remark that an object $F$ of $\mathrm{LFib}(\mathrm{N}_{(\omega,1)} A)$ corresponding to a left fibration $X \to \mathrm{N}_{(\omega,1)} A$ is **U-small** if an only if for any object $a$ of $A$, $X(a)$ is **U-small**. Eventually, we define $\mathrm{LFib}_{\mathbf{U}}(A)$ as the full sub $(\infty, 1)$-category of $\mathrm{LFib}(A)$ whose objects correspond to **U-small** left fibrations. In particular, $\mathrm{LFib}_{\mathbf{U}}(A)$ is a **V-small** $(\infty, 1)$-category unlike $\mathrm{LFib}(A)$ which is a **W-small** $(\infty, 1)$-category. Moreover, the proposition 6.1.1.14 implies that the functor

$$C : (\infty, \omega)\text{-cat} \mapsto \tau_0 \mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} C)$$

sends colimits to limits. We then define $\underline{\omega}$ as the $(\infty, \omega)$-category that represents this object:

$$\begin{array}{rcl} \underline{\omega} : & \Theta^{op} & \to & \infty\text{-grd} \\ & a & \mapsto & \tau_0 \mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} a) \end{array} \tag{6.1.1.16}$$

We then have by definition an equivalence

$$\mathrm{Hom}(C, \underline{\omega}) \sim \tau_0 \mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} C). \tag{6.1.1.17}$$

As the functor $\mathrm{N}_{(\omega,1)}$ preserves product, for any $(\infty, \omega)$-category $D$, we also have a canonical equivalence

$$\mathrm{Hom}(C, \underline{\mathrm{Hom}}(D, \underline{\omega})) \sim \tau_0 (\mathrm{LFib}_{\mathbf{U}}(\mathrm{N}_{(\omega,1)} C \times \mathrm{N}_{(\omega,1)} D)). \tag{6.1.1.18}$$

Eventually, by construction, the $\infty$-groupoid of objects of $\underline{\omega}$ corresponds to the $\infty$-groupoid of **U-small** $(\infty, \omega)$-categories, and according to proposition 6.1.1.12, we have an equivalence

$$\mathrm{hom}_{\underline{\omega}}(C, D) \sim \underline{\mathrm{Hom}}(C, D). \tag{6.1.1.19}$$

The $(\infty, \omega)$-category $\underline{\omega}$ seems to be a decent candidate for the $(\infty, \omega)$-category of **U-small** $(\infty, \omega)$-categories.

309

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.1.1.20. Let \( S \) be a subset of \( \mathbb{N}^* \). We define the subset \( \Sigma S = \{i + 1, i \in S\} \). Remark that for any \( n \), we have

\[
(\mathrm{N} _ {(\omega , 1)} C) _ {n} ^ {S} \sim (\mathrm{N} _ {(\omega , 1)} C ^ {\Sigma S}) _ {n}
\]

We then set the functor

\[
(\_) ^ {S}: \underline {{\omega}} \to (\underline {{\omega}}) ^ {\Sigma S}
\]

sending a U-small left fibration  \( X \to \mathrm{N}_{(\omega,1)} C \)  to the left fibration  \( n \mapsto (X_{n}^{S} \to (\mathrm{N}_{(\omega,1)} C^{\Sigma S})_{n}^{S}) \) . These functors are called dualities. In particular, we have the odd duality  \( (\_)^{op} : \underline{\omega} \to \underline{\omega}^{co} \) , corresponding to the set of odd integer, the even duality  \( (\_)^{co} : \underline{\omega} \to (\underline{\omega}^{t})^{op} \) , corresponding to the subset of non negative even integer, the full duality  \( (\_)^{\circ} : \underline{\omega} \to \underline{\omega}^{t\circ} \) , corresponding to  \( N^{*} \)  and the transposition  \( (\_)^{t} : \underline{\omega} \to \underline{\omega}^{\Sigma t} \) , corresponding to the singleton  \( \{1\} \) . Eventually, we have equivalences

\[
((\_) ^ {c o}) ^ {o p} \sim (\_) ^ {\circ} \sim ((\_) ^ {o p}) ^ {c o}.
\]

#### 6.1.2 Grothendieck construction

Notation. Through this section, we will identify any marked  \( (\infty,\omega) \) -categories C with the canonical induced morphism  \( C\to1 \) . If  \( f:X\to Y \)  is a morphism,  \( f\times C \)  then corresponds to the canonical morphism  \( X\times C\to Y \) .

6.1.2.1. Let A be an  \( (\infty,\omega) \) -category and a an object of A, we denote by  \( h_{a}^{A} \)  the morphism  \( 1 \rightarrow A^{\sharp} \)  induces by a. At the end of section 5.2.1, we have remarked that the left fibrant replacement of  \( h_{a}^{A} \), that we denoted by  \( Fh_{a}^{A} \), is the fibration  \( A_{a/}^{\sharp} \rightarrow A^{\sharp} \). Equation (5.1.3.7) induces, for any object b of  \( A^{\sharp} \), a cartesian square

\[
\begin{array}{c} \hom_ {A} (a, b) ^ {\flat} \longrightarrow A _ {a /} ^ {\sharp} \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Biggl \downarrow \mathbf {F} h _ {a} ^ {A} \\ \{b \} \longrightarrow A ^ {\sharp} \end{array} \tag {6.1.2.2}
\]

which induces a canonical morphism \( h_b^A \times \mathrm{hom}_A(a, b)^b \to \mathbf{F}h_a^A \), and consequently, a morphism \( \mathbf{F}h_b^A \times \mathrm{hom}_A(a, b)^b \to \mathbf{F}h_a^A \).

The case of \( A := [C,1] \) will be of particular interest. The morphism \( \mathbf{F}h_1^{[C,1]} \) is just \( h_1^{[C,1]} \) and theorem 5.2.3.10 implies that \( \mathbf{F}h_0^{[C,1]} \) is the canonical morphism \( 1 \stackrel{\circ}{\star} C^\flat \to [C,1]^{\sharp} \). In this last case, the square (6.1.2.2) corresponds to the square

\[
\begin{array}{c} C ^ {\flat} \longrightarrow 1 \stackrel {{c o}} {{\star}} C ^ {\flat} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \mathbf {F} h _ {0} ^ {[ C, 1 ]} \\ \{1 \} \longrightarrow [ C, 1 ] ^ {\sharp} \end{array}
\]

310

6.1. UNIVALENCE

induces by the one of theorem 5.1.3.24. When nothing is specified, the morphism $C^{\flat} \to \mathbf{F}h_0^{[C,1]}$ will always corresponds to this square.

**6.1.2.3.** Let $C$ be an $(\infty, \omega)$-category. We define the simplicial marked $(\infty, \omega)$-category $C_{/}$ and the simplicial arrow of marked $(\infty, \omega)$-categories $\mathbf{F}h_{/}^{C}$ whose value on an integer $n$ is given by the following pullback

$$
\begin{array}{ccc}
(C_{/})_{n} & \longrightarrow & (C^{\sharp})^{[n+1]^{\sharp}} \\
(\mathbf{F}h_{/})_{n} \downarrow & & \downarrow \\
(\mathrm{N}_{(\omega,1)} C)_{n}^{\flat} \times C^{\sharp} & \longrightarrow & (C^{\sharp})^{[n]^{\sharp}} \times (C^{\sharp})^{\{n+1\}}
\end{array}
$$

and where the functoriality in $n$ is induced by the universal property of pullback. Unfolding the definition, on all integer $n$, the canonical morphism $(C_{/})_{n} \to C^{\sharp}$ corresponds to the morphism

$$
\coprod_{x_0, \dots, x_n: C_0} \hom_C^{\flat}(x_0, \dots, x_n) \times \mathbf{F}h_{x_n}^{C}
$$

and is then a left cartesian fibration according to theorem 5.2.3.3.

**6.1.2.4.** Let $E$ be an object of $(\infty, \omega, 1)$-cat$_{/\mathrm{N}_{(\omega,1)} C}$ corresponding to an arrow $X \to \mathrm{N}_{(\omega,1)} C$. The *Grothendieck construction* of $E$, is the object of $(\infty, \omega)$-cat$_{\mathrm{m}/C^{\sharp}}$ defined by the formula

$$
\int_C E := \operatorname{colim}_n (X^{\flat} \times_{(\mathrm{N}_{(\omega,1)} C)^{\flat}} \mathbf{F}h_{/})_{n}.
$$

As the Grothendieck construction is by definition a colimit of left cartesian fibrations, the theorem 5.2.3.3 implies that it is also a left cartesian fibration. The Grothendieck construction then defines a functor

$$
\int_C : (\infty, \omega, 1)\text{-cat}_{/\mathrm{N}_{(\omega,1)} C} \to \mathrm{LCart}(C^{\sharp}).
$$

Unfolding the definition, if $E$ is a left fibration, $\int_C E$ is the colimit of a simplicial diagram whose value on $n$ is:

$$
\coprod_{x_0, \dots, x_n: C_0} X(x_0) \times \hom_C^{\flat}(x_0, \dots, x_n) \times \mathbf{F}h_{x_n}^{C}
$$

**Example 6.1.2.5.** Let $E$ be an object of $\mathrm{LFib}(\mathrm{N}_{(\omega,1)}[a,1])$ corresponding to a morphism $X \to \mathrm{N}_{(\omega,1)}([a,1])$. According to proposition 6.1.1.12, this object corresponds to a morphism $X(0) \times a \to X(1)$. The arrow $\int_{[a,1]} E$ corresponds to the colimit of the following diagram:

$$
E(0)^{\flat} \times \mathbf{F}h_0^{[a,1]} \longleftarrow E(0)^{\flat} \times a^{\flat} \longrightarrow E(1)^{\flat}
$$

311

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

The domain of this arrow is then the colimit of the following diagram:

\[
X (0) ^ {\flat} \times [ a, 1 ] _ {0 /} ^ {\sharp} \longleftarrow X (0) ^ {\flat} \times a ^ {\flat} \longrightarrow X (1) ^ {\flat}
\]

Lemma 6.1.2.6. The functor \(\int_{C}:(\infty ,\omega ,1)\text{-cat}_{/N_{(\omega ,1)}C}\to \mathrm{LCart}(C^{\sharp})\) preserves colimits. Moreover, it sends morphisms of J to equivalences.

Proof. According to corollary 5.2.3.4, it is sufficient to show that the composite

\[
(\infty , \omega , 1) \text {-cat} _ {/ N _ {(\omega , 1)} C} \xrightarrow {\int_ {C}} \operatorname{LCart} (C ^ {\sharp}) \xrightarrow {\operatorname{dom}} (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

preserves colimits.

To this extend, we consider the functor

\[
\alpha : \mathrm{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ N _ {(\omega , 1)} C} \to \mathrm{Psh} ^ {\infty} (t \Theta \times \Delta)
\]

sending an object \(E\) of \(\mathrm{LFib}(\mathrm{N}_{(\omega,1)}C)\) corresponding to a morphism \(X\to (\mathrm{N}_{(\omega,1)}C)\) to \(X\times_{(\mathrm{N}_{(\omega,1)}C)^b}C_{/}\), and the functor

\[
\beta : \mathrm{Psh} ^ {\infty} (t \Theta \times \Delta) \to (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

that is the left Kan extension of the functor  \( t\Theta \times \Delta \to t\Theta \to \mathrm{mPsh}(\Theta) \) . As  \( \mathrm{Psh}^{\infty}(\Theta \times \Delta) \)  is locally cartesian closed,  \( \alpha \)  preserves colimits. The composite  \( \beta \circ \alpha \)  then preserves colimits. Moreover, we have a commutative diagram

\[
\begin{array}{c} \operatorname{Psh} ^ {\infty} (\Theta \times \Delta) _ {/ N _ {(\omega , 1)} C} \xrightarrow {\beta \circ \alpha} (\infty , \omega) \text {-cat} _ {\mathrm{m}} \\ \mathbf {F} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (\infty , \omega , 1) \text {-cat} _ {/ N _ {(\omega , 1)} C} \xrightarrow [ \int_ {C} ]{} \operatorname{LCart} (C ^ {\sharp}) \end{array}
\]

According to proposition 6.1.1.4, one then has to show that \(\beta \circ \alpha\) sends any morphism of \(J\) to an equivalence to conclude. Indeed, it will implies that \(\beta \circ \alpha\) lifts to a colimit preserving functor

\[
\mathbf {D} (\beta \circ \alpha): (\infty , \omega , 1) \text {-cat} _ {/ N _ {(\omega , 1)} C} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}},
\]

and the previous square implies that this morphism is equivalent to \(\mathrm{dom}\int_{C}\).

Suppose given two cartesian squares

\[
\begin{array}{c} X \xrightarrow {g} X ^ {\prime} \xrightarrow {} C _ {/} \\ \Big \downarrow \quad \Big \downarrow \quad \Big \downarrow \\ \langle a, \{0 \} \rangle \xrightarrow [ f ]{} \langle a, [ n ] \rangle \longrightarrow (\mathrm{N} _ {(\omega , 1)} C) ^ {b} \end{array}
\]

312

6.1. UNIVALENCE

By currying, we see these objects as functors $t\Theta^{op} \to \mathrm{Psh}^{\infty}(\Delta)$. The right vertical morphism is then pointwise a right fibration of $(\infty, 1)$-categories fibered in $\infty$-groupoids, as it corresponds, for a fixed $a : t\Theta$ and $n : \Delta$, to the morphism of $\infty$-groupoid:

$$\coprod_{x_0, \dots, x_n : C_0} \mathrm{Hom}(a, \mathrm{hom}_C(x_0, \dots, x_n)^\flat) \times \mathrm{Hom}(a, C_{x_n}^\sharp) \to \coprod_{x_0, \dots, x_n : C_0} \mathrm{Hom}(a, \mathrm{hom}_C(x_0, \dots, x_n)^\flat).$$

As the morphism $f$ is pointwise initial, so is $g$. As $\beta$ sends pointwise initial morphisms to equivalence, this implies that $\beta\alpha(f) := \beta(g)$ is an equivalence.

Suppose now given two cartesian squares

$$\begin{array}{c} X \xrightarrow{g} X' \xrightarrow{\quad} C_./ \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ \langle a, 0 \rangle \xrightarrow{\langle f, 0 \rangle} \langle b, 0 \rangle \longrightarrow (\mathrm{N}_{(\omega, 1)} C)^\flat \end{array}$$

with $f \in \mathrm{W}$. By currying, we see these objects as functors $\Delta \to \mathrm{Psh}^{\infty}(t\Theta)$. The right vertical morphism is then pointwise a right cartesian fibration. As the morphism $\langle f, 0 \rangle$ is pointwise in $\widehat{\mathrm{tW}}$, so is $g$. The morphism $\mathrm{colim}_n g_n$ is then in $\widehat{\mathrm{tW}}$ and $\beta\alpha(f) := \beta(g)$ is an equivalence.

### 6.1.2.7. We will denote also by

$$\int_C : \mathrm{LFib}(\mathrm{N}_{(\omega, 1)} C) \to \mathrm{LCart}(C^\sharp)$$

the restriction of the Grothendieck construction. This will not cause any confusion as from now on we will only consider the Grothendieck construction of left fibration. The lemma 6.1.2.6 then implies that this functor is colimit preserving, and it is then part of an adjunction

$$\int_C : \mathrm{LFib}(\mathrm{N}_{(\omega, 1)} C) \xrightarrow{\quad} \mathrm{LCart}(C^\sharp) : \partial_C \tag{6.1.2.8}$$

**Lemma 6.1.2.9.** Let $i : C^\sharp \to D^\sharp$ be a morphism. The natural transformation

$$\partial_C \circ \mathbf{R} i^* \to \mathbf{R}(\mathrm{N}_{(\omega, 1)} i)^* \circ \partial_D$$

is an equivalence.

Proof. As equivalences between left fibrations are detected on fibers, one can suppose that $C$ is the terminal $(\infty, \omega)$-category. Let $c$ denote the object of $D$ corresponding to $i$. Let $E$ be an object of $\mathrm{LFib}(\mathrm{N}_{(\omega, 1)} 1)$, corresponding to a morphism $A \to 1$. According to lemma 6.1.2.6, we then have equivalences

$$\begin{array}{l} \mathbf{L} i_! \int_1 E \sim \mathbf{L} i_! (A^\flat \times h_1^1) \\ \qquad \sim A^\flat \times \mathbf{F} h_c^D \\ =: \int_D \mathrm{N}_{(\omega, 1)} i_! E \\ \qquad \sim \int_D \mathbf{L}(\mathrm{N}_{(\omega, 1)} i)_! E \quad (6.1.2.6) \end{array}$$

313

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

The canonical morphism \(\mathbf{L}i_{!} \circ \int_{1} \to \int_{D} \circ \mathbf{L}(\mathrm{N}_{(\omega,1)} i)_{!}\) is then an equivalence, which implies by adjunction that \(\partial_{1} \circ \mathbf{R}_{i}^{*} \to \mathbf{R}(\mathrm{N}_{(\omega,1)} i)^{*} \circ \partial_{D}\) also is.

6.1.2.10. Let \( C \) be an \( (\infty, \omega) \)-category and \( c \) an object of \( C^\sharp \). We define \( (\mathrm{N}_{(\omega,1)}C)_{/c} \) as the simplicial object in \( (\infty, \omega) \)-cat whose value on \( (a, n) \) fits in the cocartesian square

![img-357.jpeg](img-357.jpeg)

Unfolding the definition, \((\mathrm{N}_{(\omega ,1)}C)_{/c}\) is the simplicial diagram whose value on \(n\) is

\[
\coprod_ {x _ {0}, \dots , x _ {n}} \hom_ {C} (x _ {0}, \dots , x _ {n}, c)
\]

Lemma 6.1.2.11. There is an equivalence

\[
\left(\left(\mathrm{N} _ {(\omega , 1)} C\right) _ {/ c}\right) ^ {\flat} \sim c ^ {*} \mathbf {F} h..
\]

Proof. A morphism \(\langle a, n \rangle \to (c^*\mathbf{F}h.)^\sharp\) is the data of a commutative square

![img-358.jpeg](img-358.jpeg)

which is, according to proposition 5.1.3.23, equivalent to a morphism

\[
[ a, n + 1 ] ^ {\sharp} \to C ^ {\sharp}
\]

and so to a morphism \(\langle a, n \rangle \to (\mathrm{N}_{(\omega,1)} C)_{c/}\). As \(c^*\mathbf{F}h\). has a trivial marking, this shows the desired equivalence.

Lemma 6.1.2.12. Let \( p: X \to \mathrm{N}_{(\omega,1)}C \) be a left fibration, and \( c \) an object of \( C \). The canonical morphism

\[
X (c) \to \underset {n} {\operatorname{colim}} (X \times_ {\mathrm{N} _ {(\omega , 1)} C} (\mathrm{N} _ {(\omega , 1)} C) _ {/ c}) _ {n}
\]

is an equivalence.

Proof. We will show a slightly stronger statement, which is that the morphism

\[
X (c) \to \underset {n} {\operatorname{colim}} (X \times_ {(\mathrm{N} _ {(\omega , 1)} C)} (\mathrm{N} _ {(\omega , 1)} C) _ {/ c}) _ {n}
\]

314

6.1. UNIVALENCE

is an equivalence when the colimit is taken in  \( \infty \) -presheaves on  \( \Theta \) . As the colimit in presheaves commutes with evaluation, one has to show that for any globular sum a, the canonical morphism of  \( \infty \) -groupoids

\[
\mathrm{Hom} (a, X (c)) \to \underset {n} {\mathrm{colim}} (\mathrm{Hom} (a, X _ {n}) \times_ {\mathrm{Hom} (a, (\mathrm{N} _ {(\omega , 1)} C) _ {n})} \mathrm{Hom} (a, (\mathrm{N} _ {(\omega , 1)} C) _ {/ c}) _ {n})
\]

is an equivalence. Remark that the simplicial \(\infty\)-groupoid \(\mathrm{Hom}(a, ((\mathrm{N}_{(\omega,1)}C)_{/c})_{\bullet})\) is equivalent to the simplicial \(\infty\)-groupoid \((\mathrm{Hom}(a, \mathrm{N}_{(\omega,1)}C)_{\bullet})_{/c}\). If we denote also by \(\mathrm{Hom}(a, X(c))\) the constant simplicial \(\infty\)-groupoid \(n \mapsto \mathrm{Hom}(a, X(c))\), we have a cartesian square

![img-359.jpeg](img-359.jpeg)

Moreover, the left vertical morphism is a left fibration of  \( (\infty,1) \) -category fibered in  \( \infty \) -groupoid. As pullbacks along left fibrations preserve final morphisms, the morphism

\[
\mathrm{Hom} (a, X (c)) \to \mathrm{Hom} (a, X _ {\bullet}) \times_ {\mathrm{Hom} (a, (\mathrm{N} _ {(\omega , 1)} C) _ {\bullet})} \mathrm{Hom} (a, (\mathrm{N} _ {(\omega , 1)} C) _ {\bullet}) _ {/ c}
\]

is final. Taking the colimit, this implies the result.

Lemma 6.1.2.13. Let \(i:C^{\sharp}\to D^{\sharp}\) be a morphism. The natural transformation

\[
\int_ {D} \circ \mathbf {R} (\mathrm{N} _ {(\omega , 1)} i) ^ {*} \rightarrow \mathbf {R} i ^ {*} \circ \int_ {C}
\]

is an equivalence.

Proof. As equivalences between left cartesian fibrations are detected on fibers, one can suppose that C is the terminal  \( (\infty,\omega) \) -category. Let c denote the object of D corresponding to i and let E be an object of  \( \mathrm{LFib}(\mathrm{N}_{(\omega,1)}C) \) , corresponding to a left fibration  \( X\to\mathrm{N}_{(\omega,1)}C \) . By construction,  \( \int_{C}E \)  is a colimit of left cartesian fibrations. However, as proposition 5.2.4.13 states that  \( Ri^{*} \)  commutes with colimit, we have

\[
\begin{array}{l} \mathbf {R} i ^ {*} \int_ {C} E \sim \operatorname{colim} _ {n} X _ {n} ^ {\flat} \times_ {(\mathrm{N} _ {(\omega , 1)} C) _ {n} ^ {\flat}} \mathbf {R} i ^ {*} \mathbf {F} h _ {\cdot} ^ {C} \\ \sim \operatorname{colim} _ {n} (X \times_ {\mathrm{N} _ {(\omega , 1)} C} (\mathrm{N} _ {(\omega , 1)} C) _ {/ c}) _ {n} ^ {\flat} \tag {6.1.2.11} \\ \end{array}
\]

Moreover, remark that \(\int_{1} \mathbf{R}(\mathrm{N}_{(\omega,1)} i)^{*} E\) is equivalent to \(X(c)\), and the canonical morphism \(\int_{D} \mathbf{R}(\mathrm{N}_{(\omega,1)} i)^{*} E \to \mathbf{R} i^{*} \int_{C} E\) is then the image by \((\_)^{\flat}\) of the equivalence given by lemma 6.1.2.12.

Proposition 6.1.2.14. The functors \(\int_{C}\) and \(\partial_C\) are natural in \(C:(\infty ,\omega)\)-cat\(^{op}\).

315

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Proof. We denote by \(\mathrm{Arr}^{fib}((\infty, \omega)\text{-cat}_{\mathfrak{m}})\) (resp. \(\mathrm{Arr}^{fib}((\infty, \omega, 1)\text{-cat})\)) the full sub \((\infty, 1)\)-category of \(\mathrm{Arr}((\infty, \omega)\text{-cat}_{\mathfrak{m}})\) (resp. \(\mathrm{Arr}((\infty, \omega, 1)\text{-cat})\)) whose objects are U-small left cartesian fibrations (resp. U-small left fibrations). We also set \((\infty, \omega)\text{-cat} \times_{(\infty, \omega)\text{-cat}_{\mathfrak{m}}} \mathrm{Arr}^{fib}((\infty, \omega)\text{-cat}_{\mathfrak{m}})\) and \((\infty, \omega)\text{-cat} \times_{(\infty, \omega, 1)\text{-cat}} \mathrm{Arr}^{fib}((\infty, \omega, 1)\text{-cat})\) as the pullbacks:

![img-360.jpeg](img-360.jpeg)

![img-361.jpeg](img-361.jpeg)

The two left vertical morphism inherit from the right vertical morphisms of a structure of Grothendieck fibrations fibered in  \( (\infty,1) \) -categories, where cartesian liftings are given by morphisms between arrows corresponding to cartesian squares.

As the assignation \( C \mapsto \mathbf{F}h^{C} \) can be promoted in a functor \( (\infty, \omega) \)-cat \( \to \operatorname{Arr}(\operatorname{Fun}(\Delta, (\infty, \omega) \text{-cat}_{\mathfrak{m}})) \) the functors \( \int_{C} \) and \( \partial_{C} \) are the restrictions of two functors \( \int \) and \( \partial \) fitting in commutative triangles:

![img-362.jpeg](img-362.jpeg)

![img-363.jpeg](img-363.jpeg)

Lemmas 6.1.2.9 and 6.1.2.13 imply that these two functors preserve cartesian arrows, and the Grothendieck deconstruction then implies the desired result. \(\square\)

Theorem 6.1.2.15. For any \((\infty, \omega)\)-category \(C\), the adjunction

\[
\int_ {C}: \mathrm{LFib} (\mathrm{N} _ {(\omega , 1)} C) \xrightarrow [ \leftarrow ]{\perp} \mathrm{LCart} (C ^ {\sharp}): \partial_ {C}
\]

defined in (6.1.2.8), is an adjoint equivalence.

316

6.1. UNIVALENCE

Proof. As equivalences between left fibrations and between left cartesian fibrations are detected on fibers, and as the two functors are natural in $C$, it is sufficient to show the result for $C$ being the terminal $(\infty, \omega)$-category. In this case remark that $\mathrm{LFib}(\mathrm{N}_{(\omega,1)} 1) \sim \mathrm{LCart}(1)$ and that both $\int_1$ and $\partial_1$ are the identities. $\square$

Corollary 6.1.2.16. Let $F : I \to (\infty, \omega)$-cat$_\mathrm{m}$ be a $\mathbf{W}$-small diagram. The canonical functor

$$\mathrm{LCart}^c(\underset{I}{\operatorname{colim}} F) \to \lim_{I} \mathrm{LCart}^c(F)$$

is an equivalence.

Proof. This functor fits in an adjunction:

$$\operatorname{colim}_I : \lim_I \mathrm{LCart}^c(F) \xrightarrow{\perp} \mathrm{LCart}^c(\operatorname{colim}_I F)$$

The corollary 5.2.2.13 implies that the counit of this adjunction is an equivalence. To conclude, we have to show that the right adjoint is essentially surjective. By definition, the morphism $\tau_0 \mathrm{LCart}(I^\sharp) \to \tau_0 \mathrm{LCart}^c(I)$ is an equivalence. According to theorem 6.1.2.15, on the $\infty$-groupoid of objects, the right adjoint corresponds to the equivalence

$$\tau_0 \mathrm{LFib}(\mathrm{N}_{(\omega,1)} \underset{I}{\operatorname{colim}} F^\sharp) \to \lim_{I} \tau_0 \mathrm{LFib}(\mathrm{N}_{(\omega,1)} F^\sharp)$$

given in proposition 6.1.1.14. $\square$

Corollary 6.1.2.17. Let $C$ be an $(\infty, \omega)$-category and $c$ be an object of $c$. The left fibration $\partial_C \mathbf{F} h_c$ is the morphism of simplicial objects:

$$\begin{array}{ccc} \cdots & \coprod_{x_0, x_1, x_2: C_0} \hom_C(y, x_0, x_1, x_2) \xrightarrow{\longleftrightarrow} \coprod_{x_0, x_1: C_0} \hom_C(y, x_0, x_1) \xrightarrow{\longleftrightarrow} \coprod_{x_0: C_0} \hom_C(y, x_0) \\ & \downarrow & \downarrow \\ \cdots & \coprod_{x_0, x_1, x_2: C_0} \hom_C(x_0, x_1, x_2) \xrightarrow{\longleftrightarrow} \coprod_{x_0, x_1: C_0} \hom_C(x_0, x_1) \xrightarrow{\longleftrightarrow} \coprod_{x_0: C_0} 1 \end{array}$$

Proof. We denote by $E := X \to \mathrm{N}_{(\omega,1)} C$ this left fibration. According to theorem 6.1.2.15, we can equivalently show that the Grothendieck integral of $E$ is the morphism $C_{c/}^\sharp \to C$. Remark that we have by construction a family of cartesian squares

$$\begin{array}{ccc} X_n \times_{(\mathrm{N}_{(\omega,1)} C)_n} (C_{/})_n & \longrightarrow & (C^\sharp)^{[1+n+1]\sharp} \xrightarrow{(C^\sharp)^{hn}} (C^\sharp)^{[1]\sharp} \\ \downarrow & \downarrow & \downarrow \\ \{c\} \times (\mathrm{N}_{(\omega,1)} C)_n \times C^\sharp & \longrightarrow & C^\sharp \times (C^\sharp)^{[n]\sharp} \times C^\sharp \longrightarrow C^\sharp \times C^\sharp \end{array}$$

317

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

natural in n, where  \( h_{n} \)  is the simplicial morphism preserving the extremal points. The outer square factors in two cartesian squares:

![img-364.jpeg](img-364.jpeg)

This provides a canonical morphism

\[
\int_ {C} E := \underset {n} {\mathrm{colim}} (X _ {n} \times_ {(\mathrm{N} _ {(\omega , 1)} C) _ {n}} (\mathbf {F} h.) _ {n}) \to \mathbf {F} h _ {c} ^ {C}
\]

To conclude, one has to show that it is an equivalence, and for this, to check that this is the case on fibers, where it directly follows from the naturality of the integral given in proposition 6.1.2.14.

Corollary 6.1.2.18. Let \( E \) be an object of \( (\infty, \omega) \)-cat\(_{/[b,1]^{\sharp}}\) corresponding to a morphism \( p: X \to [b,1]^{\sharp} \). Consider the induced cartesian squares:

![img-365.jpeg](img-365.jpeg)

The span associated to \(\partial_{[b,1]}\mathbf{F}E\) via the equivalence of proposition 6.1.1.12 is

\[
\bot X _ {0} \leftarrow (\bot X _ {0}) \times b \xrightarrow {\bot g} \bot X _ {/ 1}. \tag {6.1.2.19}
\]

Proof. We denote \(\tilde{X} \to [b,1]^{\sharp}\) the morphism associated to \(\mathbf{F}E\). As, As \([b,1]_{/1}^{\sharp} \to [b,1]^{\sharp}\) and \(\{0\} \to [b,1]^{\sharp}\) are right cartesian fibrations, they are smooth, and the canonical morphisms

\[
X _ {/ 1} \to \tilde {X} _ {/ 1} \qquad \mathrm{and} \qquad X _ {0} \to \tilde {X} _ {0}
\]

are initial. As  \( \perp \)  sends initial morphisms to equivalences, the induced morphisms

\[
\bot X _ {/ 1} \to \bot \tilde {X} _ {/ 1} \qquad \mathrm{and} \qquad \bot X _ {0} \to \bot \tilde {X} _ {0}
\]

are equivalences. We can then suppose that \( E \) corresponds to a left cartesian fibration.

318

6.1. UNIVALENCE

As $\{1\} \to [b, 1]^{\sharp}$ is a right Gray deformation retract, so is the inclusion $X_1 \to X_{/1}$ according to proposition 5.2.1.13. The right Gray deformation retract structure induces a diagram:

![img-366.jpeg](img-366.jpeg)

By post composing with $g: X_0 \otimes b^{\flat} \to X_{/1}$ and post composing $f: X_{/1} \to X$, we get a diagram:

![img-367.jpeg](img-367.jpeg)

Remark furthermore that the following diagram:

![img-368.jpeg](img-368.jpeg)

admits a lift $l$. Indeed, the left vertical morphism is initial, and the right vertical one is a left cartesian fibration. All put together, we get a diagram

![img-369.jpeg](img-369.jpeg)

where the upper horizontal morphism is induced by the restriction of $l$ to $(X_0 \times b^{\flat}) \otimes \{1\}$. As $X_1 \to X_{/1}$ is initial, we have $\perp X_{/1} \sim \perp X_1$ and $\perp r$ is an equivalence. We denote by $F$ the left fibration associated to (6.1.2.19). The previous square then corresponds to a morphism

$$\int_{[b,1]} F \to E$$

Using the naturality of $\int_{[b,1]}$, one can see that this morphism induces an equivalence on fibers, and is then an equivalence. Applying $\partial_{[b,1]}$ and using theorem 6.1.2.15, this concludes the proof.

319

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**6.1.2.20.** A left cartesian fibration is **U**-small if its fibers are **U**-small $(\infty, \omega)$-categories. For an $(\infty, \omega)$-category $A$, we denote by $\mathrm{LCart}_{\mathbf{U}}(A^{\sharp})$ the full sub $(\infty, 1)$-category of $\mathrm{LCart}(A^{\sharp})$ whose objects correspond to **U**-small left cartesian fibrations over $A^{\sharp}$.

**Corollary 6.1.2.21.** *Let $\underline{\omega}$ be the **V**-small $(\infty, \omega)$-category of **U**-small $(\infty, \omega)$-categories and $A$ a **V**-small $(\infty, \omega)$-category. There is an equivalence*

$$\int_A : \mathrm{Hom}(A, \underline{\omega}) \to \tau_0 \mathrm{LCart}_{\mathbf{U}}(A^{\sharp})$$

*natural in $A : (\infty, \omega)$-cat$^{op}$.*

*Proof.* This is a direct consequence of the theorem 6.1.2.15 and the definition of $\underline{\omega}$. $\square$

**Corollary 6.1.2.22.** *The left cartesian fibration $\int_{\underline{\omega}} id$ is the universal left cartesian fibration with **U**-small fibers, i.e for any left cartesian fibration $X \to A^{\sharp}$ with **U**-small fibers, there exists a unique morphism $X \to \underline{\omega}$ and a unique cartesian square:*

$$\begin{array}{ccc} X & \longrightarrow & \mathrm{dom} \int_{\underline{\omega}} id \\ \downarrow & & \downarrow \int_{\underline{\omega}} id \\ A^{\sharp} & \longrightarrow & \underline{\omega}^{\sharp} \end{array}$$

*Proof.* This is a direct consequence of the corollary 6.1.2.21 and the functoriality of the Grothendieck construction given in proposition 6.1.2.14. $\square$

### 6.1.3 Univalence

**Notation.** Through this section, we will identify any marked $(\infty, \omega)$-category $C$ with the canonical induced morphism $C \to 1$. If $f : X \to Y$ is a morphism, $f \times C$ then corresponds to the canonical morphism $X \times C \to Y$.

**6.1.3.1.** For the remaining of this section, we fix a marked $(\infty, \omega)$-category $I$. Remark that $\mathbf{F}h_k^{[n]}$ corresponds to the inclusion $(d_0^{\sharp})^k : [n - k]^{\sharp} \to [n]^{\sharp}$. We define the functor

$$\oint_{n,I} : \mathrm{Fun}([n], (\infty, \omega)\text{-cat}_{\mathrm{m}/I}) \to (\infty, \omega)\text{-cat}_{\mathrm{m}/I \otimes [n]^{\sharp}}$$

whose value on a morphism $E : [n] \to (\infty, \omega)\text{-cat}_{\mathrm{m}/I}$ corresponding to a sequence $E_0 \to \dots \to E_n$, is

$$\oint_{n,I} E := \underset{m}{\mathrm{colim}} \coprod_{i_0 \le \dots \le i_m \le n} E_{i_0} \otimes \mathbf{F}h_{i_m}^{[n]}.$$

As this functor is colimit preserving, it induces an adjunction

$$\oint_{n,I} : \mathrm{Fun}([n], (\infty, \omega)\text{-cat}_{\mathrm{m}/I}) \xrightarrow{\perp} (\infty, \omega)\text{-cat}_{\mathrm{m}/I \otimes [n]^{\sharp}} : \mathring{\partial}_{n,I} \tag{6.1.3.2}$$

320

6.1. UNIVALENCE

Lemma 6.1.3.3. The functor \(\oint_{n,I}\) sends a natural transformation that is pointwise initial to an initial morphism.

Proof. As initial morphisms are closed under colimits, we have to show that for any integer \( k \), and any morphism \( E \to F \) of \( (\infty, \omega) \)-cat\(_{\mathrm{m}/I}\) corresponding to a sequence \( X \xrightarrow{i} Y \to I \), the induced morphism \( X \otimes [n - k]^{\sharp} \to Y \otimes [n - k]^{\sharp} \) over \( I \otimes [n]^{\sharp} \) is initial whenever \( i \) is. For this, remark that there is a square

![img-370.jpeg](img-370.jpeg)

where the two horizontal morphisms are initial. By stability by composition and left cancellation of initial morphism, this implies the result.

6.1.3.4. According to the last lemma, the adjunction (6.1.3.2) induces a derived adjunction

\[
\mathbf {L} \oint_ {n, I}: \operatorname{Fun} ([ n ], \operatorname{LCart} (I)) \xrightarrow [ \leftarrow ]{\perp} \operatorname{LCart} (I \otimes [ n ] ^ {\sharp}): \mathbf {R} \mathring {\partial} _ {n, I} \tag {6.1.3.5}
\]

where \(\mathbf{R}\mathring{\partial}_{n,I}\) is just the restriction of \(\mathring{\partial}_{n,I}\) to \(\mathrm{LCart}(I\otimes [n]^{\sharp})\).

Lemma 6.1.3.6. Let \( i:[n]^{\sharp}\to [m]^{\sharp} \) and \( j:I\to J \) be two morphisms. Let \( E \) be an object of \( \mathrm{LCart}(I\otimes [m]^{\sharp}) \). The natural transformation

\[
\mathring {\partial} _ {n, I} (j \otimes i) ^ {*} E \rightarrow j ^ {*} \circ \mathring {\partial} _ {m, J} E \circ i ^ {\natural}
\]

is an equivalence.

Proof. As invertible natural transformations are detected pointwise, one can suppose that \( n = 0 \), and let \( k \) be the image of [0] by \( i \). Let \( E_0 \to E_1 \to .. \to E_m \) be the sequence of morphisms of \( \mathrm{LCart}(J) \) corresponding to \( \mathring{\partial}_{m,J}E \).

The object \( j^{*} \circ \mathring{\partial}_{m,J} E \circ i^{\natural} \) is then equivalent to \( j^{*}E_{k} \) by definition. As \( \mathring{\partial}_{0,I} \) is the identity, we have to show that the canonical morphism \( (j \otimes \{k\})^{*}E \to j^{*}E_{k} \) is an equivalence. Remark that for any \( F \) of \( (\infty, \omega) \)-cat\(_{\mathrm{m}/I}\), we have by adjunction a commutative square:

![img-371.jpeg](img-371.jpeg)

where the two vertical morphisms are equivalences. As  \( ((j \otimes \{k\})_{!}F \sim (j_{!}F) \otimes h_{k}^{[n]} \) , the lower morphism is an equivalence, and so is the top one. This implies the desired result.

321

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.1.3.7. In the following lemmas and proposition, we focus on the case where I is of the form  \( A^{\sharp} \) , where everything happens more simply.

Lemma 6.1.3.8. Let \( j: A \to B \) be a morphism between \( (\infty, \omega) \)-categories and \( i: [n] \to [m] \) a morphism of \( \Delta \). Let \( E \) be an object of \( \operatorname{Fun}([n], \operatorname{LCart}(A^{\sharp})) \). The canonical morphism

\[
\mathbf {L} \oint_ {n, A ^ {\sharp}} (\mathbf {R} j ^ {*} \circ E \circ i) \rightarrow \mathbf {R} (j \times i ^ {\sharp}) ^ {*} \mathbf {L} \oint_ {m, B ^ {\sharp}} E
\]

is an equivalence.

Proof. As equivalences in  \( \operatorname{Fun}([m],\operatorname{LCart}(B^{\sharp})) \)  are detected on points, an equivalences on  \( \operatorname{LCart}(B^{\sharp}\times[m]^{\sharp}) \)  are detected on fibers, we can suppose that n=0, A=1, and we denote by k the image of i and a the image of B. As  \( L\oint_{0,1} \)  is the identity, one has to show that the canonical morphism

\[
\mathbf {R} a ^ {*} E _ {k} \rightarrow \mathbf {R} (a \times \{k \}) ^ {*} \mathbf {L} \oint_ {m, B ^ {\sharp}} E \tag {6.1.3.9}
\]

is an equivalence.

Moreover, for any \( l \leq n \), the proposition 5.2.1.7 implies that the canonical morphism \( \mathbf{F}(E_l \otimes \mathbf{F}h_l^{[n]}) \to E_l \times \mathbf{F}h_l^{[n]} \) is an equivalence, as this two left cartesian fibrations are replacement of \( E_l \otimes h_l^{[n]} \sim E_l \times h_l^{[n]} \). According to proposition 5.2.4.13, \( \mathbf{R}(a \times \{k\}^\sharp)^* \) preserves colimits, we then have

\[
\mathbf {R} (a \times \{k \}) ^ {*} \mathbf {L} \oint_ {m, B ^ {\sharp}} E \sim \underset {m} {\mathrm{colim}} \prod_ {i _ {0} \leq \ldots \leq i _ {m} \leq k} \mathbf {R} a ^ {*} E _ {i _ {0}} \sim \underset {i: [ k ]} {\mathrm{colim}} \mathbf {R} a ^ {*} E _ {i} \sim \mathbf {R} a ^ {*} E _ {k}.
\]

The morphism (6.1.3.9) is then an equivalence, which concludes the proof.

Proposition 6.1.3.10. The functor \(\mathbf{R}\mathring{\partial}_{n,I}\) is natural in \(n:\Delta^{op}\) and \(I:(\infty ,\omega)\text{-cat}_{\mathrm{m}}^{op}\). The functor \(\oint_{n,A^{\sharp}}\) is natural in \(n:\Delta^{op}\) and \(A:(\infty ,\omega)\text{-cat}^{op}\).

Proof. The proof is similar to the one of proposition 6.1.2.14, using lemma 6.1.3.6 and lemma 6.1.3.8 instead of lemma 6.1.2.9 and lemma 6.1.2.13. \(\square\)

Proposition 6.1.3.11. For any \((\infty, \omega)\)-category \(A\) and any integer \(n\), the adjunction

\[
\mathbf {L} \oint_ {n, A ^ {\sharp}}: \mathrm{Fun} ([ n ], \mathrm{LCart} (A ^ {\sharp})) \xrightarrow [ \longleftarrow ]{\perp} \mathrm{LCart} ((A \times [ n ]) ^ {\sharp}): \mathbf {R} \mathring {\partial} _ {n, A ^ {\sharp}}
\]

is an adjoint equivalence.

Proof. As in both case equivalences are detected on fibers, and as these functors are natural in A and n, one can show the result for A being the terminal  \( (\infty,\omega) \) -category and n=0. In this case remark that these two functors are the identities. □

322

6.1. UNIVALENCE

6.1.3.12. We set $\operatorname{Fun}^c([n], \operatorname{LCart}(I))$ as the pullback

$$\begin{array}{c} \operatorname{Fun}^c([n], \operatorname{LCart}(I)) \longrightarrow \operatorname{Fun}([n], \operatorname{LCart}(I)) \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \prod_{k \leq n} \operatorname{LCart}(I^\sharp) \longrightarrow \prod_{k \leq n} \operatorname{Fun}(\{k\}, \operatorname{LCart}(I)) \end{array}$$

where $I^\sharp$ stand for $(I^\sharp)^\sharp$. An object of this $(\infty, 1)$-category is then a sequence in $\operatorname{LCart}(I)$:

$$F_0 \longrightarrow \dots \longrightarrow F_n$$

such that for any integer $i \leq n$, $F_i$ is classified. A 1-cell of this $(\infty, 1)$-category is a sequence of square in $\operatorname{LCart}(I)$:

$$\begin{array}{c} F_0 \longrightarrow \dots \longrightarrow F_n \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ G_0 \longrightarrow \dots \longrightarrow G_n \end{array}$$

such that for any $k \leq n$, the morphism $F_k \to G_k$ comes from a morphism between the corresponding objects of $\operatorname{LCart}(I^\sharp)$.

**Proposition 6.1.3.13.** *Let $F: I \to (\infty, \omega)$-cat$_m$ be a **W**-small diagram. The canonical functor*

$$\operatorname{Fun}^c([n], \operatorname{LCart}(\underset{I}{\operatorname{colim}} F)) \to \lim_I \operatorname{Fun}^c([n], \operatorname{LCart}(F))$$

*is an equivalence.*

*Proof.* This morphism fits in an adjunction:

$$\operatorname{colim}_I: \lim_I \operatorname{Fun}^c([n], \operatorname{LCart}(F)) \xleftrightarrow[\perp]{\perp} \operatorname{Fun}^c([n], \operatorname{LCart}(\operatorname{colim}_I F))$$

The corollary 5.2.2.13 implies that the counit of this adjunction is an equivalence. To conclude, we have to show that the right adjoint is essentially surjective. On objects, this adjunction corresponds to the canonical equivalence

$$\lim_I \operatorname{Hom}([n], \operatorname{LCart}^c(F)) \sim \operatorname{Hom}([n], \operatorname{LCart}^c(\underset{I}{\operatorname{colim}} F))$$

induced by corollary 6.1.2.16

6.1.3.14. As $\mathbf{R}\mathring{\partial}_{0,I}$ is the identity, lemma 6.1.3.6 implies that the functor

$$\operatorname{LCart}((I \otimes [n]^\sharp)^\sharp) \to \operatorname{LCart}(I \otimes [n]^\sharp) \xrightarrow{\mathbf{R}\mathring{\partial}_{n,I}} \operatorname{Fun}([n], \operatorname{LCart}(I))$$

factors through a functor

$$\mathring{\partial}_{n,I}^c: \operatorname{LCart}((I \otimes [n]^\sharp)^\sharp) \to \operatorname{Fun}^c([n], \operatorname{LCart}(I)) \tag{6.1.3.15}$$

We are now willing to show that this functor is an equivalence, and to this extent, we will construct an inverse.

323

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.1.3.16. We fix an object \(a\) of \(t\Theta\). We define \([a,1]^{\sharp} := ([a,1]^{\sharp})^{\sharp}\) and \(\iota\) the canonical inclusion \([a,1] \to [a,1]^{\sharp}\).

We directly have an equivalence

\[
\mathbf {L} \iota_ {!} \mathbf {R} \iota^ {*} \mathbf {F} h _ {1} ^ {[ a ^ {\sharp}, 1 ]} \sim \mathbf {F} h _ {1} ^ {[ a ^ {\sharp}, 1 ]}
\]

The next lemma provides an explicit expression for \(\mathbf{L}\iota_{!}\mathbf{R}\iota^{*}\mathbf{F}h_{0}^{[a^{\sharp},1]}\).

Lemma 6.1.3.17. Let \(a\) be an object of \(t\Theta\). We have an equivalence

\[
\mathbf {L} \iota_ {!} \mathbf {R} \iota^ {*} \mathbf {F} h _ {0} ^ {[ a ^ {\sharp}, 1 ]} \sim \mathbf {F} h _ {0} ^ {[ a ^ {\sharp}, 1 ]} \coprod_ {a ^ {\flat} \otimes \{0 \}} (a \otimes [ 1 ] ^ {\sharp}) ^ {\flat}.
\]

Moreover the morphism \(\mathbf{L}\iota_{!}(a^{\flat}\to \mathbf{F}h_{0}^{[a^{\sharp},1]})\) corresponds to the inclusion

\[
(a \otimes \{0 \}) ^ {\flat} \to (a \otimes [ 1 ] ^ {\sharp}) ^ {\flat} \to \mathbf {F} h _ {0} ^ {[ a ^ {\sharp}, 1 ]} \coprod_ {a ^ {\flat} \otimes \{0 \}} (a \otimes [ 1 ] ^ {\sharp}) ^ {\flat}.
\]

Proof. The theorem 5.2.3.10 implies that \(\iota_{!}\mathbf{R}\iota^{*}\mathbf{F}h_{0}^{[b,1]}\) and \(\iota_{!}\mathbf{R}\iota^{*}\mathbf{F}h_{0}^{(\mathbf{D}_{n})_{t},1]}\) are respectively equivalent to

\[
(1 \stackrel {c o} {\star} b) ^ {\flat} \to [ b, 1 ] ^ {\sharp} \quad \mathrm{and} \quad (1 \stackrel {c o} {\star} \mathbf {D} _ {n}) ^ {\sharp_ {n + 1}} \to [ \mathbf {D} _ {n}, 1 ] ^ {\sharp}
\]

The theorem 5.1.3.24 induces cartesian diagrams

![img-372.jpeg](img-372.jpeg)

![img-373.jpeg](img-373.jpeg)

Remark furthermore that we have an equivalence

\[
\bot (\mathbf {D} _ {n} \otimes [ 1 ]) ^ {\sharp_ {n + 1}} \sim \tau_ {n} ^ {\iota} (\mathbf {D} _ {n} \otimes [ 1 ]) =: ((\mathbf {D} _ {n}) _ {t} \otimes [ 1 ] ^ {\sharp}) ^ {\sharp}.
\]

Applying the full duality to theorem 5.2.3.10 and using the corollary 6.1.2.18, this proves the first assertion.

The second assertion follows from the naturality in E of the construction given in corollary 6.1.2.18 and from the squares

![img-374.jpeg](img-374.jpeg)

![img-375.jpeg](img-375.jpeg)

that are cartesian according to theorem 5.1.3.24.

□

324

6.1. UNIVALENCE

6.1.3.18. We fix an object $a$ of $t\Theta$. Let $E$ be an object of $\mathrm{LCart}([a, 1]^{\sharp})$. According to theorem 6.1.2.15, there exists a morphism $X(0) \times a^{\sharp} \to X(1)$ such that $E$ corresponds to the colimit

$$X(0)^{\flat} \times \mathbf{F} h_{0}^{[a^{\sharp}, 1]} \coprod_{X(0)^{\flat} \times a^{\flat}} X(1)^{\flat}$$

We claim that $\mathbf{L}\iota_{!} \mathbf{R}\iota^{*}E$ is the left cartesian fibration

$$X(0)^{\flat} \times (\mathbf{F} h_{0}^{[a^{\sharp}, 1]} \coprod_{a^{\flat}} (a \otimes [1]^{\sharp})^{\flat}) \coprod_{X(0)^{\flat} \times (a \otimes \{1\})^{\flat}} X(1)^{\flat} \tag{6.1.3.19}$$

Indeed, the lemma 6.1.3.17 provides an initial morphism from $\iota_{!} \mathbf{R}\iota^{*}E$ to this object, and the theorem 5.2.3.3 implies that this object is a left cartesian fibration.

Lemma 6.1.3.20. Let $\psi : \iota_{!} \mathbf{R}\iota^{*} \to \mathbf{L}\iota_{!} \mathbf{R}\iota^{*}$ be a natural transformation, endowed with a family of natural commutative squares:

$$\begin{array}{ccc} \iota_{!} \mathbf{R}\iota^{*}(B^{\flat} \times E) & \xrightarrow{\psi_{B^{\flat} \times E}} & \mathbf{L}\iota_{!} \mathbf{R}\iota^{*}(B^{\flat} \times E) \\ \downarrow & & \downarrow \\ B^{\flat} \times \iota_{!} \mathbf{R}\iota^{*}E & \xrightarrow[B^{\flat} \times \psi_{E}]{} & B^{\flat} \times \iota_{!} \mathbf{R}\iota^{*}E \end{array}$$

where we identify marked $(\infty, \omega)$-categories with their canonical morphisms to the terminal marked $(\infty, \omega)$-category. The natural transformation $\psi$ is then the one obtained by the functorial factorization in initial morphisms followed by left cartesian fibrations.

Proof. The natural transformation $\psi$ induces a natural transformation $\mathbf{D}\psi : \mathbf{L}\iota_{!} \mathbf{R}\iota^{*} \to \mathbf{L}\iota_{!} \mathbf{R}\iota^{*}$ and we have to check that this last natural transformation is the identity. The explicit Grothendieck construction states that $E$ is a colimit of left cartesian fibration of shape $B^{\flat} \times \mathbf{F} h_{\epsilon}^{[a^{\sharp}, 1]}$ for $\epsilon \in \{0, 1\}$. The hypothesis implies that we just have to show that $\mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$ and $\mathbf{D}\psi_{\mathbf{F} h_{1}^{[a^{\sharp}, 1]}}$ are equivalences, and we will check this on fibers.

Using the explicit expression of $\mathbf{L}\iota_{!} \mathbf{R}\iota$ given in (6.1.3.19), we have equivalences

$$\{0\}^{*} \mathbf{L}\iota_{!} \mathbf{R}\iota \mathbf{F} h_{0}^{[a^{\sharp}, 1]} \sim 1 \qquad \{0\}^{*} \mathbf{L}\iota_{!} \mathbf{R}\iota \mathbf{F} h_{1}^{[a^{\sharp}, 1]} \sim \emptyset \qquad \{1\}^{*} \mathbf{L}\iota_{!} \mathbf{R}\iota \mathbf{F} h_{0}^{[a^{\sharp}, 1]} \sim 1$$

which directly implies that $\{0\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$, $\{0\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{1}^{[a^{\sharp}, 1]}}$ and $\{1\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{1}^{[a^{\sharp}, 1]}}$ are equivalences. The only case remaining is $\{1\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$. This morphism corresponds to an endomorphism of $(a \otimes [1]^{\sharp})^{\sharp}$, which is a strict object according to 5.1.3.20. By right cancellation, the morphism induced by the domain of $\mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$ is a left cartesian fibration. There exists then a lift in the following diagram

$$\begin{array}{ccc} \{0\} & \longrightarrow & [a, 1]_{0/}^{\sharp} \coprod_{a^{\flat} \otimes \{0\}} (a \otimes [1]^{\sharp})^{\flat} \\ \downarrow & \longmapsto & \downarrow^{\operatorname{dom} \mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}} \\ [a, 1]_{0/}^{\sharp} & \xrightarrow{\iota} & [a, 1]_{0/}^{\sharp} \coprod_{a^{\flat} \otimes \{0\}} (a \otimes [1]^{\sharp})^{\flat} \end{array} \tag{6.1.3.21}$$

325

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

where \(\iota\) is the canonical inclusion. As \(l\) and \(\iota\) are lifts in the following diagram:

![img-376.jpeg](img-376.jpeg)

they are equivalent. Taking the fiber on \(\{1\}\) of the cartesian square (6.1.3.21), this induces a commutative triangle:

![img-377.jpeg](img-377.jpeg)

Eventually, the naturality induces a commutative squares.

\[
\begin{array}{c} (a \otimes [ 1 ] ^ {\sharp}) ^ {\natural} \longrightarrow (a \otimes \{1 \}) ^ {\natural} \\ \left. \begin{array}{c} \{1 \} ^ {*} \mathbf {D} _ {\mathbf {F} h _ {0} ^ {[ a ^ {\natural}, 1 ]}} \Big \downarrow \\ (a \otimes [ 1 ] ^ {\sharp}) ^ {\natural} \longrightarrow (a \otimes \{1 \}) ^ {\natural} \end{array} \right. \end{array}
\]

The restriction of the morphism \(\mathbf{D}\psi_{\mathbf{F}h_0^{[a^{\sharp},1]}}\) to \(a\otimes \{0\}\) and \(a\otimes \{1\}\) is therefore the identity. Using Steiner theory, we can easily show that it forces \(\mathbf{D}\psi_{\mathbf{F}h_0^{[a^{\sharp},1]}}\) to also be the identity.

6.1.3.22. We fix an object \(F\) of \(\mathrm{LCart}([a,1]^{\sharp})\), and a morphism \(\phi : \mathbf{R}\iota^{*}E \to \mathbf{R}\iota^{*}F\). By adjunction, this corresponds to a morphism \(\tilde{\phi} : \iota_{!}\mathbf{R}\iota^{*}E \to F\), and as \(F\) corresponds to a left cartesian fibration, this induces a morphism \(\mathbf{D}\tilde{\phi} : \mathbf{L}\iota_{!}\mathbf{R}\iota^{*}E \to F\). Using once again theorem 6.1.2.15, this induces a morphism \(\partial_{[a^{\sharp},1]}\mathbf{L}\iota_{!}\mathbf{R}\iota^{*}E \to \partial_{[a^{\sharp},1]}F\), that corresponds, according to the explicit expression of \(\mathbf{L}\iota_{!}\mathbf{R}\iota\) given in (6.1.3.19), to a commutative square

\[
\begin{array}{c} X (0) \times a ^ {\natural} \xrightarrow {\mathbf {D} \tilde {\phi} (0) \times a ^ {\natural}} Y (0) \times a ^ {\natural} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ X (0) \times (a \otimes [ 1 ] ^ {\sharp}) ^ {\natural} \coprod_ {X (0) \times a ^ {\natural}} X (1) \xrightarrow [ \mathbf {D} \tilde {\phi} (1) ]{} Y (1) \end{array}
\]

where \( Y(0) \times a^{\flat} \to Y(1) \) corresponds to \( \partial_{[a^{\flat},1]}F \). This is equivalent to a diagram

![img-378.jpeg](img-378.jpeg)

326

6.1. UNIVALENCE

According to proposition 6.1.1.13, this corresponds to an object \(\xi (\phi)\) of LFib \((\mathrm{N}_{(\omega ,1)}([a,1]\otimes [1]^{\sharp})^{\sharp}))\) endowed with two equivalences:

\[
\partial_ {[ a ^ {\natural}, 1 ]} E \sim \mathrm{N} _ {(\omega , 1)} ([ a, 1 ] \otimes \{0 \}) ^ {*} \xi (\phi) \qquad \partial_ {[ a ^ {\natural}, 1 ]} F \sim \mathrm{N} _ {(\omega , 1)} ([ a, 1 ] \otimes \{1 \}) ^ {*} \xi (\phi)
\]

Using the naturality of \(\int_{C}\) demonstrated in proposition 6.1.2.14, these equivalences induce equivalences:

\[
E \sim ([ a, 1 ] \otimes \{0 \}) ^ {*} \int_ {([ a, 1 ] \otimes [ 1 ] ^ {\sharp}) ^ {\sharp}} \xi (\phi) \quad F \sim ([ a, 1 ] \otimes \{1 \}) ^ {*} \int_ {([ a, 1 ] \otimes [ 1 ] ^ {\sharp}) ^ {\sharp}} \xi (\phi) \tag {6.1.3.24}
\]

All the operations we performed were functorial and admitted inverses. We then have constructed an equivalence

\[
\int_ {([ a, 1 ] \otimes [ 1 ] ^ {\sharp}) ^ {\sharp}} \xi : \operatorname{Fun} ^ {c} ([ 1 ], \operatorname{LCart} ([ a, 1 ])) \rightarrow \operatorname{LCart} (([ a, 1 ] \otimes [ 1 ] ^ {\sharp}) ^ {\sharp}) \tag {6.1.3.25}
\]

Lemma 6.1.3.26. There is a unique commutative square of shape

\[
\begin{array}{c} \iota_ {!} \iota^ {*} E \otimes \{0 \} \longrightarrow E \otimes \{0 \} \\ \Big \downarrow \quad \Big \downarrow \\ \iota_ {!} \iota^ {*} E \otimes i d _ {[ 1 ] ^ {\sharp}} \longrightarrow \int_ {([ a, 1 ] \otimes [ 1 ] ^ {\sharp}) ^ {\sharp}} \xi (\phi) \\ \uparrow \quad \uparrow \\ \iota_ {!} \iota^ {*} E \otimes \{1 \} \longrightarrow F \otimes \{1 \} \end{array} \tag {6.1.3.27}
\]

where the upper horizontal morphism is induced by the unit of the adjunction  \( (\iota_{!},\iota^{*}) \) . Moreover, the bottom horizontal morphism is  \( \tilde{\phi} \) .

Proof. The unicity and existence of the middle horizontal morphism come from the initiality of the morphism  \( \iota_{!}\iota^{*}E\otimes\{0\}\to\iota_{!}\iota^{*}E\otimes[1]^{\sharp} \) . The unicity and existence of the lower horizontal morphism is a consequence of the equation (6.1.3.24). As the diagram (6.1.3.23) factors as

![img-379.jpeg](img-379.jpeg)

327

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

the downer square of the diagram of (6.1.3.27) factors as

$$\begin{array}{ccc} \iota_! \iota^* E \otimes [1]^\sharp & \longrightarrow & \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\mu_E) & \longrightarrow & \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi) \\ \uparrow & & \uparrow & & \uparrow \\ \iota_! \iota^* E \otimes \{1\} & \longrightarrow & \mathbf{L} \iota_! \iota^* E \otimes \{1\} & \xrightarrow[\mathbf{D}\hat{\phi}]{} & F \otimes \{1\} \end{array}$$

where $\mu_E$ denotes the canonical morphism $\iota_! \iota^* E \to \mathbf{L} \iota_! \iota^* E$. To conclude, one has to show that the lower left horizontal morphism is $\mu_E$. As these constructions are natural, and commute with the cartesian product with $B^\flat \to 1$ for $B$ an $(\infty, \omega)$-category, the lemma 6.1.3.20 implies the desired result. $\square$

**Lemma 6.1.3.28.** *The functor $\mathring{\partial}_{1,[a,1]}^c$ defined in (6.1.3.15) in is an equivalence.*

*Proof.* The lemma 6.1.3.26 induces a diagram

$$\begin{array}{ccc} \iota^* E \otimes \mathbf{F} h_1^{[1]} & \longrightarrow & \iota^* E \otimes \mathbf{F} h_0^{[1]} \\ \downarrow & & \downarrow \\ \iota^* F \otimes \mathbf{F} h_1^{[1]} & \longrightarrow & (\iota \otimes i d_{[1]})^* \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi) \end{array}$$

which corresponds to a natural transformation

$$\oint_{1,[a,1]} \phi \to (\iota \otimes i d_{[1]})^* \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi) \quad \longleftrightarrow \quad \phi \to \mathring{\partial}_{1,[a,1]}^c \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi)$$

Eventually, remark that proposition 6.1.3.10 and the equivalences (6.1.3.24) imply that this natural transformation is pointwise an equivalence. The functor (6.1.3.25) is then a left inverse of $\mathring{\partial}_{1,[a,1]}^c$. As it is an equivalence, so is $\mathring{\partial}_{1,[a,1]}^c$. $\square$

**Proposition 6.1.3.29.** *For any marked $(\infty, \omega)$-category $I$, and integer $n$, the morphism*

$$\mathring{\partial}_{n,I}^c : \text{LCart}((I \otimes [n]^\sharp)^\sharp) \to \text{Fun}^c([n], \text{LCart}(I))$$

*defined in (6.1.3.15) is an equivalence.*

*Proof.* Corollary 6.1.2.16, and propositions 5.1.2.1 and 6.1.3.13 imply that the two functors on $\Delta^{op} \times (\infty, \omega)\text{-cat}_m^{op}$:

$$\begin{aligned} (n, I) &\mapsto \text{LCart}^c(I \otimes [n]^\sharp) \\ (n, I) &\mapsto \text{Fun}^c([n], \text{LCart}^c(I)) \end{aligned}$$

send colimits to limits. We can then reduce to the case where $I$ is an element of $t\Theta$ and $n=1$. If $I$ is $[1]^\sharp$, remark that $\mathring{\partial}_{n,[1]^\sharp}^c$ is equivalent to $\mathring{\partial}_{n,[1]^\sharp}$ which is an equivalence according to proposition 6.1.3.11. If $I$ is of shape $[a,1]$ for $a$ in $t\Theta$, this is the content of lemma 6.1.3.28. $\square$

328

6.1. UNIVALENCE

6.1.3.30. We recall that a left cartesian fibration is U-small if its fibers are U-small  \( (\infty,\omega) \) -categories. For an  \( (\infty,\omega) \) -category A, we denote by  \( \mathrm{LCart}_{\mathbf{U}}(A^{\sharp}) \)  the full sub  \( (\infty,1) \) -category of  \( \mathrm{LCart}_{\mathbf{U}}(A^{\sharp}) \)  whose objects correspond to U-small left cartesian fibrations over  \( A^{\sharp} \) . For a marked  \( (\infty,\omega) \) -category I, we define similarly  \( \mathrm{LCart}_{\mathbf{U}}^{c}(I) \)  as the full sub  \( (\infty,1) \) -category of  \( \mathrm{LCart}_{\mathbf{U}}^{c}(I) \)  whose objects correspond to U-small classified left cartesian fibrations over I.

Corollary 6.1.3.31. Let \(\underline{\omega}\) be the V-small \((\infty, \omega)\)-category of U-small \((\infty, \omega)\)-categories. Let \(n\) be an integer and \(I\) be a V-small marked \((\infty, \omega)\)-category. We denote by \(I^{\sharp}\) the marked \((\infty, \omega)\)-category obtained from \(I\) by marking all cells, and \(\iota: I \to I^{\sharp}\) the induced morphism. There is an equivalence, natural in \([n]: \Delta^{op}\) and \(I: (\infty, \omega)\)-cat\(_{\mathrm{m}}^{op}\), between functors

\[
f: I \otimes [ n ] ^ {\sharp} \to \underline {{\omega}} ^ {\sharp}
\]

and sequences

\[
\iota^ {*} \int_ {I ^ {\natural}} f _ {0} \rightarrow \dots \rightarrow \iota^ {*} \int_ {I ^ {\natural}} f _ {n}
\]

where for any \(k \leq n\), \(f_{k}\) is the functor \(I^{\natural} \to \underline{\omega}\) induced by \(I \otimes \{k\} \to I \otimes [n]^{\sharp} \to \underline{\omega}^{\sharp}\).

Proof. This is a direct application of the equivalence

\[
\tau_ {0} \mathrm{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp}) \to \mathrm{Hom} ([ n ], \mathrm{LCart} ^ {c} (I))
\]

induced by proposition 6.1.3.29.

Corollary 6.1.3.32. Let \(I\) be a \(\mathbf{V}\)-small marked \((\infty, \omega)\)-category and \(c\) an object of \(\underline{\omega}\). We denote by \(I^{\sharp}\) the marked \((\infty, \omega)\)-category obtained from \(I\) by marking all cells, and \(\iota: I \to I^{\sharp}\) the induced morphism. There is an equivalence, natural in \(I: (\infty, \omega)\)-cat\(_{\mathrm{m}}^{op}\), between functors

\[
f: I \to \underline {{\omega}} _ {c /} ^ {\sharp}
\]

and arrows:

\[
I \times \int_ {1} c \rightarrow \iota^ {*} \int_ {I ^ {\natural}} \tilde {f}
\]

where \(\tilde{f}\) is the induced functor \(I^{\natural} \to \underline{\omega}_{c/} \to \underline{\omega}\).

Proof. By construction, we have a cocartesian square.

![img-380.jpeg](img-380.jpeg)

As \(\tau_0\mathrm{LCart}(\_)\) sends colimits to limits, this is a consequence of the last corollary.

329

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**Corollary 6.1.3.33.** Let $n$ be an integer, $I$ a $\mathbf{V}$-small marked $(\infty, \omega)$-category, and $A$ an $(\infty, \omega)$-category. We denote by $I^{\sharp}$ the marked $(\infty, \omega)$-category obtained from $I$ by marking all cells, and $\iota : I \to I^{\sharp}$ the induced morphism. There is an equivalence, natural in $[n] : \Delta^{op}$ and $I : (\infty, \omega)\text{-cat}_{\mathrm{m}}^{op}$, between functors

$$f : I \otimes [n]^{\sharp} \to \underline{\mathrm{Hom}}(A, \underline{\omega})$$

and sequences

$$(\iota \times A^{\sharp})^{*} \int_{I^{\natural} \times A} f_{0} \to \dots \to (\iota \times A^{\sharp})^{*} \int_{I^{\natural} \times A} f_{n}$$

where for any $k \leq n$, $f_{k}$ is the functor $I^{\natural} \times A \to \underline{\omega}$ induced by $(I \otimes \{k\}) \times A^{\sharp} \to (I \otimes [n]^{\sharp}) \times A^{\sharp} \to \underline{\omega}^{\sharp}$.

Proof. This is a direct application of the last corollary and the equivalence $(I \otimes [n]^{\sharp}) \times A^{\sharp} \sim (I \times A^{\sharp}) \otimes [n]^{\sharp}$ given in proposition 5.1.2.3. $\square$

**Corollary 6.1.3.34.** Let $I$ be a $\mathbf{V}$-small marked $(\infty, \omega)$-category, $A$ an $(\infty, \omega)$-category, and $g$ an object of $\underline{\mathrm{Hom}}(A, \underline{\omega})$. We denote by $I^{\sharp}$ the marked $(\infty, \omega)$-category obtained from $I$ by marking all cells, and $\iota : I \to I^{\sharp}$ the induced morphism. There is an equivalence, natural in $I : (\infty, \omega)\text{-cat}_{\mathrm{m}}^{op}$, between functors

$$f : I \to \underline{\mathrm{Hom}}(A, \underline{\omega})_{g/}^{\sharp}$$

and arrows:

$$I \times \int_{A} g \to (\iota \times A^{\sharp})^{*} \int_{I^{\natural} \times A} \tilde{f}$$

where $\tilde{f} : I^{\natural} \times A \to \underline{\omega}$ is the functor corresponding to $I^{\natural} \to \underline{\mathrm{Hom}}(A, \underline{\omega})_{g/} \to \underline{\mathrm{Hom}}(A, \underline{\omega})$.

Proof. We once again have a cocartesian square

$$\begin{array}{c} I \otimes \{0\} \longrightarrow I \otimes [1]^{\sharp} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \longrightarrow 1 \stackrel{\infty}{\star} I \end{array}$$

As $\tau_{0}\mathrm{LCart}(\_)$ sends colimits to limits, this is a consequence of the last corollary and the equivalence $(I \otimes [1]^{\sharp}) \times A^{\sharp} \sim (I \times A^{\sharp}) \otimes [1]^{\sharp}$ given in proposition 5.1.2.3. $\square$

### 6.1.4 $(\infty, \omega)$-Functorial Grothendieck construction

**6.1.4.1.** For $I$ a marked $(\infty, \omega)$-category and $A$ an $(\infty, \omega)$-category, we define the $(\infty, \omega)$-category $\underline{\mathrm{Hom}}_{\ominus}(I, A)$, whose value on a globular sum $a$, is given by

$$\mathrm{Hom}(a, \underline{\mathrm{Hom}}_{\ominus}(I, A)) := \mathrm{Hom}(I \ominus a^{\sharp}, A^{\sharp})$$

The section is devoted to the proof of the following theorem:

330

6.1. UNIVALENCE

**Theorem 6.1.4.2.** Let $I$ be a $\mathbf{U}$-small marked $(\infty, \omega)$-category. Let $\underline{\omega}$ be the $\mathbf{V}$-small $(\infty, \omega)$-category of $\mathbf{U}$-small $(\infty, \omega)$-categories, and $\underline{\mathrm{LCart}}_{\mathbf{U}}^{c}(I)$ the $\mathbf{V}$-small $(\infty, \omega)$-category of $\mathbf{U}$-small left cartesian fibrations. There is an equivalence

$$\underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \sim \underline{\mathrm{LCart}}_{\mathbf{U}}^{c}(I)$$

natural in $I$. On the maximal sub $\infty$-groupoid, this equivalence corresponds to the Grothendieck construction of theorem 6.1.2.15.

**Corollary 6.1.4.3.** Let $A$ be a $\mathbf{U}$-small $(\infty, \omega)$-category. Let $\underline{\mathrm{LCart}}_{\mathbf{U}}^{c}(A^{\sharp})$ be the $\mathbf{V}$-small $(\infty, \omega)$-category of $\mathbf{U}$-small left cartesian fibrations. There is an equivalence

$$\underline{\mathrm{Hom}}(A, \underline{\omega}) \sim \underline{\mathrm{LCart}}_{\mathbf{U}}(A^{\sharp})$$

natural in $A$. On the maximal sub $\infty$-groupoid, this equivalence corresponds to the Grothendieck construction of theorem 6.1.2.15.

Proof. This is a consequence of the equivalences $\underline{\mathrm{LCart}}(A^{\sharp}) \sim \underline{\mathrm{LCart}}^{c}(A^{\sharp})$, of the previous theorem and of the equivalence $\underline{\mathrm{Hom}}(A, \underline{\omega}) \sim \underline{\mathrm{Hom}}_{\ominus}(A^{\sharp}, \underline{\omega})$ induced by the second assertion of proposition 5.1.3.16. $\square$

**6.1.4.4.** The previous results provide equivalences

$$\underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \sim \underline{\mathrm{LCart}}^{c}(I) \quad \text{and} \quad \underline{\mathrm{Hom}}(A, \omega) \sim \underline{\mathrm{LCart}}(A^{\sharp})$$

By construction, for any morphism $f : I \to J$ between marked $\omega$-categories, we have a morphism

$$f^{*} : \underline{\mathrm{Hom}}_{\ominus}(J, \underline{\omega}) \to \underline{\mathrm{Hom}}(I, \underline{\omega})$$

Suppose now that the codomain of $f$ is of shape $A^{\sharp}$. The morphism (5.2.5.17) induces a morphism

$$f_{!} : \underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$$

and (5.2.5.18) induces natural transformations:

$$\mu : id \to f^{*}f_{!} \quad \epsilon : f_{!}f^{*} \to id$$

coming along with equivalences: $(\epsilon \circ_{0} f_{!}) \circ_{1} (f_{!} \circ_{0} \mu) \sim id_{f_{!}}$ and $(f^{*} \circ_{0} \epsilon) \circ_{1} (\mu \circ_{0} f^{*}) \sim id_{f^{*}}$. When $f$ is proper, the morphism (5.2.5.27) induces a morphism

$$f_{*} : \underline{\mathrm{Hom}}_{\ominus}(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$$

and (5.2.5.28) induces natural transformations:

$$\mu : id \to f_{*}f^{*} \quad \epsilon : f^{*}f_{*} \to id$$

331

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

coming along with equivalences:  \( (\epsilon \circ_{0} f^{*}) \circ_{1} (f^{*} \circ_{0} \mu) \sim id_{f^{*}} \)  and  \( (f_{*} \circ_{0} \epsilon) \circ_{1} (\mu \circ_{0} f_{*}) \sim id_{f_{*}} \) . Moreover, for every morphism  \( j : C \to D^{\sharp} \) , (5.2.5.20) induces a canonical commutative square

\[
\begin{array}{c} \underline {{\mathrm{Hom}}} _ {\ominus} (D ^ {\sharp} \times I, \underline {{\omega}}) \xrightarrow {(i d _ {D ^ {\sharp}} \times f) !} \underline {{\mathrm{Hom}}} (D \times A, \underline {{\omega}}) \\ (j \times i d _ {I}) ^ {*} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (j \times i d _ {A ^ {\sharp}}) ^ {*} \\ \underline {{\mathrm{Hom}}} _ {\ominus} (C ^ {\sharp} \times I, \underline {{\omega}}) \xrightarrow {(i d _ {C ^ {\sharp}} \times f) !} \underline {{\mathrm{Hom}}} (C \times A, \underline {{\omega}}) \end{array}
\]

and when \( f \) is proper, (5.2.5.30) induces a canonical commutative square

\[
\begin{array}{c} \underline {{\mathrm{Hom}}} _ {\ominus} (D ^ {\sharp} \times I, \underline {{\omega}}) \xrightarrow {(i d _ {D ^ {\sharp}} \times f) _ {*}} \underline {{\mathrm{Hom}}} (D \times A, \underline {{\omega}}) \\ (j \times i d _ {I}) ^ {*} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow (j \times i d _ {A ^ {\sharp}}) ^ {*} \\ \underline {{\mathrm{Hom}}} _ {\ominus} (C ^ {\sharp} \times I, \underline {{\omega}}) \xrightarrow {(i d _ {C ^ {\sharp}} \times f) _ {*}} \underline {{\mathrm{Hom}}} (C \times A, \underline {{\omega}}) \end{array}
\]

##### 6.1.4.5. We now turn our attention back to the proof of the theorem 6.1.4.2.

Lemma 6.1.4.6. Let \(I\) be a marked \((\infty, \omega)\)-category and \(b^{\flat}\) a globular sum. We denote by \(\pi_b: I \times b^{\flat} \to I\) the canonical projection. There is an equivalence of \((\infty, 1)\)-categories:

\[
\operatorname{LCart} (I \times b ^ {\flat}) \sim \operatorname{LCart} (I) _ {/ \pi_ {b}}
\]

Proof. Remark first that we have an equivalence

\[
((\infty , \omega) \text {-cat} _ {\mathrm{m} / I}) _ {/ \pi_ {b}} \sim (\infty , \omega) \text {-cat} _ {\mathrm{m} / I \times b}
\]

Now suppose given a triangle

![img-381.jpeg](img-381.jpeg)

As left cartesian fibrations are stable by composition and right cancellation, and as  \( \pi_{b} \)  is a left cartesian fibration, the diagonal morphism is a left cartesian fibration if and only if the horizontal morphism is.

The \((\infty,1)\)-categories \(\mathrm{LCart}(I)_{/\pi_b}\) and \(\mathrm{LCart}(I\times b^{\flat})\) then identity with the same full sub \((\infty,1)\)-category of \(((\infty,\omega)\text{-cat}_{\mathrm{m}/I})_{/\pi_b}\sim (\infty,\omega)\text{-cat}_{\mathrm{m}/I\times b}\).

Lemma 6.1.4.7. There is a family of cartesian squares

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ([ a \times b, n ] ^ {\sharp}) \longrightarrow \tau_ {0} \mathrm{LCart} ([ a, n ] ^ {\sharp} \times b ^ {\flat}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \mathrm{LCart} (\{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} \mathrm{LCart} (\{k \} \times b ^ {\flat}) \end{array}
\]

natural in \(a, b\) and \(n\).

332

6.1. UNIVALENCE

Proof. Remark first that the proposition 5.1.3.23 provides cocartesian squares:

![img-382.jpeg](img-382.jpeg)

![img-383.jpeg](img-383.jpeg)

According to the corollary 6.1.2.16, and proposition 6.1.3.29, and as \(\mathbf{R}(\pi_{-})_{!}:\mathrm{LCart}(1)\to\) \(\mathrm{LCart}_{(-}^{\flat})\) factors through \(\mathrm{LCart}^c (\_ ^b)\), this induces cartesian squares:

![img-384.jpeg](img-384.jpeg)

![img-385.jpeg](img-385.jpeg)

For a marked  \( (\infty,\omega) \) -category I, we denote  \( \pi_{b}:I\times b\to I \)  the canonical projection. As the  \( (\infty,1) \) -categorical slice and the maximal full sub  \( \infty \) -groupoid preserve cartesian squares, the second cartesian square induces a cartesian square

![img-386.jpeg](img-386.jpeg)

and according to lemma 6.1.4.6, this corresponds to a cartesian square

![img-387.jpeg](img-387.jpeg)

Combined with the first cartesian square of (6.1.4.8), this induces a commutative diagram

![img-388.jpeg](img-388.jpeg)

where the right and the outer square are cartesian. By right cancellation, the left square is cartesian which concludes the proof.

□

333

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Lemma 6.1.4.9. Let \( b \) be a globular sum and let \( F: I \to (\infty, \omega) \)-cat be a \( \mathbf{W} \)-small diagram. The canonical morphism

\[
\operatorname{LCart} (\underset {I} {\operatorname{colim}} F ^ {\sharp} \times b ^ {\flat}) \to \underset {I} {\lim} \operatorname{LCart} (F ^ {\sharp} \times b ^ {\flat})
\]

is an equivalence.

Proof. The corollary 6.1.2.16 implies that the canonical morphism

\[
\operatorname{LCart} (\underset {I} {\operatorname{colim}} F ^ {\sharp}) \to \underset {I} {\lim} \operatorname{LCart} (F ^ {\sharp})
\]

is an equivalence. We recall that for any  \( (\infty,\omega) \) -category A, we denote by  \( \pi_{b}:A^{\sharp}\times b^{\flat}\to A^{\sharp} \)  the canonical projection. As the  \( (\infty,1) \) -categorical slice preserves limits, the previous equivalence induces an equivalence

\[
\operatorname{LCart} (\underset {I} {\operatorname{colim}} F ^ {\sharp}) _ {/ \pi_ {b}} \to \underset {I} {\lim} \operatorname{LCart} (F ^ {\sharp}) _ {/ \pi_ {b}}.
\]

The results then follows from lemma 6.1.4.6.

Lemma 6.1.4.10. There is a family of cartesian squares

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \longrightarrow \tau_ {0} \mathrm{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp} \times b ^ {\flat}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \mathrm{LCart} (I ^ {\sharp} \otimes \{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} \mathrm{LCart} ((I ^ {\sharp} \otimes \{k \}) \times b ^ {\flat}) \end{array}
\]

natural in I, b and n.

Proof. By definition,  \( (I \ominus [b, n]^{\sharp})^{\sharp} \)  fits in the following cartesian square:

\[
\begin{array}{c} \operatorname{colim} _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} [ a \times b, m ] ^ {\sharp} \longrightarrow \operatorname{colim} _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} [ a, m ] ^ {\sharp} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{colim} _ {[ a, m ] \to (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} [ a \times b, m ] ^ {\sharp} \longrightarrow (I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp} \end{array}
\]

Combined with corollary 6.1.2.16, this implies that the \(\infty\)-groupoid \(\tau_0\mathrm{LCart}((I\ominus [b,n]^{\sharp})^{\sharp})\) fits in the cartesian square:

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ^ {c} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \lim _ {[ a, m ] \to (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a \times b, m ] ^ {\sharp}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a \times b, m ] ^ {\sharp}) \end{array}
\]

334

6.1. UNIVALENCE

Applying lemma 6.1.4.7, and the fact that any morphism \(\{l\} \to [a,m] \to (I \otimes [n]^{\sharp})^{\sharp}\) uniquely factors through \(\coprod_k I^\sharp \otimes \{k\}\), we get a cartesian square

\[
\begin{array}{c} \tau_ {0} \mathrm{LCart} ^ {c} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \lim _ {[ a, m ] \to (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \xrightarrow {} \lim _ {[ a, m ] \to \Pi_ {k} I ^ {\sharp} \otimes \{k \}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \end{array}
\]

Eventually, the lemma 6.1.4.9 induces equivalences

\[
\begin{array}{l} \lim _ {[ a, m ] \rightarrow (I \otimes [ n ] ^ {\sharp}) ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \sim \tau_ {0} \mathrm{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp} \times b ^ {\flat}) \\ \lim _ {[ a, m ] \to I ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp} \times b ^ {\flat}) \sim \tau_ {0} \mathrm{LCart} (I ^ {\sharp} \times b ^ {\flat}) \\ \lim _ {[ a, m ] \to I ^ {\sharp}} \tau_ {0} \mathrm{LCart} ([ a, m ] ^ {\sharp}) \sim \tau_ {0} \mathrm{LCart} (I ^ {\sharp}) \\ \end{array}
\]

This concludes the proof.

Lemma 6.1.4.11. There is a family of cartesian squares

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \tau_ {0} \operatorname{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp} \times b ^ {\flat}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} (I ^ {\sharp} \otimes \{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} ((I ^ {\sharp} \otimes \{k \}) \times b ^ {\flat}) \end{array}
\]

natural in \(I, b\) and \(n\).

Proof. By the construction of \(\mathrm{LCart}^c (I;b)\), we have a cartesian square

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \operatorname{Hom} ([ n ], \operatorname{LCart} (I \times b ^ {\flat})) \\ \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} ^ {c} (I) \longrightarrow \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} (I \times b ^ {\flat}) \end{array}
\]

According to lemma 6.1.4.6, this induces a cartesian square

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \operatorname{Hom} ([ n ], \operatorname{LCart} (I) _ {/ \pi_ {b}}) \\ \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} ^ {c} (I) \longrightarrow \prod_ {k \leq n} \tau_ {0} (\operatorname{LCart} (I) _ {/ \pi_ {b}}) \end{array}
\]

As the functor \(\mathrm{LCart}^c (I)\to \mathrm{LCart}(I)_{/\pi_b}\) factors through \(\mathrm{LCart}^c (I)_{/\pi_b}\), the proposition 6.1.3.29 induces a cartesian square

\[
\begin{array}{c} \operatorname{Hom} ([ n ], \operatorname{LCart} ^ {c} (I; b)) \longrightarrow \tau_ {0} (\operatorname{LCart} ((I \otimes [ n ] ^ {\sharp}) ^ {\sharp}) _ {/ \pi_ {b}}) \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \prod_ {k \leq n} \tau_ {0} \operatorname{LCart} (I ^ {\sharp} \otimes \{k \}) \longrightarrow \prod_ {k \leq n} \tau_ {0} (\operatorname{LCart} (I ^ {\sharp} \otimes \{k \}) _ {/ \pi_ {b}}) \end{array}
\]

Eventually, a last application of lemma 6.1.4.6 concludes the proof.

335

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**Lemma 6.1.4.12.** *There is an equivalence*

$$\tau_0(\mathrm{LCart}((I \ominus [b, n]^\sharp)^\sharp) \sim \mathrm{Hom}([n], \mathrm{LCart}^c(I; b))$$

*natural in $I : (\infty, \omega)$-cat$_\mathrm{m}^{op}$, $b : \Theta^{op}$ and $[n] : \Delta^{op}$.*

*Proof.* This is a direct consequence of lemmas 6.1.4.10 and 6.1.4.11.

*Proof of theorem 6.1.4.2.* Lemma 6.1.4.12 provides an natural equivalence

$$\tau_0(\mathrm{LCart}((I \ominus [b, n]^\sharp)^\sharp) \sim \mathrm{Hom}([n], \mathrm{LCart}^c(I; b))$$

that preserves smallness.

## 6.2 Yoneda lemma and applications

### 6.2.1 Yoneda lemma

**6.2.1.1.** An $(\infty, \omega)$-category $C$ is *locally* **U-small** if for any pair of objects $x$ and $y$, $\mathrm{hom}_C(x, y)$ is **U-small**.

**Example 6.2.1.2.** For all **U-small** $(\infty, \omega)$-category $A$, the corollary 6.1.4.3 provides an equivalence

$$\mathrm{hom}_{\underline{\mathrm{Hom}}(A, \underline{\omega})}(f, g) \sim \mathrm{Map}(\int_A f, \int_A g)$$

As $\int_A f$ and $\int_A g$ are **U-small** left cartesian fibrations over a **U-small** basis, their codomains are **U-small** and $\mathrm{Map}(\int_A f, \int_A g)$ is then **U-small**. The $(\infty, \omega)$-category $\underline{\mathrm{Hom}}(A, \underline{\omega})$ is then locally **U-small**.

We can generalize this example as follow:

**Proposition 6.2.1.3.** *Let $A$ be a **U-small** $(\infty, \omega)$-category, and $C$ is a locally **U-small** $(\infty, \omega)$-category. The $(\infty, \omega)$-category $\underline{\mathrm{Hom}}(A, C)$ is locally **U-small**.*

*Proof.* We have to check that for any globular sum $b$, the morphism

$$\mathrm{Hom}(A \times [b, 1], C) \to \mathrm{Hom}(A \times (\{0\} \amalg \{1\}), C)$$

has **U-small** fibers. As $A$, seen as an $\infty$-presheaves on $\Theta$, is a **U-small** colimit of representables, we can reduce to the case where $A \in \Theta$. As $C$ is local with respect to Segal extensions, and as the cartesian product conserves them, we can reduce to the case where $A$ is of shape $[a, 1]$ for $a$ a globular sum. We now fix a morphism $f : [a, 1] \times (\{0\} \amalg \{1\}) \to C$.

336

6.2. YONEDA LEMMA AND APPLICATIONS

Eventually, using the canonical equivalence between $[a, 1] \times [b, 1]$ and the colimit of the span

$$[a, 1] \vee [b, 1] \leftarrow [a \times b, 1] \rightarrow [b, 1] \vee [a, 1],$$

the $\infty$-groupoid $\operatorname{Hom}([a, 1] \times [b, 1], C)_f$ fits in a cartesian square:

$$\begin{array}{c} \operatorname{Hom}([a, 1] \times [b, 1], C)_f \longrightarrow \operatorname{Hom}(b, \operatorname{hom}(f(0, 0), f(0, 1))) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \operatorname{Hom}(b, \operatorname{hom}(f(1, 0), f(1, 1))) \longrightarrow \operatorname{Hom}(a \times b, \operatorname{hom}(f(0, 0), f(1, 1))) \end{array}$$

As all these objects are $\mathbf{U}$-small by assumption, this concludes the proof.

**6.2.1.4.** Let $C$ be an $(\infty, \omega)$-category $C$. We define the simplicial object $S(\mathrm{N}_{(\omega, 1)} C)$ by the formula

$$S(\mathrm{N}_{(\omega, 1)} C)_n := \coprod_{x_0, \dots, x_n : A_0} \coprod_{y_0, \dots, y_n : A_0} \operatorname{hom}_C(x_n, \dots, x_0, y_0, \dots, y_n)$$

This object comes along with a canonical projection

$$S(\mathrm{N}_{(\omega, 1)} C) \rightarrow \mathrm{N}_{(\omega, 1)} C^t \times \mathrm{N}_{(\omega, 1)} C. \tag{6.2.1.5}$$

which obviously is a left fibration. As this construction if functorial, it induces a functor:

$$\begin{array}{l} (\infty, \omega)\text{-cat} \rightarrow \operatorname{Arr}((\infty, \omega, 1)\text{-cat}) \\ C \mapsto (S(\mathrm{N}_{(\omega, 1)} C) \rightarrow \mathrm{N}_{(\omega, 1)} C^t \times \mathrm{N}_{(\omega, 1)} C) \end{array}$$

**6.2.1.6.** Through this section, we fix a locally $\mathbf{U}$-small $(\infty, \omega)$-category $C$. The left fibration (6.2.1.5) is then $\mathbf{U}$-small, and by definition of $\underline{\omega}$, this induces a morphism

$$\operatorname{hom}_C(\_, \_): C^t \times C \rightarrow \underline{\omega} \tag{6.2.1.7}$$

Using the canonical equivalence

$$\mathbf{F} h_{(x, y)}^{C^t \times C} \sim \mathbf{F} h_x^{C^t} \times \mathbf{F} h_y^C$$

the corresponding left cartesian fibration is then the colimit of a simplicial object whose value on $n$ is given by:

$$\coprod_{x_0, \dots, x_n} \coprod_{y_0, \dots, y_n} \mathbf{F} h_{x_n}^{C^t} \times \operatorname{hom}_C(x_n, \dots, x_0, y_0, \dots, y_n)^b \times \mathbf{F} h_{y_n}^C$$

337

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.2.1.8. We define the  \( (\infty,\omega) \) -category of  \( (\infty,\omega) \) -presheaves on C :

\[
\widehat {C} := \underline {{\mathrm{Hom}}} (C ^ {t}, \underline {{\omega}}).
\]

This \((\infty, \omega)\)-category is locally \(\mathbf{U}\)-small according to proposition 6.2.1.3. The Yoneda embedding \(y: C \to \widehat{C}\) is the functor induced by the hom functor (6.2.1.7) by currying.

An  \( (\infty,\omega) \) -presheaves is representable if it is in the image of y.

6.2.1.9. We recall that for a subset S of  \( N^{*} \) , and an object X of  \( (\infty,\omega,1) \) -cat, we denote by  \( X^{S} \)  the simplicial object  \( n\mapsto X_{n}^{S} \) . We also set  \( \Sigma S:=\{i+1,i\in S\} \) . We then have equivalences

\[
(\mathrm{N} _ {(\omega , 1)} C) ^ {S} \sim \mathrm{N} _ {(\omega , 1)} (C ^ {\Sigma C}) \quad \mathrm{and} \quad S (\mathrm{N} _ {(\omega , 1)} C)) ^ {S} \sim S (\mathrm{N} _ {(\omega , 1)} (C ^ {\Sigma C}))
\]

For an object \( X \) of \( (\infty, \omega, 1) \)-cat, we denote by \( X_{op} \) the simplicial object \( n \mapsto X_{n^{op}} \). We then have equivalences

\[
(\mathrm{N} _ {(\omega , 1)} C) _ {o p} \sim \mathrm{N} _ {(\omega , 1)} (C ^ {t}) \quad \mathrm{and} \quad S (\mathrm{N} _ {(\omega , 1)} C)) _ {o p} \sim S (\mathrm{N} _ {(\omega , 1)} (C ^ {t}))
\]

Using the dualities defined in paragraph 6.1.1.20, we then have commutative diagrams

![img-389.jpeg](img-389.jpeg)

![img-390.jpeg](img-390.jpeg)

where tw is the functor exchanging the argument. This two diagram corresponds to the natural transformations

\[
\hom_ {C ^ {\Sigma S}} (x, y) \sim \hom_ {C} (x, y) ^ {S} \quad \mathrm{and} \quad \hom_ {C ^ {t}} (x, y) \sim \hom_ {C} (y, x).
\]

In combining the two previous diagrams, we get a commutative square:

![img-391.jpeg](img-391.jpeg)

corresponding to the natural transformation

\[
\hom_ {C ^ {\circ}} (x, y) \sim \hom_ {C} (y, x) ^ {\circ}.
\]

338

6.2. YONEDA LEMMA AND APPLICATIONS

Proposition 6.2.1.10. Let A be an locally U-small  \( (\infty,\omega) \) -category. Let a be an object of A. There is an equivalence

\[
\int_ {A} \hom_ {A} (a, \_) \to \mathbf {F} h _ {a} ^ {A}
\]

Taking the fibers on \(a\), the induced morphism \(\mathrm{hom}_A(a,a) \to \mathrm{hom}_A(a,a)\) preserves the identity. In particular, for any object \(c\) of \(C\), this induces an equivalence

\[
\int_ {C ^ {t}} y _ {c} \rightarrow \mathbf {F} h _ {c} ^ {C ^ {t}}
\]

Proof. By construction, \(\int_{A} \mathrm{hom}_{A}(a, \underline{\quad})\) is the Grothendieck construction of the left fibration:

\[
\begin{array}{l} \dots \quad \coprod_ {x _ {0}, x _ {1}, x _ {2}: A _ {0}} \hom_ {A} (a, x _ {0}, x _ {1}, x _ {2}) \stackrel {{\leftrightarrow}} {{\underset {\leftrightarrow} {\longrightarrow}}} \coprod_ {x _ {0}, x _ {1}: A _ {0}} \hom_ {A} (a, x _ {0}, x _ {1}) \stackrel {{\leftrightarrow}} {{\underset {\leftrightarrow} {\longrightarrow}}} \coprod_ {x _ {0}: A _ {0}} \hom_ {A} (a, x _ {0}) \\ \begin{array}{c c c c} \Big \downarrow & & \Big \downarrow & \\ \dots & \coprod_ {x _ {0}, x _ {1}, x _ {2}: A _ {0}} \hom_ {A} (x _ {0}, x _ {1}, x _ {2}) & \stackrel {{\longrightarrow}} {{\longleftrightarrow}} \coprod_ {x _ {0}, x _ {1}: A _ {0}} \hom_ {A} (x _ {0}, x _ {1}) & \stackrel {{\longleftrightarrow}} {{\longleftrightarrow}} \coprod_ {x _ {0}: A _ {0}} 1 \end{array} \\ \end{array}
\]

The results then follow from the corollary 6.1.2.17.

□

6.2.1.11. The identity \(\widehat{C} \to \widehat{C}\) induces by currying a canonical morphism

\[
\operatorname{ev}: C ^ {t} \times \widehat {C} \to \underline {{\omega}}
\]

called the evaluation functor. Given an object \(c\) of \(C\) and \(f\) of \(\widehat{C}\), we then have \(\mathrm{ev}(c, f) \sim f(c)\) and so

\[
(c, \{f \}) ^ {*} \int_ {C \times \widehat {C}} \mathrm{ev} \sim c ^ {*} \int_ {C ^ {t}} f
\]

Let \(E\) be an object of \((\infty, \omega)\)-\(\mathrm{cat}_{\mathrm{m} / \widehat{C}^{\sharp}}\) corresponding to a morphism \(g: X \to \widehat{C}^{\sharp}\). We denote \(\iota: X \to X^{\sharp}\) the canonical inclusion. A morphism

\[
E \rightarrow \int_ {\widehat {C}} \mathrm{ev} (c, \_)
\]

corresponds by adjunction to a morphism

\[
i d _ {X} \rightarrow g ^ {*} \int_ {\widehat {C}} \mathrm{ev} (c, \_) \tag {6.2.1.12}
\]

However, we have a canonical commutative square

\[
\begin{array}{c} X ^ {\sharp} \xrightarrow {g ^ {\sharp}} \widehat {C} \\ X ^ {\sharp} \times \{c \} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \mathrm{ev} (c, \_) \\ X ^ {\sharp} \times C ^ {t} \xrightarrow [ \widehat {g} ]{} \underline {{\omega}} \end{array}
\]

339

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

where \(\tilde{g}\) is the morphism defined by currying from \(g^{\sharp}: X^{\sharp} \to \widehat{C}\). Using the naturality of the Grothendieck construction, the previous commutative square implies that the data of (6.2.1.12) corresponds to a morphism

\[
i d _ {X} \rightarrow (\iota \times \{c \}) ^ {*} \int_ {X ^ {\natural} \times C ^ {t}} \tilde {g}
\]

an by adjunction, to a morphism

\[
X \times \mathbf {F} h _ {c} ^ {C ^ {t}} \rightarrow (\iota \times (C ^ {t}) ^ {\sharp}) ^ {*} \int_ {X ^ {\natural} \times C ^ {t}} \tilde {g}
\]

We then have constructed an equivalence

\[
\operatorname{Hom} (E, \int_ {\widehat {C}} \mathrm{ev} (c, \_) \sim \operatorname{Hom} (X \times \mathbf {F} h _ {c} ^ {C ^ {t}}, (\iota \times (C ^ {t}) ^ {\sharp}) ^ {*} \int_ {X ^ {\natural} \times C ^ {t}} \tilde {g}) \tag {6.2.1.13}
\]

natural in \(E\).

Remark furthermore that if \( E \) is \( h_f^{\widehat{C}} \) for \( f \) an object of \( \widehat{C} \), the equivalence corresponds to the canonical equivalences

\[
\begin{array}{l} \mathrm{Hom} _ {(\infty , \omega) \text {-cat} _ {\mathrm{m} / \widehat {C} ^ {\sharp}}} (h _ {f} ^ {\widehat {C}}, \int_ {\widehat {C}} \mathrm{ev} (c, \_) \sim \mathrm{Hom} _ {(\infty , \omega) \text {-cat} _ {\mathrm{m}}} (1, \{f \} ^ {*} \int_ {\widehat {C}} \mathrm{ev} (c, \_) \\ \sim \mathrm{Hom} _ {(\infty , \omega) \text {-cat} _ {\mathrm{m}}} (1, c ^ {*} \int_ {C ^ {t}} f) \\ \sim \mathrm{Hom} _ {(\infty , \omega) \text {-cat} _ {\mathrm{m} / (C ^ {t}) ^ {\sharp}}} (\mathbf {F} h _ {c} ^ {C ^ {t}}, \int_ {C ^ {t}} f) \\ \end{array}
\]

Proposition 6.2.1.14. For any object \( c \) of \( C \), there exists a unique pair consisting of a morphism

\[
\int_ {\widehat {C}} \mathrm{hom} _ {\widehat {C}} (y _ {c}, \_) \rightarrow \int_ {\widehat {C}} \mathrm{ev} (c, \_)
\]

and a commutative square of shape

\[
\begin{array}{c} \left\{i d _ {y _ {c}} \right\} \longrightarrow \hom_ {\widehat {C}} \left(y _ {c}, y _ {c}\right) \sim \left\{y _ {c} \right\} ^ {*} \int_ {\widehat {C}} \hom_ {\widehat {C}} \left(y _ {c}, \_ \right) \\ \Big \| \quad \Big \downarrow \\ \left\{i d _ {c} \right\} \longrightarrow \hom_ {C} (c, c) \sim \left\{y _ {c} \right\} ^ {*} \int_ {\widehat {C}} \operatorname{ev} (c, \_) \end{array} \tag {6.2.1.15}
\]

Moreover, this comparison morphism is an equivalence.

Proof. The proposition 6.2.1.10 implies that \(\int_{\widehat{C}}\mathrm{hom}_{\widehat{C}}(y_c,\_)\) is equivalent to \(\mathbf{F}h_{y_c}^{\widehat{C}}\). A natural transformation \(\int_{\widehat{C}}\mathrm{hom}_{\widehat{C}}(y_c,\_) \to g\) then corresponds to a morphism \(\mathbf{F}h_{y_c}^{\widehat{C}} \to \int_{\widehat{C}}g\) and is then uniquely characterized by the value on \(\{id_{y_c}\}\), which proves the uniqueness.

It remains to show the existence. Let \( E \) be an object of \( (\infty, \omega) \)-cat\(_{\mathrm{m} / \widehat{C}^{\sharp}}\) corresponding to a morphism \( g: X \to \widehat{C}^{\sharp} \). We denote \( \iota: X \to X^{\sharp} \) the canonical inclusion. According to proposition 6.2.1.10, a morphism \( E \to \int_{\widehat{C}} \mathrm{hom}_{\widehat{C}}(y_c, \_) \) corresponds to a morphism \( E \to \mathbf{F}h_{y_c}^{\widehat{C}} \), and so to a triangle

![img-392.jpeg](img-392.jpeg)

340

6.2. YONEDA LEMMA AND APPLICATIONS

According to corollary 6.1.3.34, this data is equivalent to the one of

$$X \times \int_{C^{\iota}} y_{c} \to (\iota \times (C^{\iota})^{\sharp})^{*} \int_{X^{\sharp} \times C^{\iota}} \tilde{g}$$

where $\tilde{g}$ is the morphism defined by currying from $g^{\sharp}: X^{\sharp} \to \widehat{C}$. The proposition 6.2.1.10, and the equivalence (6.2.1.13) then induce an equivalence:

$$\mathrm{Hom}_{(\infty, \omega) \circ \mathrm{cat}_{\mathrm{m} / \widehat{C}^{\sharp}}}(E, \int_{\widehat{C}} \mathrm{hom}_{\widehat{C}}(y_{c}, \underline{\hspace{1cm}})) \sim \mathrm{Hom}_{(\infty, \omega) \circ \mathrm{cat}_{\mathrm{m} / \widehat{C}^{\sharp}}}(E, \int_{\widehat{C}} \mathrm{ev}(c, \underline{\hspace{1cm}}))$$

Walking through all the equivalences, we can easily see that when $E$ is $h_{y_{c}}^{\widehat{C}}$, this equivalence sends the upper horizontal morphism of (6.2.1.15) to the lower horizontal one. We then have an equivalence

$$\int_{\widehat{C}} \mathrm{hom}_{\widehat{C}}(y_{c}, \underline{\hspace{1cm}}) \sim \int_{\widehat{C}} \mathrm{ev}(c, \underline{\hspace{1cm}}).$$

that comes along with the desired commutative square.

**Theorem 6.2.1.16.** *The Yoneda embedding is fully faithful. As a consequence, every morphism $A \to \widehat{C}$ that is pointwise representable uniquely factors through the Yoneda embedding.*

*Proof.* We fix an object $c$ of $C$. By construction of the Yoneda embedding and the evaluation, we have an equivalence $\mathrm{ev}(c, y_{d}) \sim \mathrm{hom}_{C}(c, d)$ natural in $d: C$. Applying the Grothendieck deconstruction to the equivalence given in proposition 6.2.1.14, we then get an equivalence

$$\eta_{d}: \mathrm{hom}_{\widehat{C}}(y_{c}, y_{d}) \sim \mathrm{hom}_{C}(c, d)$$

natural in $d: C$ and that preserves the identity.

We also have a transformation

$$\mathrm{hom}_{y}(c, d): \mathrm{hom}_{C}(c, d) \to \mathrm{hom}_{\widehat{C}}(y_{c}, y_{d})$$

natural in $d: C$, that also preserves the identity. We then have constructed a natural transformation

$$\psi_{c, d}: \mathrm{hom}_{C}(c, d) \xrightarrow{\mathrm{hom}_{y}(c, d)} \mathrm{hom}_{\widehat{C}}(y_{c}, y_{d}) \xrightarrow{\eta_{d}} \mathrm{hom}_{C}(c, d)$$

natural in $d: C$, and which preserves the identity. As the Grothendieck construction of $\mathrm{hom}_{C}(c, \underline{\hspace{1cm}})$ is $\mathbf{F}h_{c}^{C}$ according to proposition 6.2.1.10, the morphism

$$\int_{C} \psi_{c}: \mathbf{F}h_{c}^{C} \to \mathbf{F}h_{c}^{C}$$

is characterized by its value on $\{id_{c}\}$ and is then the identity. This implies that $\psi_{c}$ is the identity. By two out of three, this implies that $\mathrm{hom}_{y}(c, \underline{\hspace{1cm}})$ also is an equivalence, which concludes the proof.

341

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Lemma 6.2.1.17. Let \(i: C \to D\) be a morphism between locally \(\mathbf{U}\)-small \((\infty, \omega)\)-categories. The canonical morphism of \(\mathrm{LCart}((C^t)^\sharp \times D^\sharp)\):

\[
\mathbf {L} (i d \times i)! \int_ {C ^ {t} \times C} \hom_ {C} \rightarrow \int_ {C ^ {t} \times D} \hom_ {D} (i (\_, \_)
\]

is an equivalence.

Proof. Let \( c, d \) be any objects of respectively \( C \) and \( D \). We then have equivalences

\[
\mathbf {R} (c, d) ^ {*} \mathbf {L} (i d \times i)! \int_ {C ^ {t} \times C ^ {t}} \hom_ {C} \sim \mathbf {R} \{d \} ^ {*} \mathbf {L} i _ {!} \mathbf {R} (i d \times \{c \}) ^ {*} \int_ {C ^ {t} \times C} \hom_ {C} \tag {5.2.4.24}
\]

\[
\sim \quad \mathbf {R} \{d \} ^ {*} \mathbf {L} i _ {!} \mathbf {F} h _ {c} ^ {C} \tag {6.2.1.10}
\]

\[
\sim \mathbf {R} \{d \} ^ {*} \mathbf {F} h _ {i (c)} ^ {D}
\]

\[
\sim \hom_ {D} (i (c), d) ^ {\flat}
\]

Remark that we also have an equivalence

\[
\mathbf {R} (c, d) ^ {*} \int_ {C ^ {t} \times D} \hom_ {D} (i (\_, \_) \sim \hom_ {D} (i (c), d) ^ {\flat}
\]

and that the induced endomorphism of \(\mathrm{hom}_D(i(c),d)^b\) is the identity. As equivalences are detected pointwise, this concludes the proof.

Theorem 6.2.1.18. Let \( C \) be a locally \( \mathbf{U} \)-small \( (\infty, \omega) \)-category. There is an equivalence between the functor

\[
\hom_ {\widehat {C}} (y _ {\_, \_}): C ^ {t} \times \widehat {C} \to \underline {{\omega}}
\]

and the functor

\[
\operatorname{ev}: C ^ {t} \times \widehat {C} \to \underline {{\omega}}.
\]

Restricted to \(\widehat{C} \times \{c\}\) for \(c\) an object of \(C\), this equivalence is the one of proposition 6.2.1.14.

Proof. The triangle

![img-393.jpeg](img-393.jpeg)

induces by adjunction a triangle

![img-394.jpeg](img-394.jpeg)

This corresponds to an equivalence

\[
\int_ {C ^ {t} \times C} \hom_ {C} (\_, \_) \rightarrow (i d \times y) ^ {*} \int_ {C ^ {t} \times \widehat {C}} \mathrm{ev}.
\]

342

6.2. YONEDA LEMMA AND APPLICATIONS

By naturality, for any object $c$ of $C$, the pullback of the previous equivalence along $C^t \times \{c\}$ is the identity. In particular, the induced morphism $\hom(c, c) \to \hom(c, c)$ between the fibers over $(c, c)$ preserves the object $\{id_c\}$. According to lemma 6.2.1.17, the previous equivalence induces a morphism

$$\int_{C^t \times \widehat{C}} \hom_{\widehat{C}}(y_-, \_) \to \int_{C^t \times \widehat{C}} \mathrm{ev} \, . \tag{6.2.1.19}$$

that comes along, by construction, with a commutative square

$$\begin{array}{c} \{id_{y_c}\} \longrightarrow \hom_{\widehat{C}}(y_c, y_c) \sim \{y_c\}^* \int_{\widehat{C}} \hom_{\widehat{C}}(y_c, \_) \\ \Big\| \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big\downarrow \\ \{id_c\} \longrightarrow \hom_C(c, c) \sim \{y_c\}^* \int_{\widehat{C}} \mathrm{ev}(c, \_) \end{array}$$

for any object $c$ of $C$. The restriction of the morphism (6.2.1.19) to $\widehat{C} \times \{c\}$ is then equivalent to the natural transformation given in proposition 6.2.1.14, and is an equivalence. As equivalences between left cartesian fibrations are detected on fibers, this concludes the proof.

**Corollary 6.2.1.20.** *The universal left cartesian fibration with U-small fibers is the canonical projection $\underline{\omega}_{1/}^\sharp \to \underline{\omega}^\sharp$.*

*Proof.* The corollary 6.2.1.20 implies that universal left cartesian fibration with U-small fibers is $\int_{\underline{\omega}} id$. The Yoneda lemma implies that this left cartesian fibration is equivalent to $\int_{\underline{\omega}} \hom_{\underline{\omega}}(1, \_)$. Eventually, the proposition 6.2.1.10 states that this left cartesian fibration is equivalent to $\underline{\omega}_{1/}^\sharp \to \underline{\omega}^\sharp$.

### 6.2.2 Adjoint functors

**Definition 6.2.2.1.** Let $C$ and $D$ be two locally U-small $(\infty, \omega)$-categories and $u : C \to D$, $v : D \to C$ two functors. An *adjoint structure* for the pair $(u, v)$ is the data of a invertible natural transformation

$$\phi : \hom_D(u(\_), \_) \sim \hom_C(\_, v(\_))$$

In this case, $u$ is a *left adjoint* of $v$ and $v$ is a *right adjoint* of $u$.

**Proposition 6.2.2.2.** *Let $u : C \to D$ be a functor between locally U-small $(\infty, \omega)$-categories. For $b$ an object of $D$, we define $(C^t)_{b/}^\sharp$ and $C_{b/}^\sharp$ as the marked $(\infty, \omega)$-categories fitting in the cartesian squares:*

$$\begin{array}{ccc} (C^t)_{/b}^\sharp & \longrightarrow & (D^t)_{b/}^\sharp & C_{b/}^\sharp \longrightarrow D_{b/}^\sharp \\ \downarrow & \downarrow & \downarrow & \downarrow \\ (C^t)^\sharp & \xrightarrow{u^t} & (D^t)^\sharp & C^\sharp \xrightarrow{u} D^\sharp \end{array}$$

343

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

The following are equivalent.

(1) The functor \( u \) admits a right adjoint.
(2) For any element \( b \) of \( D \), the marked \( (\infty, \omega) \)-category \( (C^t)_{b/}^{\sharp} \) admits an initial element.

Similarly, the following are equivalent.

(1)' The functor \( u \) admits a left adjoint.
(2)' For any element \( b \) of \( D \), \( C_{b/}^{\sharp} \) admits an initial element.

Proof. Suppose first that (1) is fulfilled, and let  \( v : D \to C \)  be a functor and  \( \phi : \hom(u(a), b) \sim \hom(a, v(b)) \)  be an invertible natural transformation. In particular, this implies that we have an equivalence

\[
\int_ {C ^ {t} \times D} \hom_ {D} (u (a), b) \sim \int_ {C ^ {t} \times D} \hom_ {C} (a, v (b))
\]

Pulling back along \( C^t \times \{b\} \) where \( b \) is any object of \( D \), we get an equivalence between \( (C^t)_{b/}^{\sharp} \) and \( (C^t)_{v(b)/}^{\sharp} \). As this last marked \( (\infty, \omega) \)-category admits an initial element, given by the image \( id_{v(b)} \), this shows the implication \( (1) \Rightarrow (2) \).

For the converse, suppose that \( u \) fulfills condition (2). The functor \( \mathrm{hom}_D(u(\_), \_) : C^t \times D \to \underline{\omega} \) corresponds by adjonction to a functor \( v' : D \to \widehat{C} \). By assumption, for any \( b \in B \), \( v'(b) \) is a representable \( (\infty, \omega) \)-presheaf. The Yoneda lemma then implies that \( v \) factors through a functor \( v : D \to C \). Using once again Yoneda lemma, we have a sequence of equivalences

\[
\hom_ {D} (u (a), b) \sim v ^ {\prime} (b) (a) \sim \hom_ {C} (b, v (a)).
\]

The equivalence between  \( (1)' \)  and  \( (2)' \)  is proved similarly.

□

6.2.2.3. Let  \( (u,v,\phi) \)  be an adjoint structure. There is a transformation

\[
\hom_ {C} (a, a ^ {\prime}) \to \hom_ {D} (u (a), u (a ^ {\prime})) \to \hom_ {C} (a, v u (a ^ {\prime}))
\]

natural in  \( a : C^{t} \) ,  \( a' : C \) . According to the Yoneda lemma, this corresponds to a natural transformation  \( \mu : id_{C} \to vu \) , called the unit of the adjunction. Similarly, the natural transformation:

\[
\hom_ {D} (b, b ^ {\prime}) \to \hom_ {C} (v (b), v (b ^ {\prime})) \to \hom_ {C} (u v (b), b ^ {\prime})
\]

induces a natural transformation \(\epsilon : uv \to id_D\), called the counit of the adjunction.

344

6.2. YONEDA LEMMA AND APPLICATIONS

Lemma 6.2.2.4. Suppose we have two morphisms $f : C \to D$ and $g : C \to D$ between locally U-small $(\infty, \omega)$-categories as well as a natural transformation $\nu : f \to g$. This induces a commutative diagram

$$\begin{array}{c} \hom_C(a, b) \longrightarrow \hom_D(g(a), g(b)) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow_{(\nu_a)!} \\ \hom_D(f(a), f(b)) \xrightarrow{(\nu_b)!} \hom_D(f(a), g(b)) \end{array}$$

natural in $a : C^t, b : C$.

Proof. Remark that $\hom_{[1]}(0, 1) \sim \hom_{[1]}(1, 1) \sim \hom_{[1]}(0, 0) = 1$. Using the naturality of the hom functor, we have a commutative diagram

$$\begin{array}{c} \hom_C(a, b) \times \hom_{[1]}(0, 0) \longrightarrow \hom_D(f(a), f(b)) \\ \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow_{(\nu_b)!} \\ \hom_C(a, b) \times \hom_{[1]}(0, 1) \longrightarrow \hom_D(f(a), g(b)) \\ \sim \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \uparrow_{(\nu_a)!} \\ \hom_C(a, b) \times \hom_{[1]}(1, 1) \longrightarrow \hom_D(g(a), g(b)) \end{array}$$

where the left-hand vertical morphisms are equivalences.

Proposition 6.2.2.5. Let $u : C \to D$ and $v : D \to C$ be two functors between locally U-small $(\infty, \omega)$-categories, $\mu : id_C \to vu$, $\epsilon : uv \to id_D$ be two natural transformations coming along with equivalences

$$(\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u \quad (v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v.$$

If we set $\phi$ as the composite

$$\hom_D(u(a), b) \to \hom_C(vu(a), v(b)) \xrightarrow{(\mu_a)!} \hom_C(a, v(b)),$$

the triple $(u, v, \phi)$ is an adjoint structure. Moreover, the unit of the adjunction is $\mu$ and its counit is $\epsilon$.

Proof. Suppose we have such data. We define $\psi$ as the composite

$$\hom_C(a, v(b)) \to \hom_D(u(a), uv(b)) \xrightarrow{(\epsilon_a)!} \hom_D(u(a), b)$$

natural in $a : C^t$ and $b : D$. We then have to show that these two morphisms are inverse

345

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

of each other. For this consider the diagram

$$\begin{array}{c} \hom_D(u(a), b) \longrightarrow \hom_C(vu(a), v(b)) \xrightarrow{(\mu_a)_!} \hom_C(a, v(b)) \\ \Bigg\| \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_D(uvu(a), uv(b)) \xrightarrow{(u(\mu_a))_!} \hom_D(u(a), uv(b)) \\ \Bigg\| \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_D(u(a), b) \xrightarrow{(\epsilon_{u(a)})_!} \hom_D(uvu(a), b) \xrightarrow{(u(\mu_a))_!} \hom_D(u(a), b) \end{array}$$

which is commutative thanks to lemma 6.2.2.4 and the naturality of the hom. By hypothesis, the left lower horizontal morphism is equivalent to the identity. The outer square then defines an equivalence between $\psi \circ \phi$ and the identity. We show similarly $\phi \circ \psi \sim id$.

For the second assertion, remark that the composition

$$\hom_C(a, a') \to \hom_D(u(a), u(a')) \xrightarrow{\phi(a, u(a'))} \hom_C(a, vu(a'))$$

is by definition equivalent to

$$\hom_C(a, a') \to \hom_D(vu(a), vu(a')) \xrightarrow{(\mu_a)_!} \hom_C(a, vu(a'))$$

and according to the lemma 6.2.2.4, to

$$\hom_C(a, a') \xrightarrow{(\mu_{a'})_!} \hom_C(a, vu(a'))$$

The Yoneda lemma then implies that the unit of the adjunction is $\mu$. We proceed similarly for the counit.

**6.2.2.6.** In paragraph 6.1.4.4, for a morphism $i : I \to A^\sharp$ between marked $(\infty, \omega)$-categories, we define the morphism $i_! : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$ and when $i$ is proper, a morphism $i_* : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$.

**Corollary 6.2.2.7.** *Let $i : I \to A^\sharp$ be a morphism between U-small $(\infty, \omega)$-category. The functor $i^* : \underline{\mathrm{Hom}}(A, \underline{\omega}) \to \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega})$ has a left adjoint given by the functor $i_! : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$. If $i$ is proper, the functor $i^*$ has a right adjoint $i_* : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$.*

*Proof.* With the characterization of adjunction given in proposition 6.2.2.5, this is a direct consequence of natural transformations given in paragraph 6.1.4.4.

346

6.2. YONEDA LEMMA AND APPLICATIONS

6.2.2.8. We conclude this section with the proof of the following theorem.

Theorem 6.2.2.9. Let $u : C \to D$ and $v : D \to C$ be two functors between locally U-small $(\infty, \omega)$-categories. The two following are equivalent.

(1) The pair $(u, v)$ admits an adjoint structure.
(2) Their exists a pair of natural transformations $\mu : id_C \to vu$ and $\epsilon : uv \to id_D$ together with equivalences $(\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u$ and $(v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v$.

We directly give a corollary:

Corollary 6.2.2.10. Let $(u : B \to C, v : C \to B)$ be an adjoint pair between locally U-small $(\infty, \omega)$-categories and $D$ a locally U-small $(\infty, \omega)$-category. If $C$ and $B$ are U-small, this induces an adjunction

$$\_ \circ u : \underline{\mathrm{Hom}}(C, D) \xleftrightarrow{\perp} \underline{\mathrm{Hom}}(B, D) : \_ \circ v$$

and if $D$ is U-small an adjunction

$$u \circ \_ : \underline{\mathrm{Hom}}(D, C) \xleftrightarrow{\perp} \underline{\mathrm{Hom}}(D, B) : v \circ \_$$

Proof. Let $\mu$ and $\epsilon$ be the unit and the counit of the adjunction. We define $\mu' : \underline{\mathrm{Hom}}(C, D) \times [1] \to \underline{\mathrm{Hom}}(C, D)$, induced by currying the morphism

$$\underline{\mathrm{Hom}}(C, D) \times [1] \times C \xrightarrow{id \times \mu} \underline{\mathrm{Hom}}(C, D) \times C \xrightarrow{\mathrm{ev}} D$$

and $\epsilon' : \underline{\mathrm{Hom}}(B, D) \times [1] \to \underline{\mathrm{Hom}}(B, D)$ by currying the morphism

$$\underline{\mathrm{Hom}}(B, D) \times [1] \times B \xrightarrow{id \times \epsilon} \underline{\mathrm{Hom}}(B, D) \times B \xrightarrow{\mathrm{ev}} B$$

We can easily check that $\mu'$ and $\epsilon'$ fulfill the triangle identities, and theorem 6.2.2.9 then implies that the pair $(\_ \circ u, \_ \circ v)$ admits an adjunction structure. We proceed similarly for the second assertion.

6.2.2.11. For the remaining, we fix two functors $u : C \to D$ and $v : D \to C$ between $(\infty, \omega)$-categories as well as an equivalence

$$\phi : \mathrm{hom}_D(u(a), b) \sim \mathrm{hom}_C(a, v(b))$$

natural in $a : C^t$ and $b : D$.

347

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Lemma 6.2.2.12. The natural transformation

\[
\hom_ {D} (u (a), b) \to \hom_ {C} (v u (a), v (b)) \xrightarrow {(\mu_ {a}) !} \hom_ {C} (a, v (b))
\]

is equivalent to \(\phi : \hom_D(u(a), b) \to \hom_D(a, v(b))\). Similarly, the natural transformation

\[
\hom_ {C} (a, v (b)) \to \hom_ {D} (u (a), u v (b)) \xrightarrow {(\epsilon_ {b}) !} \hom_ {D} (u (a), b)
\]

is equivalent to \(\phi^{-1}:\hom_D(a,v(b))\to \hom_D(u(a),b)\).

Proof. Remark that we have a commutative diagram

![img-395.jpeg](img-395.jpeg)

The commutativity of the left triangle comes from the definition of  \( \mu \) , and the second one, from the lemma 6.2.2.4, applied to  \( \mu \) . This then induces a commutative square

![img-396.jpeg](img-396.jpeg)

By adjunction, this corresponds to a commutative square

![img-397.jpeg](img-397.jpeg)

However, the top horizontal and left vertical morphisms are equivalences according to lemma 6.2.1.17. We then have an equivalence

\[
\int_ {C ^ {t} \times D} (\mu_ {a}) _ {!} \circ \mathrm{hom} _ {v} \sim \int_ {C ^ {t} \times D} \phi
\]

which implies the result. The other assertion is shown similarly.

Lemma 6.2.2.13. There are equivalences \((\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u\) and \((v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v\).

348

6.2. YONEDA LEMMA AND APPLICATIONS

Proof. As the proof of the two assertions are similar, we will only show the second one. To demonstrate this, it is enough to show that the induced natural transformation

$$\hom_C(a, v(b)) \xrightarrow{(\mu_{v(b)})!} \hom_C(a, vuv(b)) \xrightarrow{(v(\epsilon_{(b)}))!} \hom_C(a, v(b)) \xrightarrow{\phi^{-1}} \hom_D(u(a), b) \tag{6.2.2.14}$$

is equivalent to $\phi^{-1}$. By definition, the first morphism is equivalent to the composition

$$\hom_C(a, v(b)) \to \hom_D(u(a), uv(b)) \xrightarrow{\phi} \hom_C(a, vuv(b))$$

and as $\phi^{-1}$ is a natural transformation, we have a commutative square

$$\begin{array}{ccc} \hom_C(a, vuv(b)) & \xrightarrow{(v(\epsilon_b))!} & \hom_C(a, v(b)) \\ \phi^{-1} \downarrow & & \downarrow \phi^{-1} \\ \hom_C(u(a), uv(b)) & \xrightarrow{(\epsilon_b)!} & \hom_D(u(a), b) \end{array}$$

The composite of the sequence (6.2.2.14) is then equivalent to

$$\hom_C(a, v(b)) \to \hom_D(u(a), uv(b)) \xrightarrow{(\epsilon_b)!} \hom_D(u(a), b)$$

which is itself equivalent to $\phi^{-1}$ according to lemma 6.2.2.12.

Proof of theorem 6.2.2.9. The implication (1) $\Rightarrow$ (2) is given by proposition 6.2.2.5 and the contraposed by the lemma 6.2.2.13.

### 6.2.3 Lax colimits

6.2.3.1. According to corollary 6.2.2.7, a morphism $f : A \to B$ between U-small $(\infty, \omega)$-categories induces an adjoint pair:

$$f_! : \widehat{A} \xrightarrow{\perp} \widehat{B} : f^* \tag{6.2.3.2}$$

Proposition 6.2.3.3. Let $f : A \to B$ be a morphism between U-small $(\infty, \omega)$-categories. There is an equivalence

$$f_!(y_a) \sim y_{f(a)}$$

natural in $a : A$.

Proof. Consider the sequence of equivalences

$$\begin{array}{lcl} \hom_{\widehat{B}}(f_!(y_a), g) & \sim & \hom_{\widehat{A}}(y_a, f^*(g)) \quad (6.2.3.2) \\ & \sim & \operatorname{ev}(a, f^*(g)) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(Yoneda lemma)} \\ & \sim & \operatorname{ev}(f(a), g) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(naturality of ev)} \\ & \sim & \hom_{\widehat{B}}(y_{f(a)}, g) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Eventually, the Yoneda lemma applied to $(\widehat{B})^t$ concludes the proof.

349

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.2.3.4. For I a marked  \( (\infty,\omega) \) -category and A an  \( (\infty,\omega) \) -category, we recall that  \( \underline{\mathrm{Hom}}_{\ominus}(I,A) \)  is the  \( (\infty,\omega) \) -category whose value on a globular sum a is given by:

\[
\mathrm{Hom} (a, \underline {{\mathrm{Hom}}} _ {\ominus} (I, A)) := \mathrm{Hom} (I \ominus a ^ {\sharp}, A ^ {\sharp})
\]

Remark 6.2.3.5. Let \( B \) be an \( (\infty, \omega) \)-category. We want to give an intuition of the object \( \underline{\mathrm{Hom}}_{\ominus}(B^{\flat}, \omega) \). The objects of this \( (\infty, \omega) \)-category are the functors \( I \to \omega \). The 1-cells are the lax transformations \( F \Rightarrow G \). For \( n > 1 \), the \( n \)-cells are the lax transformations \( F^{\times \mathbf{D}_{n-1}} \Rightarrow G \) where \( F^{\times \mathbf{D}_{n-1}}: I \to \omega \) is the functor that sends \( i \) onto \( F(i) \times \mathbf{D}_{n-1} \). This last assertion is a consequence of the equivalence

\[
\tau_ {0} (\mathrm{LCart} ((I \ominus [ b, n ] ^ {\sharp}) ^ {\sharp}) \sim \mathrm{Hom} ([ n ], \mathrm{LCart} ^ {c} (I; b))
\]

provided by the lemma 6.1.4.12.

Proposition 6.2.3.6. If \( I \) is U-small and \( A \) is locally U-small, the \( (\infty, \omega) \)-category \( \underline{\mathrm{Hom}}_{\ominus}(I, A) \) is locally U-small.

Proof. We have to check that for any globular sum \( b \), the morphism

\[
\operatorname{Hom} (I \ominus [ b, 1 ] ^ {\sharp}, A ^ {\sharp}) \to \operatorname{Hom} (I \ominus (\{0 \} \amalg \{1 \}), A ^ {\sharp})
\]

has U-small fibers. As I, seen as an  \( \infty \) -presheaves on  \( t\Theta \) , is a U-small colimit of representatives, we can reduce to the case where  \( I \in t\Theta \) . As A is local with respect to Segal extensions, and as  \( \ominus \)  conserves them, we can reduce to the case where I is of shape  \( [1]^{\sharp} \)  or  \( [a,1] \)  for a in  \( t\Theta \) . If I is  \( [1]^{\sharp} \) , according to the second assertion of proposition 5.1.3.16,  \( [1]^{\sharp} \ominus [b,1]^{\sharp} \)  is equivalent to  \( ([1] \times [b,1])^{\sharp} \)  and the result follows from proposition 6.2.1.3.

For the second case, we fix a morphism \( f:[a,1]\times (\{0\} \amalg \{1\})\to A \). Using the canonical equivalence between \([a,1]\ominus [b,1]^{\sharp}\) and the colimit of the diagram (5.1.3.14), the \(\infty\)-groupoid \(\mathrm{Hom}(I\ominus [b,1]^{\sharp},A^{\sharp})_f\) is the limit of the diagram:

![img-398.jpeg](img-398.jpeg)

As all these objects are U-small by assumption, this concludes the proof.

□

350

6.2. YONEDA LEMMA AND APPLICATIONS

6.2.3.7. Let I be a U-small marked  \( (\infty,\omega) \) -category, A a locally U-small  \( (\infty,\omega) \) -category A and  \( F:I\to A^{\sharp} \)  a functor. A lax colimit of F is an object laxcolim \( _{I} \)  F of A together with an equivalence

\[
\hom_ {A} (\underset {I} {\text { laxcolim }} F, b) \sim \hom_ {\underline {{\text { Hom }}} _ {\square} (I, A)} (F, \text { cst } b)
\]

natural in \( b: A \). Conversely, a lax limit of \( F \) is an object laxlim\(_I\) \( F \) of \( A \) together with an equivalence

\[
\hom_ {A} (b, \underset {I} {\text { laxlim }} F) \sim \hom_ {\underline {{\text { Hom }}} _ {\square} (I, A)} (\text { cst } b, F)
\]

natural in \( b: A \). We say that a locally U-small \( (\infty, \omega) \)-category \( C \) is lax U-complete (resp. lax U-cocomplete), if for any U-small marked \( (\infty, \omega) \)-category \( I \) and any functor \( F: I \to C \), \( F \) admits limits (resp. colimits).

Using proposition 6.2.2.2, C is lax U-complete (resp. lax U-cocomplete) if and only if for any U-small marked  \( (\infty,\omega) \) -category I, the functor  \( \operatorname{cst}:C\to\underline{\operatorname{Hom}}_{\square}(I,C) \)  admits a right adjoint (resp. a left adjoint).

The proposition 5.1.3.15 induces an equivalence

\[
\underline {{\mathrm{Hom}}} _ {\square} (I, A) ^ {\circ} \sim \underline {{\mathrm{Hom}}} _ {\square} (I ^ {\circ}, A ^ {\circ})
\]

As a consequence, a functor  \( F: I \to A^{\sharp} \)  admits a lax colimit if and only if  \( F^{\circ}: I^{\circ} \to (A^{\circ})^{\sharp} \)  admits a lax limit. If F admits such lax colimit, the lax limit of  \( F^{\circ} \)  is the image by the canonical equivalence  \( A_{0} \sim A_{0}^{\circ} \)  of the lax colimit of F.

Remark 6.2.3.8. We want to give an intuition of the lax colimits. Let I be a U-small marked  \( (\infty,\omega) \) -category, A a locally U-small  \( (\infty,\omega) \) -category A and  \( F:I\to A^{\sharp} \)  a functor admitting a lax colimit laxcolim \( _{I} \)  F. For any 1-cell  \( i:a\to b \)  in I, we have a triangle

![img-399.jpeg](img-399.jpeg)

If \( i \) is marked, the preceding 2-cell is an equivalence. For any 2-cell \( u: i \to j \), we have a diagram

![img-400.jpeg](img-400.jpeg)

If u is marked, the 3-cell is an equivalence. We can continue these diagrams in higher dimensions and we have similar assertions for lax limits.

The marking therefore allows us to play on the "lax character" of the universal property that the lax colimit must verify.

351

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**6.2.3.9.** Let $A$ be a $\mathbf{U}$-small $(\infty, \omega)$-category and $I$ a $\mathbf{U}$-small marked $(\infty, \omega)$-category. Recall that $\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$ is equivalent to $\underline{\mathrm{Hom}}_{\ominus}(I \times (A^t)^{\sharp}, \underline{\omega})$. Let $t$ be the canonical morphism $I \to 1$. As $t$ is smooth, corollary 6.2.2.7 induces adjunctions

$$\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A}) \xleftarrow{(t \times id_A)_*} \xrightarrow{(t \times id_A)_*} \widehat{A} \tag{6.2.3.10}$$

and $\widehat{A}$ is then lax $\mathbf{U}$-complete and lax $\mathbf{U}$-cocomplete. For a morphism $g: I \to \widehat{A}^{\sharp}$ corresponding to an object $E$ of $\mathrm{LCart}^c(I \times (A^t)^{\sharp})$, we then have

$$\int_{A^t} \underset{I}{\mathrm{laxcolim}} \, g \sim \mathbf{L}(t \times id_{(A^t)^{\sharp}})_! E \quad \int_{A^t} \underset{I}{\mathrm{laxlim}} \, g \sim \mathbf{R}(t \times id_{(A^t)^{\sharp}})_* E \tag{6.2.3.11}$$

Let $i: B^{\sharp} \to A^{\sharp}$ be any morphism. The squares given in paragraph 6.1.4.4 induce the commutative squares

$$\begin{array}{ccc} \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A}) & \xrightarrow{\mathrm{laxcolim}_I} & \widehat{A} \xleftarrow{\mathrm{laxlim}_I} & \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A}) \\ (id_I \times i^t)^* & \downarrow & \downarrow i^* & \downarrow (id_I \times i^t)^* \\ \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{B}) & \xrightarrow{\mathrm{laxcolim}_I} & \widehat{B} \xleftarrow{\mathrm{laxlim}_I} & \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{B}) \end{array}$$

In particular, choosing $B := 1$, this implies that the lax colimits and limits in $(\infty, \omega)$-presheaves commute with evaluation.

The next proposition implies that limits and colimits in $(\infty, \omega)$-presheaves can be detected as the level of the sub maximal $(\infty, 1)$-categories of $\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$ and $\widehat{A}$. We recall that the sub maximal $(\infty, 1)$-categories of $\underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$, denoted by $\tau_1 \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})$, is the adjoint of the functor $[n] \mapsto I \otimes [n]^{\sharp}$.

**Proposition 6.2.3.12.** *Let $I$ be a $\mathbf{U}$-small marked $(\infty, \omega)$-category, and $g: I \to A^{\sharp}$ a functor. An object $f$ of $\widehat{A}$ has a structure of colimit of the functor $g$ if and only if there exists an equivalence*

$$\mathrm{Hom}_{\tau_1 \widehat{A}}(f, h) \sim \mathrm{Hom}_{\tau_1 \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})}(F, \mathrm{cst} \, h)$$

*natural in $h: (\tau^1 \widehat{A})^{op}$. Similarly, the object $f$ has a structure of limit of the functor $F$ if and only if there exists an equivalence*

$$\mathrm{Hom}_{\tau_1 \widehat{A}}(h, f) \sim \mathrm{Hom}_{\tau_1 \underline{\mathrm{Hom}}_{\ominus}(I, \widehat{A})}(\mathrm{cst} \, h, F)$$

*natural in $h: (\tau^1 \widehat{A})^{op}$.*

352

6.2. YONEDA LEMMA AND APPLICATIONS

Proof. We recall that theorem 6.1.4.2 and corollary 6.1.4.3 induces equivalences

$$\tau_{1}\widehat{A}\sim\mathrm{LCart}_{\mathbf{U}}((A^{t})^{\sharp})\quad\tau_{1}\underline{\mathrm{Hom}}_{\ominus}(I,A)\sim\mathrm{LCart}_{\mathbf{U}}^{c}(I\otimes(A^{t})^{\sharp})$$

and that we have a triplet of adjoints

$$\mathrm{LCart}_{\mathbf{U}}^{c}(I\otimes(A^{t})^{\sharp})\xrightarrow[\leftarrow((\stackrel{\perp}{\times}(t\times id_{A^{t}}))^{*}\text{--}\mathrm{LCart}_{\mathbf{U}}((A^{t})^{\sharp})]{\underset{\perp}{\mathrm{L}}(t\times id_{A^{t}})_{*}\text{--}\mathrm{LCart}_{\mathbf{U}}((A^{t})^{\sharp})}$$

which is the image by $\tau_{1}$ of the triplet of adjoints (6.2.3.10). The first hypothesis induces an equivalence

$$\int_{A^{t}}f\sim\mathbf{L}(t\times id_{(A^{t})^{\sharp}})_{!}E$$

and the second one an equivalence

$$\int_{A^{t}}f\sim\mathbf{R}(t\times id_{(A^{t})^{\sharp}})_{*}E$$

where $E$ denote the object of $\mathrm{LCart}^{c}(I\times(A^{t})^{\sharp})$ corresponding to $g$. The assertions then follow from the equivalences (6.2.3.11).

Example 6.2.3.13. We recall that we denote by $\perp:\mathrm{Arr}((\infty,\omega)\text{-cat}_{\mathrm{m}})\to(\infty,\omega)\text{-cat}$ the functor sending a left fibration $Y\to A$ to the localization of $Y$ by marked cells. This functors sends initial and final morphisms to equivalences. If $E$ is a left cartesian fibration over a marked $(\infty,\omega)$-category $I$, we then have $\perp E\sim\mathbf{L}t_{!}E$ where $t$ denotes the morphism $I\to 1$.

Let $g:I\to\underline{\omega}$ be a diagram. We denote $\iota:I\to I^{\sharp}$ the canonical inclusion. By the explicit expression of lax colimit given above, we then have an equivalence

$$\operatorname*{laxcolim}_{I}g\sim\perp\iota^{*}\int_{I^{\sharp}}g^{\sharp}.$$

If $I$ is equivalent to $I^{\flat}$, we then have

$$\operatorname*{laxcolim}_{I}g\sim\mathrm{dom}(\int_{I^{\sharp}}g^{\sharp})^{\sharp}.$$

- Let $c:1\to\underline{\omega}$ be a morphism corresponding to an $(\infty,\omega)$-category $C$. For any $(\infty,\omega)$-category $A$, we then have

$$\operatorname*{laxcolim}_{A^{\sharp}}\mathrm{cst}_{c}\sim(\tau_{0}A)\times C\qquad\operatorname*{laxcolim}_{A^{\flat}}\mathrm{cst}_{c}\sim A\times C$$

- Let $f:[b,1]\to\underline{\omega}$ be a morphism corresponding to a morphism $A\times b\to B$. We then have

$$\operatorname*{laxcolim}_{[b,1]^{\flat}}f\sim A\times(1^{\text{co}}\star b)\coprod_{A\times b}B$$

353

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

Example 6.2.3.14. Using the explicit expression of lax limit given above, we have an equivalence

\[
\underset {I} {\mathrm{laxlim}} g \sim \mathrm{Map} (i d _ {I}, \iota^ {*} \int_ {I ^ {\sharp}} g ^ {\sharp})
\]

- Let \( c: 1 \to \underline{\omega} \) be a morphism corresponding to an \( (\infty, \omega) \)-category \( C \). For any \( (\infty, \omega) \)-category \( A \), we then have

\[
\underset {A ^ {\sharp}} {\mathrm{laxlim}} \operatorname{cst} _ {c} \sim \underline {{\mathrm{Hom}}} (\tau_ {0} A, C) \qquad \underset {A ^ {\flat}} {\mathrm{laxlim}} \operatorname{cst} _ {c} \sim \underline {{\mathrm{Hom}}} (A, C)
\]

- Let \( f:[b,1] \to \underline{\omega} \) be a morphism corresponding to a morphism \( A \times b \to B \). Let \( c \) be a globular sum. According to corollary 6.1.3.32, a morphism \( id_{[b,1]^{\flat}} \times c^{\flat} \to \iota^{*} \int_{[b,1]^{\flat}} g^{\sharp} \) corresponds to a diagram

![img-401.jpeg](img-401.jpeg)

and according to proposition 6.1.1.13, to a diagram

![img-402.jpeg](img-402.jpeg)

where the upper horizontal morphism is of shape  \( g \times b \) . We then have

\[
\underset {[ b, 1 ] ^ {\flat}} {\text { laxlim }} f \sim A \prod_ {\operatorname{Hom} (b, B)} \operatorname{Hom} (b \star 1, B).
\]

Proposition 6.2.3.15. Let \(i: I \to J\) be a morphism between \(\mathbf{U}\)-small marked \((\infty, \omega)\)-categories, \(A\) a \(\mathbf{U}\)-small \((\infty, \omega)\)-category and \(f: J \to \widehat{A}^{\sharp}\) a morphism. If \(i\) is final, then the canonical morphism

\[
\underset {I} {\text { laxcolim }} f \circ i \to \underset {J} {\text { laxcolim }} f
\]

is an equivalence.

If \(i\) is initial, then the canonical morphism

\[
\underset {J} {\mathrm{laxlim}} f \to \underset {I} {\mathrm{laxlim}} f \circ i
\]

is an equivalence.

354

6.2. YONEDA LEMMA AND APPLICATIONS

Proof. We only show the first assertion as the second follows by duality. As equivalences are detected pointwise and as the lax colimit commutes with evaluation, one can suppose that $A := 1$, and so $\widehat{A} := \underline{\omega}$. We denote by $E$ (resp. $H$) the object of $\mathrm{LCart}(J)$ (resp. $\mathrm{LCart}(I)$) corresponding to $f$ (resp. $f \circ i$) and $X \to I$ (resp. $Y \to J$) the corresponding left cartesian fibration. We then have a cartesian square

$$
\begin{array}{c c c} Y & \xrightarrow {i ^ {\prime}} & X \\ E \Big \downarrow & & \Big \downarrow H \\ J & \xrightarrow [ i ] & I \end{array}
$$

As classified left cartesian fibrations are proper, $i'$ is final. We recall that we denote by $\perp : (\infty, \omega)$-$\mathrm{cat}_{\mathrm{m}} \to (\infty, \omega)$-cat the functor sending a marked $(\infty, \omega)$-category to its localization by marked cells, and that $\perp$ sends final morphism to equivalences. If we denote by $t$ the two morphisms $I \to 1$ and $J \to 1$, we then have a sequence of equivalences:

$$
\operatorname * {l a x c o l i m} _ {I} f \circ i \sim \mathbf {L} t _ {!} H \sim \bot Y \sim \bot X \sim \mathbf {L} t _ {!} E \sim \operatorname * {l a x c o l i m} _ {J} f
$$

Lemma 6.2.3.16. Let $F: I \to A^{\sharp}$ be a morphism between $\mathbf{U}$-small marked $(\infty, \omega)$-categories. There is an equivalence

$$
\hom_ {\underline {{\operatorname {H o m}}} _ {\ominus} (I, A)} (\operatorname {c s t} _ {a}, F) \sim \underset {I} {\operatorname {l a x l i m}} \hom_ {A} (a, F)
$$

natural in $F:\underline{\mathrm{Hom}}_{\ominus}(I,A)$ and $a:A^t$.

Proof. Remark that there is a commutative square:

$$
\begin{array}{c} A \xrightarrow {\text {c s t}} \underline {{\operatorname {H o m}}} _ {\ominus} (I, A) \\ y \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \widehat {A} \xrightarrow [ \text {c s t} ]{} \underline {{\operatorname {H o m}}} _ {\ominus} (I, \widehat {A}) \end{array}
$$

and that the right vertical morphism is fully faithful as $y$ is. We then have a sequence of equivalences

$$
\begin{array}{l} \hom_ {\underline {{\operatorname {H o m}}} _ {\ominus} (I, A)} (\operatorname {c s t} _ {a}, F) \sim \hom_ {\underline {{\operatorname {H o m}}} _ {\ominus} (I, \widehat {A})} (\operatorname {c s t} _ {y _ {a}}, \underline {{\operatorname {H o m}}} _ {\ominus} (I, y) (F)) \\ \sim \hom_ {\widehat {A}} (y _ {a}, \operatorname {l a x l i m} _ {I} \underline {{\operatorname {H o m}}} _ {\ominus} (I, y) (F))) \\ \sim \left(\operatorname {l a x l i m} _ {I} \underline {{\operatorname {H o m}}} _ {\ominus} (I, y) (F)\right) (a) \quad (\text {Y o n e d a l e m m a}) \\ \sim \operatorname {l a x l i m} _ {I} \hom_ {A} (a, F (i)) \\ \end{array}
$$

where the last one comes from the fact that evaluations commute with lax limits.

355

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

**Proposition 6.2.3.17.** *Consider a functor $F : I \to A^{\sharp}$ between $\mathbf{U}$-small marked $(\infty, \omega)$-categories. Then $F$ admits a lax limit if and only if there exists an object $l$ and an equivalence*

$$
\hom_A(a, l) \sim \underset{I}{\text{laxlim}} \hom_A(a, F(i))
$$

*natural in $a : A^t$. If such an object exists, then $l$ is the lax limit of $F$. Dually, $F$ admits a lax colimit if and only if there exists an object $c$ and an equivalence*

$$
\hom_A(c, a) \sim \underset{I}{\text{laxlim}} \hom_A(F(i), a)
$$

*natural in $a : A$. If such an object exists, then $c$ is the lax colimit of $F$.*

*Proof.* The first assertion is a direct application of lemma 6.2.3.16. The second one follows by duality, using the fact that the functor

$$
(\_)^\circ : \underline{\omega} \to \underline{\omega}^{t^\circ}
$$

preserves limits as it is an equivalence. $\square$

**Corollary 6.2.3.18.** *Left adjoints between $\mathbf{U}$-small $(\infty, \omega)$-categories preserve colimits and right adjoints preserve limits.*

*Proof.* Let $u : C \to D$ and $v : D \to C$ be two adjoint functors. Let $F : I \to C^{\sharp}$ be a functor admitting a colimit. We then have a sequence of equivalences

$$
\begin{array}{rcl}
\hom_C(u(\text{laxcolim}_I F), b) & \sim & \hom_D(\text{laxcolim}_I F, v(b)) \\
& \sim & \text{laxlim}_I \hom_D(F, v(b)) \quad (6.2.3.17) \\
& \sim & \text{laxlim}_I \hom_C(u(F), b) \\
& \sim & \hom_C(\text{laxlim}_I u(F), b) \quad (6.2.3.17)
\end{array}
$$

natural in $b : D$. The result then follows from the Yoneda lemma applied to $C^t$. The other assertion is proved similarly. $\square$

**Corollary 6.2.3.19.** *Consider a functor $F : I \to A^{\sharp}$ between $\mathbf{U}$-small marked $(\infty, \omega)$-categories. Then $F$ admits a limit if and only if there exists an object $l$ and an equivalence*

$$
\hom_A(a, l) \sim \hom_{\underline{\operatorname{Hom}}_\square(I, \underline{\omega})}(\text{cst } 1, \hom_A(a, F(\_)))
$$

*natural in $a : A^t$. If such an object exists, then $l$ is a limit of $F$. Dually, $F$ admits a colimit if and only if there exists an object $c$ and an equivalence*

$$
\hom_A(c, a) \sim \hom_{\underline{\operatorname{Hom}}_\square(I, \underline{\omega})}(\text{cst } 1, \hom_A(F(\_), a))
$$

*natural in $a : A$. If such an object exists, then $c$ is the colimit of $F$.*

356

6.2. YONEDA LEMMA AND APPLICATIONS

Proof. Remark that we have an equivalence

$$\hom_{\underline{\mathrm{Hom}}_{\square}(I, \underline{\omega})}(\mathrm{cst}\ 1, \hom_A(a, F(\_))) \sim \hom_{\underline{\omega}}(1, \underset{I}{\mathrm{laxlim}}\hom_A(a, F(\_)))$$

Eventually, the Yoneda lemma implies that

$$\hom_{\underline{\omega}}(1, \underset{I}{\mathrm{laxlim}}\hom_A(a, F(\_)) \sim \underset{I}{\mathrm{laxlim}}\hom_A(a, F(\_)))$$

The result then follows from proposition 6.2.3.17.

Remark 6.2.3.20. The characterization of the lax colimit and limit given in previous corollary is the generalization to the case $(\infty, \omega)$ of the characterization of lax colimit and limit for $(\infty, 2)$-categories given in [GHL20, corollary 5.1.7].

Proposition 6.2.3.21. Let $i: I \to J$ and $F: J \to A^\sharp$ be two morphisms between U-small marked $(\infty, \omega)$-categories. If $i$ is initial, and $F$ admits a lax limit, the functor $F \circ i$ also admits a lax limit, and the canonical morphism:

$$\underset{I}{\mathrm{laxlim}}\ F \to \underset{J}{\mathrm{laxlim}}\ F \circ i$$

is an equivalence. Dually, if $i$ is final, and $F$ admits a lax colimit, the functor $F \circ i$ also admits a lax colimit, and the canonical morphism:

$$\underset{J}{\mathrm{laxcolim}}\ F \circ i \to \underset{I}{\mathrm{laxlim}}\ F$$

is an equivalence.

Proof. The first assertion is a direct application of the characterization of limits given in proposition 6.2.3.17 and of proposition 6.2.3.15. The second assertion follows by duality.

The proof of the following lemma is a direct adaptation of the one of proposition 5.1 of [GHN].

Proposition 6.2.3.22. Let $f: A \to B$ be any morphism between U-small $(\infty, \omega)$-categories.. There is an equivalence

$$\hom_{\underline{\mathrm{Hom}}(A, B)}(f, g) \sim \underset{a \to b: S(A)}{\mathrm{laxlim}}\hom_B(f(a), g(a))$$

natural in $f$ and $g$.

Proof. Remark first that the left term is in fact equivalent to

$$\underset{a \to b: S(A)}{\mathrm{laxlim}}\ h^*\hom_B(\_, \_)$$

357

CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

where \( h \) is the left cartesian fibration \( S(A) \to A^t \times A \) corresponding to \( \mathrm{hom}_A: A^t \times A \to \underline{\omega} \). We then have

\[
\operatorname{laxlim} _ {a \rightarrow b: S (A)} \hom_ {B} (f (a), g (a)) \sim \hom_ {\underline {{\omega}}} (1, \operatorname{laxlim} _ {a \rightarrow b: S (A)} h ^ {*} \hom_ {B} (\_, \_)) \tag {6.2.1.18}
\]

\[
\sim \hom_ {\underline {{\mathrm{Hom}}} _ {\square} (S (A), \underline {{\omega}})} (\mathrm{cst} 1, h ^ {*} \hom_ {B} (\_, \_))
\]

\[
\sim \hom_ {\underline {{\mathrm{Hom}}} (A ^ {t} \times A, \underline {{\omega}})} (h _ {!} \mathrm{cst} 1, \hom_ {B} (\_, \_)) \tag {6.2.2.7}
\]

By construction, \( h_{!} \) cst 1 is the Grothendieck deconstruction of the left cartesian fibration \( \mathbf{L}h_{!}id \sim h \), and so is equivalent to \( \mathrm{hom}_A \). We then have

\[
\underset {a \to b: S (A)} {\text { laxlim }} \hom_ {B} (f (a), g (a)) \sim \hom_ {\underline {{\text { Hom }}} (A ^ {t} \times A, \underline {{\omega}})} (\hom_ {A} (\_, \_), \hom_ {B} (f (\_, g (\_))))
\]

We have a canonical equivalence \(\underline{\mathrm{Hom}}(A^t \times A, \underline{\omega}) \sim \underline{\mathrm{Hom}}(A, \widehat{A})\) sending the functor \(\mathrm{hom}_A\) to the Yoneda embedding \(y^A\), and \(\mathrm{hom}_B(f(\_), g(\_))\) is \(f^*(y^B \circ g)\). We then have

\[
\hom (\hom_ {A} (\_, \_), \hom_ {B} (f (\_, g (\_))) \sim \hom_ {\underline {{\mathrm{Hom}}} (A, \widehat {A})} (y ^ {A}, f ^ {*} (y ^ {B} \circ g))
\]

\[
\sim \hom_ {\underline {{\mathrm{Hom}}} (A, \widehat {B})} (f _ {!} \circ y ^ {A}, y ^ {B} \circ g) \tag {6.2.2.7}
\]

\[
\sim \hom_ {\underline {{\mathrm{Hom}}} (A, \widehat {B})} (y ^ {B} \circ f, y ^ {B} \circ g) \tag {6.2.3.3}
\]

\[
\sim \hom_ {\underline {{\mathrm{Hom}}} (A, B)} (f, g) \quad (\text { Yoneda   lemma })
\]

□

6.2.3.23. We suppose the existence of a Grothendieck universe \(\mathbf{Z}\) containing \(\mathbf{W}\). As a consequence, we can use all the results of the last three subsections to respectively \(\mathbf{V}\)-small and locally \(\mathbf{V}\)-small objects.

Let \( A \) be a U-small \( (\infty, \omega) \)-category. Let \( f \) be an object of \( \widehat{A} \). We define \( A_{/f}^{\sharp} \) as the following pullback

![img-403.jpeg](img-403.jpeg)

Theorem 6.2.3.24. The colimit of the functor \(\pi : A_{/f}^{\sharp} \to A^{\sharp} \to \widehat{A}^{\sharp}\) is \(f\).

Proof. We denote by \(\pi'\) the canonical projection \(\widehat{A}_{/f}^{\sharp} \to \widehat{A}^{\sharp}\), and \(t_{A_{/f}^{\sharp}}: A_{/f}^{\sharp} \to 1\), \(t_{\widehat{A}_{/f}^{\sharp}}: \widehat{A}_{/f}^{\sharp} \to 1\) the canonical morphisms. By the explicit construction of colimits in \((\infty, \omega)\)-presheaves, we have equivalences

\[
\int_ {A ^ {t}} \underset {A _ {/ f} ^ {\sharp}} {\operatorname{colim}} \pi \sim (i d _ {(A ^ {t}) ^ {\sharp}} \times t _ {A _ {/ f} ^ {\sharp}})! E \qquad \int_ {A ^ {t}} \underset {\widehat {A} _ {/ f} ^ {\sharp}} {\operatorname{colim}} \pi^ {\prime} \sim (i d _ {(A ^ {t}) ^ {\sharp}} \times t _ {\widehat {A} _ {/ f} ^ {\sharp}})! F
\]

where \(E\) is the object of \(\mathrm{LCart}(A^{\sharp} \times A_{/f}^{\sharp})\) induced by currying \(\pi\), and \(F\) is the object of \(\mathrm{LCart}(A^{\sharp} \times \widehat{A}_{/f}^{\sharp})\) induced by currying \(\pi'\). We denote by \(X \to A^{\sharp} \times A_{/f}^{\sharp}\) the left cartesian

358

6.2. YONEDA LEMMA AND APPLICATIONS

fibration corresponding to $E$, and by $Y \to (A^t)^\sharp \times \widehat{A}_{/f}^\sharp$ the left fibration corresponding to $F$. All this data fits in the diagram

![img-404.jpeg](img-404.jpeg)

where all squares are cartesian. Furthermore, according to the Yoneda lemma, $\mathrm{dom}(\int_{A^t \times \widehat{A}} \mathrm{ev}))$ is equivalent to $\mathrm{dom}(\int_{A^t \times \widehat{A}} \mathrm{hom}_{\widehat{A}}(y_{-}, -))$, and lemma 6.2.1.17 implies that $i$ is initial. As the lower horizontal morphism is a right cartesian fibration, and the dual version of proposition 5.2.4.7 induces that $j$ is initial. This implies that the canonical morphism

$$(id_{(A^t)^\sharp} \times \bot_{A_{/f}^\sharp})_! E \to (id_{(A^t)^\sharp} \times \bot_{\widehat{A}_{/f}^\sharp})_! F$$

is an equivalence, and we then have

$$\underset{A_{/f}^\sharp}{\mathrm{colim}} \pi \sim \underset{\widehat{A}_{/f}^\sharp}{\mathrm{colim}} \pi'$$

However, $A_{/f}^\sharp$ admits a terminal element, given by $id_f$, and according to proposition 6.2.3.17, we have

$$\underset{A_{/f}^\sharp}{\mathrm{colim}} \pi \sim f.$$

**Corollary 6.2.3.25.** *A U-small $(\infty, \omega)$-category $A$ is lax U-cocomplete if and only if the Yoneda embedding has a left adjoint, which we will also note by laxcolim.*

*Proof.* If such a left adjoint exists, as $\widehat{A}$ is lax U-cocomplete, corollary 6.2.3.18 implies that $A$ is lax U-cocomplete. Suppose now that $A$ is lax U-cocomplete and let $f: A^t \to \underline{\omega}$ be a functor. Let $c$ be the colimit of the functor $A_{/f}^\sharp \to A^\sharp$. According to theorem 6.2.3.24, we have a sequence of equivalences

$$\begin{array}{l} \mathrm{hom}_{\widehat{A}}(f, y(a)) \sim \mathrm{hom}_{\widehat{A}}(\mathrm{laxcolim}_{A_{/f}^\sharp} y(\_), y(a)) \\ \quad \sim \mathrm{laxlim}_{A_{/f}^\sharp} \mathrm{hom}_{\widehat{A}}(y(\_), y(a)) \\ \quad \sim \mathrm{laxlim}_{A_{/f}^\sharp} \mathrm{hom}_A(\_, a) \\ \quad \sim \mathrm{hom}_A \mathrm{hom}(c, a) \end{array}$$

359

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

natural in $a : A^t$. The functor

$$a : A \mapsto \hom_{\widehat{A}}(f, y(a))$$

is then representable, which concludes the proof according to proposition 6.2.2.2.

**6.2.3.26.** Let $i : A \to B$ be a functor between two $\mathbf{U}$-small $(\infty, \omega)$-categories. We define $N_i : B \to \widehat{A}$ as

$$a : A^t, b : B \mapsto \hom_B(i(a), b)$$

**Corollary 6.2.3.27.** *Let $i : A \to B$ be a functor between two $\mathbf{U}$-small $(\infty, \omega)$-categories with $B$ lax $\mathbf{U}$-cocomplete. The morphism $N_i : B \to \widehat{A}$ admits a left adjoint that sends an $(\infty, \omega)$-presheaf $f$ to $\operatorname{laxcolim}_{A_{/f}^t} i(\_)$*

*Proof.* The proof is similar to the one of corollary 6.2.3.25.

### 6.2.4 Kan extensions

We suppose the existence of a Grothendieck universe $\mathbf{Z}$ containing $\mathbf{W}$. As a consequence, we can use all the results of the last three subsections to respectively $\mathbf{V}$-small and locally $\mathbf{V}$-small objects.

**6.2.4.1.** Let $f : A \to B^\sharp$ be a morphism between marked $\mathbf{U}$-small $(\infty, \omega)$-categories. This induces for any $(\infty, \omega)$-category $C$ a morphism

$$\_ \circ f : \underline{\operatorname{Hom}}_\odot(B, C) \to \underline{\operatorname{Hom}}(A, C).$$

Let $g : A \to C$ be a morphism. A *left Kan extension* of $g$ along $f$ is a functor $\operatorname{Lan}_f g : B \to C$ and an equivalence

$$\hom_{\underline{\operatorname{Hom}}(B, C)}(\operatorname{Lan}_f g, h) \sim \hom_{\underline{\operatorname{Hom}}_\odot(A, C)}(g, h \circ f).$$

Remark that if the left Kan extension along $f$ exists for any $g$, the proposition 6.2.2.2 implies that the assignation $g \mapsto \operatorname{Lan}_f g$ can be promoted to a left adjoint, which is called the *global left Kan extension* of $f$.

**Proposition 6.2.4.2.** *Let $C$ be a $\mathbf{U}$-small $(\infty, \omega)$-category, $f : I \to B^\sharp$ a functor between $\mathbf{U}$-small $(\infty, \omega)$-categories and $g : I \to \underline{\operatorname{Hom}}(C, \underline{\omega})$ a functor. The functor $g$ then corresponds to a morphism $\tilde{g} : \underline{\operatorname{Hom}}_\odot(C^\sharp \times I, \underline{\omega})$. The left Kan extension of $f$ along $g$ corresponds to the morphism $(id_{C^\sharp} \times f)_! \tilde{g}$.*

*Proof.* This is a direct consequence of corollary 6.2.2.7.

360

6.2. YONEDA LEMMA AND APPLICATIONS

Corollary 6.2.4.3. Let $i : A \to B$ be a morphism between U-small $(\infty, \omega)$-categories. The left Kan extension of the Yoneda embedding $y : A \to \widehat{A}$ along $i$ is $N_i : B \to \widehat{A}$.

Proof. According to proposition 6.2.4.2, the desired left Kan extension is given by

$$(B^t \times i)_! \operatorname{hom}_B$$

which is $N_i$ according to lemma 6.2.1.17.

Proposition 6.2.4.4. Let $i : A \to B$ a functor between U-small $(\infty, \omega)$-categories. The left Kan extension of $y^B \circ i$ along $y^A$ is given by $i_!$.

Proof. Let $i : A \to B$ be any functor. Remark first that the Yoneda lemma and the corollary 6.2.4.3 imply that the left Kan extension of $y : A \to \widehat{A}$ along $y : A \to \widehat{A}$ is the identity of $\widehat{A}$. We then have a sequence of equivalences

$$\begin{array}{l} \operatorname{hom}_{\underline{\operatorname{Hom}}(\widehat{A}, \widehat{A})}(i_!, f) \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(\widehat{A}, \widehat{A})}(id, i^* \circ f) \quad (6.2.2.7) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{A})}(y_A, i^* \circ f \circ y^A) \quad (\text{Yoneda lemma}) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(i_! \circ y^A, f \circ y^A) \quad (6.2.2.7) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(y_B \circ i, f \circ y^A) \quad (6.2.3.3) \end{array}$$

natural in $f : \underline{\operatorname{Hom}}(\widehat{A}, \widehat{B})$.

Corollary 6.2.4.5. For any morphism $A \to B$ between U-small $(\infty, \omega)$-categories with $B$ lax U-cocomplete, there exists a unique colimit preserving functor $\widehat{A} \to B$ extending $i$.

Proof. Let $|\_|_i : \widehat{A} \to B$ be the functor defined in corollary 6.2.3.27. As this functor is an extension of $A$, it fulfills the desired condition, that shows the existence. The $(\infty, \omega)$-category of functors verifying the desired property is given by the pullback

$$\begin{array}{ccc} \underline{\operatorname{Hom}}_!(\widehat{A}, B)_i & \longrightarrow & \underline{\operatorname{Hom}}_!(\widehat{A}, B) \\ \downarrow & & \downarrow \\ \{i\} & \longrightarrow & \underline{\operatorname{Hom}}(A, B) \end{array}$$

where $\underline{\operatorname{Hom}}_!(\widehat{A}, B)$ is the full sub $(\infty, \omega)$-category of $\underline{\operatorname{Hom}}(\widehat{A}, B)$ whose objects are colimit preserving functors. As $|\_|_i$ is the left Kan extension of $i$ along the Yoneda embedding, there is a transformation

$$|_|_i \to h$$

natural in $h : \underline{\operatorname{Hom}}(\widehat{A}, B))_i$. To conclude, one has to show that for any object $h$ of $\underline{\operatorname{Hom}}(\widehat{A}, B))_i$, $|\_|_i \to h$ is an equivalence, and so that for any object $f$ of $\widehat{A}$, $|f|_i \to h(f)$ is an equivalence. As $f$ is a lax colimit of representables as shown in theorem 6.2.3.24 and as both $|\_|_i$ and $h$ preserve lax colimits, this is immediate.

361

CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**Corollary 6.2.4.6.** Let $A, B$ and $C$ be three $\mathbf{U}$-small $(\infty, \omega)$-categories with $B$ lax $\mathbf{U}$-cocomplete, and $i : A \to C$ and $f : A \to B$ two functors. The left Kan extension of $i$ along $f$ is given by the composite functor.

$$B \xrightarrow{N_f} \widehat{A} \xrightarrow{i_!} \widehat{C} \xrightarrow{\text{laxcolim}} C$$

*Proof.* We have a sequence of equivalences

$$\begin{array}{l} \operatorname{hom}_{\underline{\operatorname{Hom}}(C, B)}(\text{laxcolim } \circ i_! \circ N_f, h) \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(C, \widehat{A})}(N_f, i^* \circ y^B \circ h) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{A})}(y^A, i^* \circ y^B \circ h \circ f) \quad (6.2.4.3) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(i_! \circ y^A, y^B \circ h \circ f) \quad (6.2.2.7) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(y^B \circ i, y^B \circ h \circ f) \quad (6.2.3.3) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, B)}(i, h \circ f) \quad (6.2.1.16) \end{array}$$

natural in $h : \underline{\operatorname{Hom}}(C, B)$.

362

# Index of symbols

|  $(0, n)$-cat ... 28 | $(\_)^op$  |
| --- | --- |
|  $(0, \omega)$-cat ... 28 | *for* $(\infty, \omega)$-categories ... 199  |
|  $(0, \omega)$-cat_{B} ... 45 | *for* $\underline{\omega}$ ... 310  |
|  $(0, \omega)$-cat_{m} ... 234 | *for* $(0, \omega)$-categories ... 27  |
|  $(\infty, n)$-cat ... 193 | *for marked* $(\infty, \omega)$-categories ... 237  |
|  $(\infty, \omega)$-cat ... 186 | $(\_)^t$  |
|  $(\infty, \omega)$-cat_{m} ... 237 | *for* $(\infty, \omega)$-categories ... 199  |
|  $(\infty, \omega, 1)$-cat ... 303 | *for* $\underline{\omega}$ ... 310  |
|  $(\_)^\sharp$ | *for* $(0, \omega)$-categories ... 27  |
|  *for (marked)* $(\infty, \omega)$-categories . 235 | *for marked* $(\infty, \omega)$-categories ... 237  |
|  *for (marked)* $(0, \omega)$-categories ... 234 | $(\_)^o$  |
|  $(\_)^b$ | *for* $(\infty, \omega)$-categories ... 199  |
|  *for (marked)* $(\infty, \omega)$-categories . 235 | *for* $\underline{\omega}$ ... 310  |
|  *for (marked)* $(0, \omega)$-categories ... 234 | *for* $(0, \omega)$-categories ... 27  |
|  $(\_)^\sharp$ | *for augmented directed complexes* 46  |
|  *for (marked)* $(\infty, \omega)$-categories . 235 | *for marked* $(\infty, \omega)$-categories ... 237  |
|  *for (marked)* $(0, \omega)$-categories ... 234 | $(\_)_o$ ... 85  |
|  *for stratified Segal A-precategories* | $(\_)_mk$ ... 72  |
|  118 | $\otimes$  |
|  $(\_)^\sharp_n$ ... 236 | *for* $(\infty, \omega)$-categories ... 207  |
|  $(\_)^S$ | *for* $(0, \omega)$-categories ... 54  |
|  *for* $(\infty, \omega)$-categories ... 199 | *for marked simplicial sets* ... 77  |
|  *for* $\underline{\omega}$ ... 310 | *for stratified simplicial sets* ... 77  |
|  *for* $(0, \omega)$-categories ... 27 | $\otimes_n$ ... 210  |
|  *for marked* $(\infty, \omega)$-categories ... 237 | $\ominus$  |
|  $(\_)^\infty$ | *for* $(\infty, \omega)$-categories ... 211  |
|  *for* $(\infty, \omega)$-categories ... 199 | *for marked* $(\infty, \omega)$-categories ... 250  |
|  *for* $\underline{\omega}$ ... 310 | $\diamond$ ... 80  |
|  *for* $(0, \omega)$-categories ... 27 | $\star$ ... 82  |
|  *for marked* $(\infty, \omega)$-categories ... 237 | $\_ \otimes [1]$  |

363

INDEX OF SYMBOLS

|  *for* (∞, ω)-categories ... 207 | [3]^{eq} ... 74  |
| --- | --- |
|  *for* (0, ω)-categories ... 54 | [n]^{2} ... 74  |
|  *for augmented directed complexes* 48 | ≥_{n} ... 152  |
|  *for marked simplicial sets* ... 84 | □ ... 69  |
|  _ ⊗ [1]^{2} ... 247 | ADC ... 40  |
|  _ * 1 | ADC_{B} ... 44  |
|  *for* (∞, ω)-categories ... 208 | C^{[1]}^{2} ... 247  |
|  *for* (0, ω)-categories ... 55 | C^{[1]} ... 208  |
|  *for augmented directed complexes* 48 | Ĉ ... 338  |
|  *for marked* (∞, ω)-categories ... 249 | C(a, b) ... 80  |
|  *for marked simplicial sets* ... 84 | C_{/c}  |
|  1 ^{co} _ | *for* (∞, ω)-categories ... 208  |
|  *for* (∞, ω)-categories ... 208 | *for marked* (∞, ω)-categories ... 250  |
|  *for* (0, ω)-categories ... 55 | *for marked simplicial sets* ... 84  |
|  *for augmented directed complexes* 48 | C_{c/}  |
|  *for marked* (∞, ω)-categories ... 249 | *for* (∞, ω)-categories ... 208  |
|  *for marked simplicial sets* ... 84 | *for marked* (∞, ω)-categories ... 250  |
|  [_, 1] | *for marked simplicial sets* ... 84  |
|  *for* (∞, ω)-categories ... 188 | C_{/} ... 311  |
|  *for* (0, ω)-categories ... 27 | C_{S} ... 183  |
|  *for augmented directed complexes* 50 | D_{n}  |
|  *for marked* (∞, ω)-categories ... 238 | *for* (0, ω)-categories ... 26  |
|  [a, n] ... 29 | *for marked simplicial sets* ... 93  |
|  [a, n] | Δ^{2}_{/[n]} ... 129  |
|  *for A-Segal precategories* ... 115 | Δ^{3}_{/[n]} ... 126  |
|  *for* (0, ω)-categories ... 29 | Δ[Θ] ... 33  |
|  [a_{0}, n_{0}] ∨ [a_{1}, n_{1}] ∨ ... ∨ [a_{k}, n_{k}] | Δ[Θ_{n}] ... 33  |
|  *for* Θ ... 29 | (D_{n})_{t} ... 234  |
|  *for Segal A-precategories* ... 116 | E^{⊗} ... 117  |
|  ⟨a, n⟩ ... 302 | E^{eq} ... 32  |
|  [e, 1]_{t} ... 119 | e * _ ... 129  |
|  [e, 1]_{t} ∨ [a, n] ... 123 | ev ... 339  |
|  ⊥ ... 285 | F ... 258  |
|  [n]_{t} ... 74 | F ... 183  |
|  [n]^{k} ... 74 | f_{1} : C_{/c} → C_{d/} ... 184  |
|  ([n]^{k})' ... 74 | f^{*} : C_{/d} → C_{c/} ... 184  |
|  ([n]^{k})'' ... 74 | f_{*} : C_{/c} → C_{d/} ... 184  |

364

INDEX OF SYMBOLS

|  $f_! : \underline{\text{LCart}}^c(I) \rightarrow \underline{\text{LCart}}(A^\sharp)$ | 296 | M | 33  |
| --- | --- | --- | --- |
|  $f^* : \underline{\text{LCart}}^c(J) \rightarrow \underline{\text{LCart}}^c(I)$ | 294 | $\text{Map}(\_, \_)$ | 283  |
|  $f_* : \underline{\text{LCart}}^c(I) \rightarrow \underline{\text{LCart}}(A^\sharp)$ | 297 | $m_C$ | 211  |
|  $f_! : \underline{\text{Hom}}_\ominus(I, \underline{\omega}) \rightarrow \underline{\text{Hom}}(A, \underline{\omega})$ | 331 | $m_{C^1}$ | 250  |
|  $f^* : \underline{\text{Hom}}_\ominus(I, \underline{\omega}) \rightarrow \underline{\text{Hom}}_\ominus(J, \underline{\omega})$ | 331 | $\text{mPsh}_M(\_)$ | 72  |
|  $f_* : \underline{\text{Hom}}_\ominus(I, \underline{\omega}) \rightarrow \underline{\text{Hom}}(A, \underline{\omega})$ | 331 | $\text{mPsh}(\Delta)$ | 75  |
|  $F_g$ | 267 | $\text{M}_{\text{Sat}}$ | 33  |
|  $\mathbf{F}h^C$ | 311 | $\text{M}_{\text{Seg}}$ | 33  |
|  $\mathbf{F}h_a^A$ | 310 | $\text{mSeg}(A)$ | 143  |
|  $\text{Fun}^c([\_], \_)$ | 323 | $N : (0, \omega)\text{-cat} \rightarrow \text{mPsh}(\Delta)$ | 85  |
|  $h_a^A$ | 310 | $N : (0, \omega)\text{-cat} \rightarrow \text{tSeg}(\text{tPsh}(\Delta))$ | 162  |
|  $\underline{\text{Hom}}_\ominus(\_, \_)$ | 330 | $\nabla_{k,n}$ | 202  |
|  $\text{hom}_(\_, \_)$ |  | $N_{(\omega,1)}$ | 305  |
|  *for $(\infty, \omega)$-categories* | 188 | $\nu : \text{ADC} \rightarrow \omega\text{-cat}$ | 41  |
|  *for marked $(\infty, \omega)$-categories* | 238 | $\partial_C$ | 313  |
|  $\underline{\text{Hom}}(\_, \_)$ | 195 | $\partial_{n,I}$ | 320  |
|  I | 258 | $\partial_{n,I}^c$ | 323  |
|  $I_g$ | 267 | $\partial_n^+$ | 43  |
|  Im | 200 | $\partial_n^-(\_)$ | 43  |
|  $\oint_{n,I}$ | 320 | $\pi_0 : (\infty, \omega)\text{-cat} \rightarrow (0, \omega)\text{-cat}$ | 186  |
|  $I \otimes \_$ | 127 | $\pi_0 : (\infty, \omega)\text{-cat}_m \rightarrow (0, \omega)\text{-cat}_m$ | 238  |
|  $i_{str}$ | 86 | $\text{Psh}^\infty(\_)$ | 175  |
|  J | 303 | $R : \text{mPsh}(\Delta) \rightarrow (0, \omega)\text{-cat}$ | 85  |
|  $\lambda : \omega\text{-cat} \rightarrow \text{ADC}$ | 40 | $R : \text{tSeg}(\text{tPsh}(\Delta)) \rightarrow (0, \omega)\text{-cat}$ | 162  |
|  $\text{Lan}_f g$ | 360 | $r_C : C \rightarrow C_{mk}$ | 143  |
|  laxcolim | 351 | $\text{RCart}(\_)$ | 283  |
|  $\text{laxcolim} : \widehat{C} \rightarrow C$ | 359 | $\mathbf{R}f^* : (C_{/d})_{S_{d/}} \rightarrow (C_{c/})_{S_{c/}}$ | 184  |
|  laxlim | 351 | $\mathbf{R}f_* : (C_{/c})_{S_{c/}} \rightarrow (C_{d/})_{S_{d/}}$ | 184  |
|  $\text{LCart}(\_)$ | 283 | $\mathbf{R}G$ | 184  |
|  $\text{LCart}^c(\_)$ | 283 | $R_S$ | 182  |
|  $\underline{\text{LCart}}(\_)$ | 293 | $\widehat{S}$ | 177  |
|  $\underline{\text{LCart}}^c(\_)$ | 293 | $S_{/c}$ | 184  |
|  $\mathbf{L}F$ | 184 | $\text{Seg}(A)$ | 115  |
|  $\mathbf{L}f_! : (C_{/c})_{S_{c/}} \rightarrow (C_{d/})_{S_{d/}}$ | 184 | $\Sigma_-$ | 80  |
|  $\mathbf{L}f^* : (C_{/d})_{S_{d/}} \rightarrow (C_{c/})_{S_{c/}}$ | 184 | $\Sigma^n$ |   |
|  $\text{LFib}(\_)$ | 304 | *for $(\infty, \omega)$-categories* | 32  |
|  $L_S$ | 182 | *for $(0, \omega)$-categories* | 28  |

365

INDEX OF SYMBOLS

|  Σ° | 132  |
| --- | --- |
|  Σ* | 82  |
|  [1] ∀ΣX | 83  |
|  ΣX ∀ [1] | 83  |
|  Sp_{a} | 32  |
|  Sq(i, p) | 178  |
|  $$\overline{S}$$ | 34  |
|  T | 302  |
|  tΔ[tΘ] | 235  |
|  tPsh^{∞}(Θ) | 234  |
|  tΘ | 234  |
|  τ_{n} |   |
|  for (∞, ω)-category | 193  |
|  for (0, ω)-categories | 28  |
|  for marked simplicial sets | 76  |
|  τ_{n}^{i} |   |
|  for (∞, ω)-categories | 193  |
|  for (0, ω)-categories | 28  |
|  for marked simplicial sets | 76  |
|  for stratified Segal A-precategories | 141  |
|  Θ | 29  |
|  Θ_{n} | 30  |
|  tM | 236  |
|  tPsh_{M}(B) | 70  |
|  tPsh(Δ) | 74  |
|  tPsh(Δ)^{n} | 75  |
|  tSeg(A) | 118  |
|  tW | 236  |
|  W | 32  |
|  W_{Sat} | 32  |
|  W_{Seg} | 32  |
|  y | 338  |
|  N : (0, ω)-cat → (∞, ω)-cat | 186  |
|  N : (0, ω)-cat_{m} → (∞, ω)-cat_{m} | 238  |

366

# Index of notions

## A

adjoint structure ... 343
algebraic morphism of $\Theta$ ... 31
array ... 41
atomic basis ... 45

## B

basis
    for $(\infty, \omega)$-categories ... 44
    for augmented directed complexes ... 43
Beck-Chevaley condition ... 287

## C

$\omega$-category ... 25
$(0, \omega)$-category ... 28
$(0, n)$-category ... 28
$(\infty, n)$-category ... 193
$(\infty, \omega)$-category ... 186
$(\infty, \omega, 1)$-category ... 303
$n$-cell
    for $(\infty, \omega)$-categories ... 186
    for $(0, \omega)$-categories ... 25
    for marked simplicial sets ... 93
classified left cartesian fibration ... 276
closed under left or right cancellation ... 177
co-join ... 82
cocomplete $\infty$-groupoid of arrows ... 177
coherent array ... 42
completeness extensions ... 117
complicial horn inclusions ... 75
complicial set ... 75

complicial thinness extensions ... 75

## D

degenerate morphism of $\Theta$ ... 30
degeneration partition operator ... 76
degree of an element of $\Delta^3_{[n]}$ ... 133
D-equivalence ... 97
diamond product ... 80
dimension of a globular sum ... 30
discrete Conduché functor
    for $(\infty, \omega)$-categories ... 202
    for marked $(\infty, \omega)$-categories ... 239
discrete objects ... 115
D-trivial fibration ... 97
dualities
    for $(\infty, \omega)$-categories ... 199
    for $\underline{\omega}$ ... 310
    for $(0, \omega)$-categories ... 27

## E

elegant Reedy category ... 30
elementary anodyne extension
    for Segal A-precategory ... 117
    for stratified simplicial sets ... 74
entire morphism ... 70
epimorphism ... 200
equivalence ... 28
equivalence of marked Segal A-categories ... 119
equivalent $n$-cells ... 93
essentially surjective

367

INDEX OF NOTIONS

|  *for marked simplicial sets* ...100 | *for augmented directed complexes* 48  |
| --- | --- |
|  even duality | *for marked (∞, ω)-categories* ... 249  |
|  *for (∞, ω)-categories* ...199 | *for marked simplicial sets* ...84  |
|  *for ω* ...310 | Gray cone  |
|  *for (0, ω)-categories* ...27 | *for (∞, ω)-categories* ...208  |
|  *for marked (∞, ω)-categories* ...237 | *for (0, ω)-categories* ...55  |
|  *b*-exponentiable ...271 | *for augmented directed complexes* 48  |
|   | *for marked (∞, ω)-categories* ... 249  |
|   | *for marked simplicial sets* ...84  |
|  **F** | Gray cylinder  |
|  face partition operator ...77 | *for (∞, ω)-categories* ...207  |
|  factorization system in (L, R) ...178 | *for (0, ω)-categories* ...54  |
|  final morphism ...258 | *for augmented directed complexes* 48  |
|  full duality | *for marked (∞, ω)-categories* ... 247  |
|  *for (∞, ω)-categories* ...199 | *for marked simplicial sets* ...84  |
|  *for ω* ...310 | *n*-Gray cylinder  |
|  *for (0, ω)-categories* ...27 | *for (∞, ω)-categories* ...207  |
|  *for augmented directed complexes* 46 | *for (0, ω)-categories* ...54  |
|  *for marked (∞, ω)-categories* ...237 | *for augmented directed complexes* 48  |
|  fully faithful | *for marked (∞, ω)-categories* ... 247  |
|  *for (∞, ω)-categories* ...202 | *for marked simplicial sets* ...84  |
|  *for marked (∞, ω)-categories* ...239 | *n*-Gray cylinder ...210  |
|  *for marked simplicial sets* ...100 | Gray module ...125  |
|  **G** | Gray tensor product  |
|  generated by composition ...44 | *for (∞, ω)-categories* ...207  |
|  generating Reedy cofibrations ...117 | *for (0, ω)-categories* ...54  |
|  global left Kan extension ...360 | *for augmented directed complexes* 47  |
|  *n*-globe | *for marked (∞, ω)-categories* ...241  |
|  *for marked simplicial sets* ...93 | *for marked simplicial sets* ...77  |
|  *for (0, ω)-categories* ...26 | *for stratified simplicial sets* ...77  |
|  globular morphism | Grothendieck construction ...311  |
|  *for (0, ω)-categories* ...31 |   |
|  *for marked (0, ω)-categories* ...239 | **I**  |
|  globular set ...25 | image of a morphism ...200  |
|  globular sum ...29 | initial morphism ...258  |
|  Gray o-cone | intelligent *n*-truncation  |
|  *for (∞, ω)-categories* ...208 | *for (∞, ω)-categories* ...193  |
|  *for (0, ω)-categories* ...55 | *for (0, ω)-categories* ...28  |
|   | *for marked simplicial sets* ...76  |
|   | isomorphism for an arrow $x : [e, 1] \rightarrow C$  |
|   | 117  |
|  **L** |   |
|  lax U-cocomplete ...351 |   |

368

INDEX OF NOTIONS

|  lax U-complete | 351 | monomorphism | 200  |
| --- | --- | --- | --- |
|  lax colimit | 351 |  |   |
|  lax limit | 351 | **N** |   |
|  left and right deformation retract | 255 | nice model structure | 68  |
|  left cancellable *n*-cell | 268 |  |   |
|  left fibration | 303 | **O** |   |
|  left Kan extension | 360 | odd duality |   |
|  left or right *k*-Gray deformation retract | 212 | *for* (∞, ω)-categories | 199  |
|  left or right *k*-Gray deformation retract |  | *for* ω | 310  |
|  structure | 212 | *for* (0, ω)-categories | 27  |
|  left or right adjoint | 343 | *for marked* (∞, ω)-categories | 237  |
|  left or right cancellable 1-cell | 265 | opposed Beck-Chevaley condition | 289  |
|  left or right cartesian fibration | 260 | oriental | 85  |
|  left or right deformation retract | 254 |  |   |
|  left or right Gray deformation retract | 254 | **P** |   |
|  left or right Gray deformation retract |  | polygraph | 27  |
|  structure | 254 | precocomplete set of arrows | 34  |
|  lift in a square | 178 | (∞, ω)-presheaves | 338  |
|  *S*-local | 183 | proper morphism | 284  |
|  locally U-small (∞, ω)-category | 336 |  |   |
|  loop free basis |  | **Q** |   |
|  *for* (0, ω)-categories | 45 | quasi-rigid morphism | 46  |
|  *for augmented directed complexes* | 44 |  |   |
|  **M** |  | **R** |   |
|  marked (∞, ω)-category | 237 | Reedy category | 30  |
|  marked (0, ω)-category | 233 | regular elements of Δ^{3}_{/[n]} | 133  |
|  marked *n*-cell |  | regular morphism | 74  |
|  *for marked* (∞, ω)-categories | 237 | *n*-relying on *x* | 151  |
|  *for marked* (0, ω)-categories | 233 | *n*-relying on *x* and *x'* | 152  |
|  marked globular sum | 239 | representable (∞, ω)-presheaves | 338  |
|  marked morphism | 234 |  |   |
|  marked presheaf on *B* | 72 | **S** |   |
|  marked Segal *A*-category | 119 | saturation extensions | 75  |
|  marked Segal *A*-precategory | 143 | Segal *A*-category | 117  |
|  marked simplicial set | 75 | Segal *A*-precatagory | 115  |
|  marked trivialization | 259 | Segal extensions | 117  |
|   |  | slice over |   |
|   |  | *for* (∞, ω)-categories | 208  |
|   |  | *for marked* (∞, ω)-categories | 250  |
|   |  | *for marked simplicial sets* | 84  |

369

INDEX OF NOTIONS

|  slice under | *for stratified Segal A-precategories*  |
| --- | --- |
|  *for* (∞, ω)-*categories* ... 208 | 141  |
|  *for marked* (∞, ω)-*categories* ... 250 |   |
|  *for marked simplicial sets* ... 84 |   |
|  U-small left cartesian fibration ... 320 |   |
|  U-small object of (∞, ω, 1)-cat_{/A} ... 309 |   |
|  smooth morphism ... 284 |   |
|  special colimit |   |
|  *for* (∞, ω)-*categories* ... 189 |   |
|  *for marked* (∞, ω)-*categories* ... 240 |   |
|  stratified ∞-presheaf on Δ[Θ] ... 235 |   |
|  stratified ∞-presheaf on Θ ... 234 |   |
|  stratified morphism ... 70 |   |
|  stratified presheaf on B ... 70 |   |
|  stratified Segal A-precatagory ... 118 |   |
|  stratified simplicial set ... 74 |   |
|  Street endofunctor ... 86 |   |
|  strict (∞, ω)-category ... 186 |   |
|  strict marked (∞, ω)-category ... 238 |   |
|  suspension |   |
|  *for* (∞, ω)-*categories* ... 188 |   |
|  *for* (0, ω)-*categories* ... 27 |   |
|  *for augmented directed complexes* 50 |   |
|  *for marked* (∞, ω)-*categories* ... 238 |   |
|  *for marked simplicial sets* ... 80 |   |
|  ○-suspension ... 132 |   |
|  **T** |   |
|  thin simplex ... 74 |   |
|  transposition |   |
|  *for* (∞, ω)-*categories* ... 199 |   |
|  *for* ω ... 310 |   |
|  *for* (0, ω)-*categories* ... 27 |   |
|  *for marked* (∞, ω)-*categories* ... 237 |   |
|  n-truncation |   |
|  *for* (∞, ω)-*category* ... 193 |   |
|  *for* (0, ω)-*categories* ... 28 |   |
|  *for marked simplicial sets* ... 76 |   |
|   | **U**  |
|   | unique left or right lifting property . 178  |
|   | unit and counit of an adjunction ... 344  |
|   | unitary basis ... 44  |
|   | **W**  |
|   | weak Beck-Chevaley condition ... 287  |
|   | weak factorization system in (L, R) . 178  |
|   | **Y**  |
|   | Yoneda embedding ... 338  |
|   | **Z**  |
|   | zigzag of acyclic cofibration ... 69  |

370

# Bibliography

[AGOR23] Dimitri Ara, Andrea Gagna, Viktoriya Ozornova, and Martina Rovelli. A categorical characterization of strong steiner $\omega$-categories. *Journal of Pure and Applied Algebra*, 227(7):107313, 2023.

[AM20] Dimitri Ara and Georges Maltsiniotis. *Joint et tranches pour les $\infty$-catégories strictes*. Société Mathématique de France, 2020.

[Ara10] Dimitri Ara. *Sur les $\infty$-groupoïdes de Grothendieck et une variante $\infty$-catégorique*. PhD thesis, Université Paris 7, 2010.

[Ara14] Dimitri Ara. Higher quasi-categories vs higher rezk spaces. *Journal of K-theory*, 14(3):701–749, 2014.

[BD95] John C Baez and James Dolan. Higher-dimensional algebra and topological quantum field theory. *Journal of mathematical physics*, 36(11):6073–6105, 1995.

[Ber02] Clemens Berger. A cellular nerve for higher categories. *Advances in Mathematics*, 169(1):118–175, 2002.

[BOR21] Julia E Bergner, Viktoriya Ozornova, and Martina Rovelli. An explicit comparison between 2-complicial sets and $\theta_2$-spaces. *arXiv preprint arXiv:2104.13292*, 2021.

[BR13a] Julia E Bergner and Charles Rezk. Comparison of models for $(\infty, n)$-categories, i. *Geometry & Topology*, 17(4):2163–2202, 2013.

[BR13b] Julia E Bergner and Charles Rezk. Reedy categories and the $\theta$-construction. *Mathematische Zeitschrift*, 274(1-2):499–514, 2013.

[BR20] Julia E Bergner and Charles Rezk. Comparison of models for $(\infty, n)$-categories, ii. *Journal of Topology*, 13(4):1554–1581, 2020.

371

# BIBLIOGRAPHY

[BSP21] Clark Barwick and Christopher Schommer-Pries. On the unicity of the theory of higher categories. *Journal of the American Mathematical Society*, 34(4):1011–1058, 2021.

[Cis06] Denis-Charles Cisinski. *Les préfaiseaux comme modèles des types d'homotopie*. Société mathématique de France, 2006.

[Cis19] Denis-Charles Cisinski. *Higher categories and homotopical algebra*, volume 180. Cambridge University Press, 2019.

[CN22] Denis-Charles Cisinski and Hoang Kim Nguyen. The universal cocartesian fibration. *arXiv preprint arXiv:2210.08945*, 2022.

[CNW] Denis-Charles Cisinski, Hoang Kim Nguyen, and Tashi Walde. Univalent directed type theory. *in preparation*.

[CS19] Damien Calaque and Claudia Scheimbauer. A note on the $(\infty, n)$-category of cobordisms. *Algebraic & Geometric Topology*, 19(2):533–655, 2019.

[DKM21] Brandon Doherty, Chris Kapulkin, and Yuki Maehara. Equivalence of cubical and simplicial approaches to $(\infty, n)$-categories. *arXiv preprint arXiv:2106.09428*, 2021.

[Dug01] Daniel Dugger. Replacing model categories with simplicial ones. *Transactions of the American Mathematical society*, 353(12):5003–5027, 2001.

[GHL20] Andrea Gagna, Yonatan Harpaz, and Edoardo Lanari. Fibrations and lax limits of $(\infty, 2)$-categories. *arXiv preprint arXiv:2012.04537*, page 2, 2020.

[GHL21] Andrea Gagna, Yonatan Harpaz, and Edoardo Lanari. Cartesian fibrations of $(\infty, 2)$-categories. *arXiv preprint arXiv:2107.12356*, 2021.

[GHL22] Andrea Gagna, Yonatan Harpaz, and Edoardo Lanari. On the equivalence of all models for $(\infty, 2)$-categories. *Journal of the London Mathematical Society*, 106(3):1920–1982, 2022.

[GHN] D Gepner, R Haugseng, and Th Nikolaus. Lax colimits and free fibrations in $\infty$-categories (2015). *Preprint. arXiv*, 1501.

[GOR21] Andrea Gagna, Viktoriya Ozornova, and Martina Rovelli. Nerves and cones of free loop-free $\omega$-categories. *arXiv preprint arXiv:2103.01066*, 2021.

372

BIBLIOGRAPHY

[GP21] Daniel Grady and Dmitri Pavlov. The geometric cobordism hypothesis. *arXiv preprint arXiv:2111.01095*, 2021.

[GR19] Dennis Gaitsgory and Nick Rozenblyum. *A study in derived algebraic geometry: Volume I: correspondences and duality*, volume 221. American Mathematical Society, 2019.

[Gra06] John Walker Gray. *Formal category theory: adjointness for 2-categories*, volume 391. Springer, 2006.

[GS21] Fernando Abellán García and Walker H Stern. 2-cartesian fibrations i: A model for ∞-bicategories fibred in ∞-bicategories. *arXiv preprint arXiv:2106.03606*, 2021.

[GS22] Fernando Abellán García and Walker H Stern. 2-cartesian fibrations ii: The grothendieck construction. *arXiv preprint arXiv:2201.09589*, 2022.

[Gue18] Léonard Guetta. Polygraphs and discrete conduché ω-functors. *arXiv preprint arXiv:1812.05332*, 2018.

[Hei20] Hadrian Heine. An equivalence between enriched ∞-categories and ∞-categories with weak action. *arXiv preprint arXiv:2009.02428*, 2020.

[Hin21] Vladimir Hinich. Colimits in enriched ∞-categories and day convolution. *arXiv preprint arXiv:2101.09538*, 2021.

[Hir03] Philip S Hirschhorn. *Model categories and their localizations*. Number 99. American Mathematical Soc., 2003.

[HL23] Simon Henry and Felix Loubaton. An inductive model structure for strict ∞-categories. 2023.

[hsp] Chris Schommer-Pries (https://mathoverflow.net/users/184/chris-schommer-pries). Is there an accepted definition of (∞, ∞) category? MathOverflow. URL:https://mathoverflow.net/q/134099 (version: 2017-12-15).

[Joy] André Joyal. Factorisation systems. joyalscatlab. URL:https://ncatlab.org/joyalscatlab/show/Factorisation+systems.

[Joy02] André Joyal. Quasi-categories and kan complexes. *Journal of Pure and Applied Algebra*, 175(1-3):207–222, 2002.

373

# BIBLIOGRAPHY

[JT07] André Joyal and Myles Tierney. Quasi-categories vs segal spaces. *Contemporary Mathematics*, 431(277-326):10, 2007.

[Lou21] Félix Loubaton. Conditions de kan sur les nerfs des $\omega$-catégories. *arXiv preprint arXiv:2102.04281*, 2021.

[Lou22a] Félix Loubaton. Dualities in the complicial model of $\infty$-categories. *arXiv preprint arXiv:2203.11845*, 2022.

[Lou22b] Félix Loubaton. $n$-complicial sets as a model of $(\infty, n)$-categories. *arXiv preprint arXiv:2207.08504*, 2022.

[Lur08] Jacob Lurie. On the classification of topological field theories. *Current developments in mathematics*, 2008(1):129–280, 2008.

[Lur09a] Jacob Lurie. *Higher topos theory*. Princeton University Press, 2009.

[Lur09b] Jacob Lurie. $(\infty, 2)$-categories and the goodwillie calculus i. *arXiv preprint arXiv:0905.0462*, 2009.

[Mae23] Yuki Maehara. Orientals as free weak $\omega$-categories. *Journal of Pure and Applied Algebra*, 227(3):107230, 2023.

[Nor19] Paige Randall North. Towards a directed homotopy type theory. *Electronic Notes in Theoretical Computer Science*, 347:223–239, 2019.

[Nui21] Joost Nuiten. On straightening for segal spaces. *arXiv preprint arXiv:2108.11431*, 2021.

[OR20a] Viktoriya Ozornova and Martina Rovelli. Fundamental pushouts of $n$-complicial sets. *arXiv preprint arXiv:2005.05844*, 2020.

[OR20b] Viktoriya Ozornova and Martina Rovelli. Model structures for $(\infty, n)$-categories on (pre) stratified simplicial sets and prestratified simplicial spaces. *Algebraic & Geometric Topology*, 20(3):1543–1600, 2020.

[OR22] Viktoriya Ozornova and Martina Rovelli. A quillen adjunction between globular and complicial approaches to $(\infty, n)$-categories. *arXiv preprint arXiv:2206.02689*, 2022.

[ORV20] Viktoriya Ozornova, Martina Rovelli, and Dominic Verity. Gray tensor product and saturated $n$-complicial sets. *arXiv preprint arXiv:2007.01235*, 2020.

374

BIBLIOGRAPHY

[Ras21] Nima Rasekh. Yoneda lemma for $\mathcal{D}$-simplicial spaces. *arXiv preprint arXiv:2108.06168*, 2021.

[Rez10] Charles Rezk. A cartesian presentation of weak $n$-categories. *Geometry & Topology*, 14(1):521–571, 2010.

[Rie16] Emily Riehl. Complicial sets, an overture, 2016.

[RS17] Emily Riehl and Michael Shulman. A type theory for synthetic $\infty$-categories. *arXiv preprint arXiv:1705.07442*, 2017.

[RV22] Emily Riehl and Dominic Verity. *Elements of $\infty$-Category Theory*, volume 194. Cambridge University Press, 2022.

[Sim11] Carlos Simpson. *Homotopy Theory of Higher Categories: From Segal Categories to $n$-Categories and Beyond*, volume 19. Cambridge University Press, 2011.

[Ste04] Richard Steiner. $\omega$-categories and chain complexes. *Homology, Homotopy and Applications*, 6(1):175 – 200, 2004.

[Str87] Ross Street. The algebra of oriented simplexes. *Journal of Pure and Applied Algebra*, 49(3):283 – 335, 1987.

[Ver06] Dominic Verity. Weak complicial sets, a simplicial weak omega-category theory. part ii: nerves of complicial gray-categories. *arXiv preprint math/0604416*, 2006.

[Ver08a] Dominic Verity. Complicial sets. *Memoirs of the AMS*, 193(905), 2008.

[Ver08b] Dominic Verity. *Complicial Sets Characterising the Simplicial Nerves of Strict $\omega$-Categories*, volume 193. American Mathematical Soc., 2008.

[Ver08c] Dominic Verity. Weak complicial sets i. basic homotopy theory. *Advances in Mathematics*, 219(4):1081–1149, 2008.

[Ver17] Dominic Verity. A complicial compendium. *https://www.cirm-math.fr/ProgWeebly/Renc1773/Verity.pdf*, 2017.

[War11] Michael A Warren. The strict $\omega$-groupoid interpretation of type theory. *Models, logics, and higher-dimensional categories*, 53:291–340, 2011.

375

BIBLIOGRAPHY

376