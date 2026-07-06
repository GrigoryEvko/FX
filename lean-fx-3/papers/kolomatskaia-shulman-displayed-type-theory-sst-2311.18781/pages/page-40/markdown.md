**Remark 4.1.** Actually we will not quite model all of dTT as presented in section 2: we omit the type-former $\triangle$ and its associated introduction and elimination rule. This is purely for reasons of simplicity and space. It should be possible to model $\triangle$ as well as long as the starting discrete model has a unit type, but we leave the details for the future. We will, however, still model $\triangle$-annotated variables and function types such as $(x : \triangle A) \to B x$.

In section 4.1 we review the semantics of ordinary dependent type theory, introduce some notation, extend this to our calculus of telescopes and meta-abstractions, and define what it means for such a model to have countable infinite limits. Then in section 4.2 we construct a model of augmented semi-simplicial Reedy diagrams, starting with any model of dependent type theory having countable infinite limits. This is essentially an instance of the general inverse diagram models constructed in [Shu15, KL21], but we give an explicit inductive construction that avoids category-theoretic machinery and builds display and décalage in from the beginning. In section 4.3 we add modalities to this model, and then in section 4.4 we discuss the *general* notion of model of dTT and show that the simplicial model is in fact such. Finally, in section 4.5 we construct displayed coinductive types in these models, including the type SST of semi-simplicial types.

## 4.1 THE SEMANTICS OF DEPENDENT TYPE THEORY

We approach semantics from the perspective of *Categories with Families* (CwF) [CCD21]. Here we will recount the relevant categorical concepts while providing a translation into language reminiscent of a type theoretic logical framework.

At the most basic level, a category with families is just a category with a terminal object and distinguished substructure of objects and morphisms that behave like *types* and *terms* in a dependent type theory. In the absence of any other structure, the only way in which this behaviour is manifested is through the presence of *substitution*, which categorically corresponds to a choice of definitionally functorial distinguished pullbacks. Here, instead of giving the substructure as a proposition on objects and morphisms, we first give it as presheaves, and then use representability to overlay this structure into the category.

### 4.1.1 Categories with Families

A 'CwF with levels' consists of a category $\mathcal{C}$, along with a chosen terminal object $\mathbb{I}$, and equipped with the data of two families of presheaves, indexed by $\ell$ level:

$$\text{Ty}_\ell : \mathcal{C}^{\text{op}} \to \text{Set} \quad \quad \quad \quad \quad \quad \quad \text{Tm}_\ell : \left( \int^{\mathcal{C}} \text{Ty}_\ell \right)^{\text{op}} \to \text{Set},$$

such that for every $\Gamma : \text{ob}_\mathcal{C}$ and $A : \text{Ty}_\ell \Gamma$, there is a chosen representation of the presheaf:

$$\Delta \mapsto \{\sigma : \text{mor}_\mathcal{C}(\Delta, \Gamma)\} \times \text{Tm}_\ell(\Delta, A^\sigma).$$

### 4.1.2 Notation

The objects of the category $\mathcal{C}$ are called *contexts* and denoted by $\Gamma, \Delta$. For $\Gamma : \text{ob}_\mathcal{C}$ we write:

$\Gamma$ ob

40