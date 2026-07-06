However, it does not seem possible to give rules for computing décalage on a  \( \Pi \) -telescope that are similarly consistent. Fortunately, we will not need such rules. Of course, since décalage and  \( \Pi \) -telescopes both compute independently on telescopes extended by a type, so does their combination.

This concludes our description of the ambient syntax of dTT.

◀

## 3 Semi-Simplicial and Displayed Coinductive Types

Recall from the introduction that our primary goal in formulating dTT (at the moment) is to have a type theory in which we can make precise our coinductive definition of the type SST of semi-simplicial types. In this section we give that definition, making use of the 'display' primitives of dTT that was introduced in section 2. The basic definition is contained in section 3.1, followed by an exploration of some examples in section 3.2. Then in section 3.3 we describe a more general notion of 'displayed coinductive type' that has SST as a special case, and in section 3.4 we explore a few other examples of the general notion.

### 3.1 SEMI-SIMPLICIAL TYPES

In an ideal version of displayed type theory, one could define semi-simplicial types as an instance of a general codata declaration. We would expect to write this in a proof assistant with a syntax like the following, which generalises Agda-like syntax for records by allowing the coinductive input of each destructor to be specified explicitly and referred to in its type:

codata SST : Type where
Z : SST → Type
S : (A : SST) → Z A → SST\( ^{d} \) A

It is beyond the scope of this paper to give a sufficiently broad framework to generally encompass such definitions, but we will describe one general paradigmatic class of them, analogous to W-types as paradigmatic inductive types and M-types as paradigmatic coinductive types. However, we begin by discussing the concrete example of SST in more detail, to help motivate the general case.

#### 3.1.1 SST basics

We begin by giving the type formation law and destructors. Of course, since SST is a sort of 'universe', its elements consisting of types, it must also be parametrized by a level.

\(\Gamma \vdash_{sm} SST_{\ell} type_{lsuc \ell}\)

\(\Gamma \vdash_{sm} Z : ((\text{Type}_{\ell}))_{A : SST_{\ell}}\)

\(\Gamma \vdash_{sm} S : ((\text{SST}_{\ell}^{d} A))_{A : SST_{\ell}, a : EI(Z A)}\)

Note that the destructors are defined as terms belonging to 'meta-abstractions' as introduced in section 2.3.3. We have chosen this over the more common method of supplying the arguments in premises, e.g.

\(\frac{\Gamma \vdash_{sm} A : SST_{\ell}}{\Gamma \vdash_{sm} Z A : Type_{\ell}},\)

29