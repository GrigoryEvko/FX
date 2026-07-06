11:20

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

in a manner that makes the postulated equations hold. In this section we shall take on the task of decomposing these algebraic models into more tractable pieces.

A moment's thought reveals that many of the equations of the GAT given in Section 4 are rather close to the familiar notion of *categories with families* (CwFs) [Dyb96], which can be adapted to the present setting.$^{3}$ However, we will take things a bit further by opting for a category-theoretic reformulation of CwFs known as *natural models* [Awo18].

Natural models build on the view of CwFs as consisting of a presheaf of types (over the category of contexts), coupled with a presheaf of terms (over the elements of those types). We find this relatively recent technology helpful for two reasons. First, it concisely encodes the many naturality conditions normally required of a CwF. Second, it aids in uncovering the implicit universal properties of type-theoretic connectives, which are not quite so evident in the usual GAT-like formulation of CwFs.

In Section 5.1 we demonstrate how the basic notions of context, type, term, and context extension in MTT can be presented in terms of natural models. Then, in Section 5.2 we show how to interpret the various connectives—including the modality—in the language of natural models; this discussion concludes with a concise definition of a model of MTT in Section 5.2.5. Following that, in Section 5.3 we briefly discuss a strict notion of morphism of models.

## 5.1. Contexts, Types, and Terms.

5.1.1. *Contexts.* First, we observe that a model of our type theory must contain a set of contexts at each mode $m \in \mathcal{M}$. Equipped with the substitutions at the same mode, which can be composed associatively and have the identity substitution as a unit, these sets are readily seen to form a category—the *context category* at $m \in \mathcal{M}$—for which we write $\mathcal{C}[m]$.

Moreover, recall that for $\Gamma \operatorname{ctx} \otimes m$ and $\mu : n \rightarrow m$ we have a context $\Gamma, \widehat{\bullet}_{\mu} \operatorname{ctx} \otimes n$, and that this construction extends to substitutions in a functorial fashion. Hence, we will require for each modality $\mu : n \rightarrow m$ a functor

$$[\widehat{\bullet}_{\mu}] : \mathcal{C}[m] \rightarrow \mathcal{C}[n]$$

Similarly, each $\alpha : \mu \Rightarrow \nu$ induces a natural transformation. Accordingly, a model should come with a natural transformation

$$[\widehat{\bullet}_{\mu}^\alpha] : [\widehat{\bullet}_{\nu}] \Rightarrow [\widehat{\bullet}_{\mu}]$$

The equalities of the GAT require that the assignments $\mu \mapsto \widehat{\bullet}_{\mu}$ and $\alpha \mapsto \widehat{\bullet}_{\mu}^\alpha$ be strictly 2-functorial. Thus, this part of the model can be succinctly summarized as follows.

**Definition 5.1.** A *modal context structure* for a mode theory $\mathcal{M}$ is a (strict) 2-functor

$$[-] : \mathcal{M}^{\operatorname{coop}} \rightarrow \operatorname{Cat}_1$$

where $\mathcal{M}^{\operatorname{coop}}$ is the 2-category $\mathcal{M}$ with the direction of *both* 1-cells and 2-cells reversed, and $\operatorname{Cat}_1$ is the full subcategory of (large) categories with a terminal object.

This double contravariance may seem peculiar at first sight. Recall that the 2-category $\mathcal{M}$ specifies the behaviour of the modal types $\langle \mu \mid - \rangle$, which are supposed to have a right-adjoint-like behaviour, with the corresponding left-adjoint-like operators being the lock functors $-\widehat{\bullet}_{\mu}$. Being left-adjoint-like, the interpretation $[\widehat{\bullet}_{-}]$ of each lock will behave with

$^{3}$The conference version of this paper used such a presentation in the interest of brevity.