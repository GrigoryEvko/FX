# Under Lock and Key:
A Proof System for a Multimodal Logic

G. A. Kavvos Daniel Gratzer

Tuesday 8th November, 2022

1. INTRODUCTION

Many-dimensional [Gab+03], multimodal [CP08] or poly-modal [Ben10] have found a number of successful applications. To name but a few:

|  temporal logic | **F**φ, **G**φ, **X**φ | [DGL16]  |
| --- | --- | --- |
|  epistemic logic | *K*ιφ, *B*ιφ, *C*Γφ | [Fag+95]  |
|  dynamic logic | [a]φ, ⟨a⟩φ | [HKT00]  |
|  dynamic epistemic logic | *K*ιφ, [α]φ | [DHK08]  |
|  Hennessy-Milner logic | [α]φ, ⟨α⟩φ | [Sti01]  |

The majority of work on the aforementioned logics has a number of common features:

- **The propositional substrate is almost always classical.** While a classical approach is more than sufficient for modelling knowledge and computational systems, it precludes the making of a close connection with categorical logic, where the *internal language* of many categories is intuitionistic [Pit01].
- **The modal fragment is almost always inspired by a Kripke semantics, and lacks a proof system.** The Kripke semantics usually model some intensional aspect of interest, such as states of knowledge, the execution trace of a machine, and so on. While this is indeed more than adequate for modelling purposes, it precludes the immediate formulation of a well-behaved, computational theory for these logics under the Curry-Howard correspondence [GLT89; SU06].
- **There is no cohesive, unifying account.** While there have been a few attempts at building a framework [CP08, §8], as well as a host of results on combining simpler modal logics using *product* and *fusion* operators [Gab+03, §§3–4], we have yet to obtain a unifying account of logics with multiple interacting modalities.

In this paper we present a new modal logic. Unlike previous work, this logic fixes neither the number nor the interactions of modalities in advance. Instead, it is given

1

parametrically in a specification of the modalities and their interrelations, which is called the *mode theory*.

Moreover, this new logic is not just *multimodal*—in that it sports multiple modalities—but also *multimode*. This is a new concept in modal logic. Traditionally, a modal operator $\square$ is an operator that takes a formula $\varphi$ to a formula $\square\varphi$. Crucially, the formula $\square\varphi$ is in the same syntactic category as $\varphi$. The logic in this paper will conceive of modal operators as transporting formulas *between* multiple syntactic categories. We will call these syntactic categories *modes*, and modalities will map formulas of one mode to formulas in another. Modes can be conceived of as ‘possible universes of discourse’ in which we can make various logical statements. Modalities will then allow formulas in one mode to appear in another—not directly, but as spectres under a modality. All the modal operators in the logic will preserve conjunction. Thus, their essence is one of a *necessity* modality. Extending the present approach to possibility-like modalities is an open problem.

Instead of originating from a Kripke semantics of computational interest, our logic comes from categorical logic. In fact, it is the logical isolate of a multimodal Martin-Löf Type Theory [NPS90] called MTT [Gra+20; Gra+21]. Hence, it is presented as a proof system in the style of Gentzen’s *natural deduction* [Pra65; Pra06]. Due to a lack of a double-negation elimination rule the resultant logic is intuitionistic. The formulation of a classical version of this logic as well as an associated Kripke semantics for this remains an open problem.

## 2. MODE THEORIES

### 2.1. Modes

To begin presenting the logic we must presuppose a set $\mathcal{M}$ of *modes*, with typical members $m, n, \dots \in \mathcal{M}$. Each of these modes corresponds to a syntactic category, thus partitioning the formulas of the logic. We will write

$$\varphi \circledcirc m$$

to mean that $\varphi$ is a formula at mode $m$.

### 2.2. Modalities

Modalities are traditionally endoöperators of the logic: a modality $\square$ maps a formula $\varphi \circledcirc m$ to a formula $\square\varphi \circledcirc m$ at the same mode. Our logic breaks with tradition by featuring modalities which map formulas to different modes. Thus, a modality indexed by $\mu$ applied to a formula $\varphi \circledcirc n$ at mode $n$ may yield a formula $\square_\mu\varphi \circledcirc m$ at some other mode $m$. We will also break with tradition by writing $\langle \mu \mid \varphi \rangle$ for the application of the modality indexed by $\mu$ to $\varphi$, instead of the more common notation $\square_\mu\varphi$.

We will specify the fact that $\varphi \circledcirc n$ implies $\langle \mu \mid \varphi \rangle \circledcirc m$ by writing

$$\mu : n \rightarrow m$$

2

This notation says that $\mu$ is a *modality from mode $n$ to mode $m$*. We are likely to call $m$ and $n$ the *boundary* of the modality.$^{1}$

One may wonder how modal operators may be combined. Indeed, standard treatments of modal logic define a *modality* to be a composite of modal operators, and demonstrate various ‘reduction laws’ that simplify such composites; see e.g. Hughes and Cresswell [HC96, §3]. In our case, if we have two modalities $\nu : o \rightarrow n$ and $\mu : n \rightarrow m$, and a formula $\varphi \circledcirc o$ we see that

$$\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle \circledcirc m$$

In a more traditional system of modal logic we might have tried to prove that such a formula is equivalent to a simpler formula $\langle \xi \mid \varphi \rangle \circledcirc m$ for some modality $\xi : o \rightarrow m$. We will once more break with tradition by presuming that such a modality always exists. In other words, we will assume that for any two modalities $\nu : o \rightarrow n$ and $\mu : n \rightarrow m$ there exists a *composite modality* $\mu \circ \nu : o \rightarrow m$. The rules of our logic will eventually allow us to prove for any formula $\phi \circledcirc o$ a logical equivalence

$$\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle \leftrightarrow \langle \mu \circ \nu \mid \varphi \rangle \circledcirc m$$

In order to ensure that the composition of modalities behaves well we must assume that it is governed by some algebraic laws. In particular, we will assume that it is *associative*: for any three composable modalities $\xi : p \rightarrow o$, $\nu : o \rightarrow n$, $\mu : n \rightarrow m$ we must have

$$(\mu \circ \nu) \circ \xi = \mu \circ (\nu \circ \xi) : p \rightarrow m$$

Thus, a string of modalities will compose to a unique result. Moreover, we will assume for each mode $m \in \mathcal{M}$ an *identity modality*

$$1_m : m \rightarrow m$$

which will be an identity element for the composition operator $\circ$, so that for each $\mu : \nu \rightarrow \mu$ it is the case that $1_m \circ \mu = \mu = \mu \circ 1_n$. We will later be able to prove a logical equivalence $\langle 1_m \mid \varphi \rangle \leftrightarrow \varphi \circledcirc m$ for any $\varphi \circledcirc m$.

Readers that have encountered category theory before will immediately recognise that we have assumed that $\mathcal{M}$ is not just a set, but a category. Between any two modes $m, n \in \mathcal{M}$ (the *objects* of the category) we are given a set $\operatorname{Hom}_{\mathcal{M}}(m, n)$ of modalities from $m$ to $n$ (the *morphisms* of the category with *source* $m$ and *target* $n$). Moreover, for any three modes $m, n, o \in \mathcal{M}$ we are given an indexed binary operation

$$\circ_{m,n,o} : \operatorname{Hom}_{\mathcal{M}}(n, m) \times \operatorname{Hom}_{\mathcal{M}}(o, n) \rightarrow \operatorname{Hom}_{\mathcal{M}}(o, m)$$

which is associative and has ‘indexed’ identity elements $1_m \in \operatorname{Hom}_{\mathcal{M}}(m, m)$. Thus, modes and modalities form a category, i.e. a ‘typed’ monoid, whose elements (morphisms) have a ‘source’ and ‘target’ type, and where monoid multiplication (composition) can only happen when these types align. The structure of a category underlies a large part of

$^{1}$This term has its origins in higher category theory.

3

modern algebra and mathematics. For an introduction we refer the reader to books by Awodey [Awo10] and Mac Lane [Mac78].

It is instructive to try to encode a very simple modal syntax as a mode theory. Recall that traditional modal logics assume a single-mode syntax. Thus, we define the set $\mathcal{M}_{\mathbf{K}} = \{\bullet\}$ to consist of a unique mode $\bullet$. Next, we can generate the morphisms by stipulating that $\square : \bullet \rightarrow \bullet$ is an endomodality on that unique mode. We can then generate the *free category* based on this data. This is essentially the free monoid on a set of generating morphisms, subject to the restriction that in any string of morphisms the target of a morphism always matches the source of the next. As this happens trivially in our case (we have a unique mode), the set of morphisms is exactly the free monoid on one generator: its elements consist of the modalities $\square^n : \bullet \rightarrow \bullet$ for each $n \in \mathbb{N}$. The composite of two morphisms is

$$\square^a \circ \square^b = \square^{a+b}$$

Finally, the identity morphism for this operation is $\square^0$.

This generates a syntax with an infinite set of modalities: if $\varphi \circledast \bullet$ then

$$\langle \square^0 \mid \varphi \rangle, \langle \square \mid \varphi \rangle, \langle \square^2 \mid \varphi \rangle, \dots \circledast \bullet$$

are all well-formed formulas at mode $\bullet$. We will see later that the logic generated here is essentially (an intuitionistic variant of) the smallest normal modal logic $\mathbf{K}$ [BRV01, §1.6].

### 2.3. Transformations between modalities

This technology does not suffice to encode richer settings. For example, the 4 axiom

$$\square \phi \rightarrow \square \square \phi$$

is one of the two a characteristic axioms of the modal logic $\mathbf{S4}$ [HC96, §3]. We would ideally like to be able to encode this as part of the structure of the mode theory $\mathcal{M}$. However, none of the 'moving parts' of $\mathcal{M}$ allows the representation of such information.

Consequently, to encode implications such as the above we will need to add another layer to the mode theory $\mathcal{M}$. We will postulate that between any two 'parallel' modalities $\mu, \nu : n \rightarrow m$ with the same source and target mode there exists a set of *transformations*

$$\alpha : \mu \Rightarrow \nu$$

These transformations—typically denoted by letters $\alpha, \beta, \dots$—encode implications between modalities. We are likely to collectively call the modes $m, n$ and the modalities $\mu$ and $\nu$ the *boundary* of $\alpha$.

The presence of such a transformation in $\mathcal{M}$ will allow us to prove the formula

$$\langle \mu \mid \varphi \rangle \rightarrow \langle \nu \mid \varphi \rangle \circledast m$$

in the logic, for any formula $\varphi \circledast n$. For example, if in $\mathcal{M}_{\mathbf{K}}$ we postulate a transformation

$$4 : \square \Rightarrow \square^2$$

4

which corresponds to the 4 axiom, then in the logic we will be able to prove the implication

$$\langle \Box \mid \varphi \rangle \rightarrow \langle \Box^2 \mid \varphi \rangle \circledast$$

Combined with the equivalence $\langle \Box^2 \mid \varphi \rangle \leftrightarrow \langle \Box \mid \langle \Box \mid \varphi \rangle \rangle \circledast$ this implication enables a proof of a formula that looks like axiom 4 within the logic.

The addition of 4 to a modal logic may have far-reaching implications. For example, when combined with the $K$ axiom it allows us to prove the implication $\Box\Box A \rightarrow \Box\Box\Box A$. Thus, there should be a minimum amount of algebra on transformations that generates these consequences. To start, given three parallel modalities $\mu, \nu, \xi : n \rightarrow m$ and a formula $\varphi \circledast n$, the desired *hypothetical syllogism*

$$\frac{\langle \mu \mid \varphi \rangle \rightarrow \langle \nu \mid \varphi \rangle \circledast m \quad \langle \nu \mid \varphi \rangle \rightarrow \langle \xi \mid \varphi \rangle \circledast m}{\langle \mu \mid \varphi \rangle \rightarrow \langle \xi \mid \varphi \rangle \circledast m}$$

can be indirectly encoded by the existence of a composition operation on transformations: if $\alpha : \mu \Rightarrow \nu$ and $\beta : \nu \Rightarrow \xi$ then there should exist a composite transformation

$$\beta \circ \alpha : \mu \Rightarrow \xi$$

subject to associativity. There should also be an identity transformation $1_\mu : \mu \Rightarrow \mu$ for every modality $\mu : n \rightarrow m$. Note that we abuse the notations for composition and identities, using them for both modalities and their transformations.

This *vertical composition* of transformations is not sufficient to construct $\Box\Box\varphi \rightarrow \Box\Box\Box\varphi$ from the 4 axiom $\Box\varphi \rightarrow \Box\Box\varphi$. What is needed instead is a form of *horizontal composition*. Suppose that we have four modalities $\mu, \nu : n \rightarrow m$ and $\theta, \xi : o \rightarrow n$, and transformations $\beta : \theta \Rightarrow \xi$ and $\alpha : \mu \Rightarrow \nu$. This can be illustrated pictorially as

$$\underbrace{\begin{array}{c} \theta \\ o \quad \beta \Downarrow \\ \xi \end{array}}_{\xi} n \underbrace{\begin{array}{c} \mu \\ \alpha \Downarrow \\ \nu \end{array}}_{\nu} m$$

The *horizontal composition* of the transformations $\alpha$ and $\beta$ is a transformation

$$\alpha * \beta : \mu \circ \theta \Rightarrow \nu \circ \xi$$

which transforms the composite modality $\mu \circ \theta$ to the composite modality $\nu \circ \xi$.

If one of the two transformations is the identity then the horizontal composites are

$$1_\mu * \beta : \mu \circ \theta \Rightarrow \mu \circ \xi \qquad \alpha * 1_\theta : \mu \circ \theta \Rightarrow \nu \circ \theta$$

This special case is sometimes called *whiskering*, because its pictorial representation resembles adding a cat's whisker to a transformation:

$$\underbrace{\begin{array}{c} \theta \\ o \quad \beta \Downarrow \\ \xi \end{array}}_{\xi} n \xrightarrow{\mu} m \qquad \qquad o \xrightarrow{\theta} n \underbrace{\begin{array}{c} \mu \\ \alpha \Downarrow \\ \nu \end{array}}_{\nu} m$$

5

Picking $\alpha \stackrel{\mathrm{def}}{=} 4 : \square \Rightarrow \square^2$ and $\theta \stackrel{\mathrm{def}}{=} \square$ we obtain a transformation

$$4 * \square : \square^2 \Rightarrow \square^3$$

which, modulo isomorphisms, is the desired conclusion $\square\square\varphi \to \square\square\square\varphi$. Thus, transformations of modalities along with their vertical and horizontal compositions can be used to systematically encode various interaction laws between modalities.

It may not come as a surprise that this type of structure is already well-known: the ingredients used above are precisely the components of a (strict) 2-category, i.e. a category which is also equipped with morphisms between morphisms, which can be composed vertically (i.e. in the same hom-set) as well as horizontally (between hom-sets whose source and targets match). To have the structure of a 2-category these two compositions need to be compatible, i.e. to obey the interchange law: for any modalities and transformations fitting into the diagram

![img-0.jpeg](img-0.jpeg)

we must have that no matter which direction we compose in first, the result should be the same:

$$(\delta \circ \alpha) * (\gamma \circ \beta) = (\alpha * \beta) \circ (\delta * \alpha)$$

The structure of 2-categories is rich, and of foundational interest to category theory. Of course, the terminology is different: highers category theorists do not speak of modes, modalities, and transformations, but of morphisms and n-cells. The correspondence of terms between 2-categories and our multimodal logic can be summarised as follows:

$$\begin{array}{l} \text{object} \sim \text{mode} \\ \text{morphism (1-cell)} \sim \text{modality} \\ \text{2-cell} \sim \text{transformation (natural map between modalities)} \end{array}$$

In this manner we are able to give a very precise definition of a mode theory:

**Definition 2.1.** A mode theory is a (strict) 2-category.

Unfortunately, we cannot expand on the subject any further in this paper. For introductory treatments of 2-categories we refer the reader to books by Mac Lane [Mac78, §XII.3] and Borceux [Bor94, §7].

### 3. FORMULAS AND JUDGEMENTS

Having sketched how mode theories can be used to encode the modal structure of a modal logic, we now turn to defining the formulas of our logic as well as its proof system.

6

Owing to the roots of our work in Martin-Löf type theory, almost all our definitions will be given using Martin-Löf's methodology of *judgements* [Mar96]. This amounts to a universal use of positive statements which are inductively justified by evidence. The canonical examples of this methodology are the proof systems of natural deduction and sequent calculus: each sequent is a judgement, and the evidence that a judgement holds is a proof tree with that conclusion. This methodology is very common in the parts of Computer Science that are influenced by type theory; see e.g. Harper [Har16]. It has also been particularly influential in treatments of the Curry-Howard correspondence for modal logic; see e.g. Pfenning and Davies [PD01].

### 3.1. Formulas

The majority of presentations of modal logic assumes a propositional syntax that has been augmented by a set of endomodalities—usually $\square$ and $\diamond$, or an indexed version of them in the multimodal case. We will enrich this by including a modal operator $\langle \mu \mid - \rangle$ for every modality $\mu : n \rightarrow m$ in the mode theory $\mathcal{M}$. However, modalities transport formulas between modes, so we have to ensure that every formula is *well-formed*. We first define a grammar of *pre-formulas*. Then, we introduce a judgement

$$\varphi \text{ wff } @ m$$

which states that the pre-formula $\varphi$ is well-formed with respect to the mode theory $\mathcal{M}$. Thus, the well-formed formulas of the logic are a subset of the pre-formulas.

The *pre-formulas* of are generated by the BNF

$$\varphi, \psi ::= p_i \mid \perp \mid \top \mid \varphi \vee \psi \mid \varphi \wedge \psi \mid (\mu \mid \varphi) \rightarrow \psi \mid \langle \mu \mid \varphi \rangle$$

where $\mu$ is a modality in $\mathcal{M}$. These are mostly standard. Each $p_i$ is a propositional variable, and we have the usual propositional connectives. As is usual in intuitionistic logic, we define $\neg \varphi \stackrel{\text{def}}{=} \varphi \rightarrow \perp$. The only deviant is the implication $(\mu \mid \varphi) \rightarrow \psi$, whose antecedent carries a modality $\mu$. Written in terms of the modal operator and the traditional connective of implication, this is essentially $\langle \mu \mid \phi \rangle \rightarrow \psi$. However, there are technical advantages in having this compound version of implication in the logic: many proofs become significantly shorter, and the relevant 'modal modus ponens' rule is interesting from a modal perspective. We write the usual implication $\varphi \rightarrow \psi$ as shorthand for $(1 \mid \varphi) \rightarrow \psi$.

The *well-formed formulas* (wffs) are generated by the following inductive definition:

$$\begin{array}{ccc} \frac{\overline{p_i \text{ wff } @ m} \quad \overline{\top \text{ wff } @ m}}{\varphi \text{ wff } @ m} & \frac{\overline{\perp \text{ wff } @ m} \quad \frac{\varphi \text{ wff } @ m \quad \psi \text{ wff } @ m}{\varphi \wedge \psi \text{ wff } @ m}}{\varphi \vee \psi \text{ wff } @ m} & \frac{\mu : n \rightarrow m \quad \varphi \text{ wff } @ n \quad \psi \text{ wff } @ m}{(\mu \mid \varphi) \rightarrow \psi \text{ wff } @ m} \\ \frac{\varphi \text{ wff } @ n \quad \mu : n \rightarrow m}{\langle \mu \mid \varphi \rangle \text{ wff } @ m} & \end{array}$$

7

With the exception of the implication and the modal operator, the rest of the rules all refer to a single mode $m$, in which they are parametric. Thus, most of the connectives are *mode-local*: they construct propositions that pertain to a single mode. In contrast, both the rules for the modal operator and the implication rules reach across modes. In the first case, a formula that is well-formed at $n$ may appear in mode $m$, but only under a modality $\mu : n \rightarrow m$. In the second case, the antecedent of an implication should be well-formed under the appropriate modality, in a similar manner.

### 3.2. Judgements

A *judgement* of the multimodal logic has the form

$$\Gamma \vdash \varphi \circledast m$$

where $\Gamma$ is a context (at mode $\mu$), and $\varphi$ is a well-formed formula (at mode $m$).

### 3.3. Contexts

Contexts in natural deduction traditionally consist of a list of assumptions $\phi_1, \dots, \phi_n$. However, in order to accommodate modal reasoning, ours will feature two additional gadgets: *tags* and *locks*. Each of these gadgets complements the other.

Each assumption in the context will be *tagged* with a modality. Hence, the assumption

$$(\mu \mid \varphi)$$

is meant to be read as 'the formula $\varphi$ under modality $\mu$.' In broad strokes this is logically equivalent to the assumption $\langle \mu \mid \varphi \rangle$. When we come to define contexts we must remember to ensure that $\varphi$ be well-formed under $\mu$.

The other side of the coin is the appearance of *locks* in contexts. Unlike tags, locks are operators that act on entire contexts, and are annotated by a modality. If $\mu : n \rightarrow m$ is a modality and $\Gamma$ is a context at the appropriate mode, then

$$\Gamma, \widehat{\bullet}_\mu$$

will also be a context, also at an appropriate mode. We use postfix notation for reasons that will be revealed shortly. Finally, it should be stressed that locks are formal operations that act on the entire context; it might be perhaps more apt to think of $\Gamma, \widehat{\bullet}_\mu$ as $\widehat{\bullet}_\mu(\Gamma)$.

As is suggested by the notation, locks restrict access to the assumptions they enclose: whether an assumption $(\nu \mid \varphi)$ found in $\Gamma, \widehat{\bullet}_\mu$ shall be accessible will depend on the transformations between modalities $\mu$ and $\nu$. For this reason, it is important that contexts are understood as structures generated by the grammar above, and not as multisets of assumptions as is sometimes assumed.

In summary, the *pre-contexts* are generated by the grammar

$$\Gamma ::= \cdot \mid \Gamma, (\mu \mid \varphi) \mid \Gamma, \widehat{\bullet}_\mu$$

where $\cdot$ is the empty context, $\varphi$ is a pre-formula, and $\mu$ is modality in $\mathcal{M}$.

8

The (well-formed) *contexts* are isolated by a judgement

$$\Gamma \operatorname{ctx} @ m$$

which is generated by the following rules.

$$\frac{\Gamma \operatorname{ctx} @ m \quad \mu : n \to m \quad \varphi \operatorname{wff} @ n}{\Gamma, (\mu \mid \varphi) \operatorname{ctx} @ m} \quad \frac{\Gamma \operatorname{ctx} @ m \quad \mu : n \to m}{\Gamma, \widehat{\mathbf{\Omega}}_\mu \operatorname{ctx} @ n}$$

Perhaps the only unexpected detail here is that locks transport contexts backwards along modalities: if $\Gamma \operatorname{ctx} @ m$ and $\mu : n \to m$, then $\Gamma, \widehat{\mathbf{\Omega}}_\mu \operatorname{ctx} @ n$. In categorical language we would say that the lock operation $-, \widehat{\mathbf{\Omega}}_\mu$ is *contravariant* in the modality $\mu$. The reason for this will become clear when we introduce the modal rules. The categorical essence of it is that $-, \widehat{\mathbf{\Omega}}_\mu$ is in some sense a *left adjoint* to the modal operator $\langle \mu \mid - \rangle$, and thus must have the opposite variance.

Finally, it is important to determine how the lock operators should interact with the composition of modalities. Suppose that we have

$$\Gamma \operatorname{ctx} @ m \qquad \nu : o \to n \qquad \mu : n \to m$$

The rules then allow us to construct the following context:

$$\frac{\frac{\vdots}{\Gamma \operatorname{ctx} @ m} \quad \mu : n \to m}{\Gamma, \widehat{\mathbf{\Omega}}_\mu \operatorname{ctx} @ n} \qquad \nu : o \to n}{\Gamma, \widehat{\mathbf{\Omega}}_{\mu \circ \nu} \operatorname{ctx} @ o}$$

However, the mode theory also provides a composite modality $\mu \circ \nu : o \to m$. With respect to that modality the rules then allow us to construct the following context:

$$\frac{\frac{\vdots}{\Gamma \operatorname{ctx} @ m} \quad \mu \circ \nu : o \to m}{\Gamma, \widehat{\mathbf{\Omega}}_\mu, \widehat{\mathbf{\Omega}}_\nu \operatorname{ctx} @ o}$$

We will quotient the set of contexts, so that these two contexts will be understood to be identical. The rationale for this choice has to do with our earlier discussion about the equivalence between the formulas

$$\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle \leftrightarrow \langle \mu \circ \nu \mid \varphi \rangle @ m$$

for any $\varphi @ o$. The proof of this equivalence will be enabled by the fact these two contexts are syntactically interchangeable.

Hence, for any $\Gamma \operatorname{ctx} @ m$, $\nu : o \to n$, $\mu : n \to m$, and $\phi @ o$, we stipulate that

$$\Gamma, \widehat{\mathbf{\Omega}}_{1_m} = \Gamma \operatorname{ctx} @ m \tag{1}$$

9

![img-1.jpeg](img-1.jpeg)

Figure 1: Rules of Multimodal Logic

\[
\Gamma , \widehat {\mathbf {m}} _ {\mu}, \widehat {\mathbf {m}} _ {\nu} = \Gamma , \widehat {\mathbf {m}} _ {\mu \circ \nu} \operatorname{ctx} @ o \tag {2}
\]

This last equation also reveals the reason that \(-, \widehat{\mathbf{m}}_{\mu}\) is best written as a postfix operator: as it is contravariant, writing it at the end preserves the order of symbols when composing modalities.

### 3.4. Rules

We are now able to introduce the logical rules of the system. The complete list is given in Fig. 1.

Propositional connectives The rules for the propositional constants and connectives \(\top\), \(\bot\), \(\wedge\), and \(\vee\) are the standard rules of natural deduction. The only difference is that they have become parametric in the mode \(@m\), which they carry from premise to conclusion. In the case of \(\vee\), the elimination rule creates 'local assumptions' as usual; but because of the structure of contexts these need to be tagged with a modality. We pick the identity modality 1, so that the rule remains completely mode-local. Therefore, the rules for all but one of the usual propositional connectives apply in an unchanged form within a single mode. The only exception is the compound modal implication.

Using assumptions The usual variable rule of natural deduction

\[
\overline {{\Gamma , \varphi , \Delta \vdash \varphi}}
\]

10

allows us to prove a conclusion if we have already assumed it in the context.

This rule does not immediately adapt to our multimodal system. There is a sense in which modal reasoning is largely about the *control of assumptions*. The rôle of modalities very often seems to amount to a specification of who or which state of the world ‘owns’ an assumption, and when we should be able to use it. In this particular setting, the logical power of an assumption is attenuated by the presence of a lock operator $-,\widehat{\mathbf{\Omega}}_{\mu}$. The lock stops us from using the assumptions that it guards—unless there is a transformation that explicitly allows it.

There are three principles that determine the behaviour of locks.

**Principle 1.** A $\mu$-variable can escape the hold of a $\mu$-lock.

In symbols, this implies that the variable rule at the very least admits the inference

$$\overline{\Gamma, (\mu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu} \vdash \varphi @ n}$$

where for $\mu : n \rightarrow m$ the formation of the context presupposes that

$$\Gamma \text{ ctx } @ m \quad \varphi \text{ wff } @ n$$

If we view a lock $\widehat{\mathbf{\Omega}}_{\mu}$ as a protector of variables, we see that it acts as a $\mu$-firewall that only authorises $\mu$-assumptions to escape its hold. In another interpretation, the appearance of a lock at the end of a context signifies that we are currently reasoning in a $\mu$-protected environment, so we are entitled to access $\mu$-classified information.

As we have quotiented our contexts up to Eqs. (1) and (2), this ability of a $\mu$-assumption to escape a $\mu$-lock should be retained even when the locks match only up to composition. For example, given $\nu : o \rightarrow n$ and $\varphi \text{ wff } @ o$ we should also be able to use the variable rule to infer

$$\overline{\Gamma, (\mu \circ \nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu}, \widehat{\mathbf{\Omega}}_{\nu} \vdash \varphi @ o}$$

precisely because $\Gamma, (\mu \circ \nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu}, \widehat{\mathbf{\Omega}}_{\nu} = \Gamma, (\mu \circ \nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu \circ \nu} @ o$.

The second principle allows us to weaken the requirement for an exact match between the modality and the lock:

**Principle 2.** The transformations of $\mathcal{M}$ are ‘keys’ for the lock.

In other words, suppose that for modalities $\mu, \nu : n \rightarrow m$ we have a transformation

$$\alpha : \nu \Rightarrow \mu$$

in $\mathcal{M}$. If we interpret this to mean that the modality $\nu$ implies (or is stronger than) the modality $\mu$, then intuition has it that $\nu$-modal assumptions should be able to ‘unlock’ a $\mu$-lock. In symbols:

$$\frac{\alpha : \nu \Rightarrow \mu}{\Gamma, (\nu \mid \varphi), \widehat{\mathbf{\Omega}}_{\mu} \vdash \varphi @ n}$$

The final principle is already well-known:

11

# **Principle 3.** The variable rule should be stable under weakening.

The idea here is that weakening should be admissible independently of the position of locks: if we have an inference in context $\Gamma, \widehat{\bullet}_\mu$ we should also be to admit it in either $\Gamma, (\nu \mid \varphi), \widehat{\bullet}_\mu$ or $\Gamma, \widehat{\bullet}_\mu, (\nu' \mid \varphi)$ for appropriately-typed modalities $\nu$ and $\nu'$. Moreover, this should only apply to tagged assumptions: introducing a new lock should by no means be admissible! That is, if we have an inference in context $\Gamma$, it should not in general be possible to also have it in $\Gamma, \widehat{\bullet}_\mu$, as $\widehat{\bullet}_\mu$ might protect some of the assumptions in $\Gamma$ by prohibiting their use.

Combining those three principles we see that the assumption rule should more or less function in the following manner:

1. It should gather all the locks to the right of the relevant assumption.
2. It should compose the modalities associated with each one of these locks.
3. It should allow the use of an assumption whenever its tag is stronger than the locks that protect it, i.e. the locks to its right.

In symbols we write

$$\frac{\mu : n \rightarrow m \quad \alpha : \mu \Rightarrow \text{locks}(\Delta)}{\Gamma, (\mu \mid A), \Delta \vdash A @ m}$$

where the function $\text{locks}(-)$ is defined by the following inductive clauses:

$$\begin{aligned} \text{locks}(\cdot) &\stackrel{\text{def}}{=} 1 \\ \text{locks}(\Gamma, (\mu \mid A)) &\stackrel{\text{def}}{=} \text{locks}(\Gamma) \\ \text{locks}(\Gamma, \widehat{\bullet}_\mu) &\stackrel{\text{def}}{=} \text{locks}(\Gamma) \circ \mu \end{aligned}$$

It is evident that this function is well-defined on contexts, for it respects Eqs. (1) and (2).

**Locks vs. modalities** The modal rules of the system reveal the close interaction between locks and modal operators.

Broadly speaking, the lock operators $-, \widehat{\bullet}_\mu$ are used to 'filter' the assumptions in the context, keeping only those that are allowed in a proof of a formula under the modality $\langle \mu \mid - \rangle$. This is encoded in the introduction rule, viz.

$$\frac{\mu : n \rightarrow m \quad \Gamma, \widehat{\bullet}_\mu \vdash \varphi @ n}{\Gamma \vdash \langle \mu \mid \varphi \rangle @ m}$$

which allows us to prove the modal formula $\langle \mu \mid \varphi \rangle$ from the context $\Gamma$ exactly whenever we can prove $\varphi$ from a $\mu$-locked $\Gamma$. Thus, when trying to prove $\langle \mu \mid \varphi \rangle$ it suffices to prove $\varphi$, but with restrictions on the proof. More precisely, we are able to use only those assumptions whose modal tag is at least as strong as $\mu$.

12

The modal elimination rule

$$\frac{\nu : o \rightarrow n \quad \mu : n \rightarrow m \quad \Gamma, \widehat{\bullet}_\mu \vdash \langle \nu \mid \varphi \rangle @ n \quad \Gamma, (\mu \circ \nu \mid \varphi) \vdash \psi @ m}{\Gamma \vdash \psi @ m}$$

is the most complicated rule of the system. Its *major premise* (i.e. the premise whose connective is being eliminated) is $\Gamma, \widehat{\bullet}_\mu \vdash \langle \nu \mid \varphi \rangle @ n$. Notice that this judgement could be turned into $\Gamma \vdash \langle \mu \mid \langle \nu \mid \varphi \rangle \rangle @ m$ by applying the introduction rule. Putting the transformed major premise and the minor premise side-by-side

$$\Gamma \vdash \langle \mu \mid \langle \nu \mid \varphi \rangle \rangle @ m \quad \Gamma, (\mu \circ \nu \mid \varphi) \vdash \psi @ m$$

we see that this elimination rule is almost a cut rule! This is particularly evident if we recall that $\langle \mu \mid \langle \nu \mid \varphi \rangle \rangle$ is supposed to be logically equivalent to $\langle \mu \circ \nu \mid \varphi \rangle$, which is also supposed to be equivalent to the tagged assumption $(\mu \circ \nu \mid \varphi)$.

Despite appearances, this elimination rule is subtle: it allows the prover to ‘split’ a composite modality $\mu \circ \nu$ into its constituent parts, keeping the second half $\mu$ as a lock in the context of the major premise, and eliminating only the first half $\nu$. In fact, we will see in §4 that the modal elimination rule is the central device that allows highly non-trivial interactions between modalities to appear as reasoning principles in the logic.

**Implication** As is usual in natural deduction, the implication introduction rule

$$\frac{\Gamma, (\mu \mid \varphi) \vdash \psi @ m}{\Gamma \vdash (\mu \mid \varphi) \rightarrow \psi @ m}$$

internalises the usual deduction theorem as a rule of the proof system, by allowing the prover to discharge an assumption. This is exactly why the compound implication $(\mu \mid \varphi) \rightarrow \psi$ is a natural connective in this logic: its antecedent mirrors the structure of assumptions in the proof system.

The elimination rule is a form of *modal modus ponens*:

$$\frac{\mu : n \rightarrow m \quad \Gamma \vdash (\mu \mid \varphi) \rightarrow \psi @ m \quad \Gamma, \widehat{\bullet}_\mu \vdash \varphi @ n}{\Gamma \vdash \psi @ m}$$

If we can prove the implication $(\mu \mid \varphi) \rightarrow \psi$ then proving $\varphi$ in a $\mu$-locked context suffices to obtain $\psi$. Notice once more that the minor premise can be transformed into $\Gamma \vdash \langle \mu \mid \varphi \rangle @ m$ by one application of the modal introduction rule. Thus, if we consider the assumption $(\mu \mid \varphi)$ and the formula $\langle \mu \mid \varphi \rangle$ to be equivalent, this rule is simply modus ponens, but a little bit more accommodating towards the structure of locks.

### 3.5. Metatheory

The system satisfies a number of the usual metatheorems. First, one is able to show the admissibility of the usual structural rules of weakening and exchange. Some additional care is needed in the case of weakening to ensure that the weakened context is well-formed.

13

**Theorem 3.1** (Structural rules). *The following rules are admissible.*

$$\frac{\Gamma, (\mu \mid \varphi), \Delta \text{ ctx } @p \quad \Gamma, \Delta \vdash C @p}{\Gamma, (\mu \mid \varphi), \Delta \vdash C @p} \quad \frac{\Gamma, (\mu \mid \varphi), (\nu \mid \psi), \Delta \vdash C @p}{\Gamma, (\nu \mid \psi), (\mu \mid \varphi), \Delta \vdash C @p}$$

We cannot in general weaken a context by adding a lock. In fact, locks transport contexts between modes, so adding arbitrary locks to a context may well map a well-formed context $\Gamma \text{ ctx } @m$ to one that is not well-formed. However, we can 'weaken a $\mu$-lock' by replacing it with one corresponding to a $\nu$-lock for a 'weaker' $\nu$, i.e. a modality with the same boundary (source and target modes) for which there exists some $\alpha : \mu \Rightarrow \nu$.

**Theorem 3.2** (Lock Weakening). *The following rule is admissible.*

$$\frac{\Gamma, \text{🖼}_\mu, \Delta \vdash \varphi @p \quad \alpha : \mu \Rightarrow \nu}{\Gamma, \text{🖼}_\nu, \Delta \vdash \varphi @p}$$

Finally, we can prove that a modal version of the cut rule is admissible.

**Theorem 3.3** (Cut). *The following rule is admissible:*

$$\frac{\Gamma, \text{🖼}_\mu \vdash \varphi @n \quad \Gamma, (\mu \mid \varphi), \Delta \vdash \psi @b}{\Gamma, \Delta \vdash \psi @b}$$

These metatheorems will be shown as corollaries of theorems in §5.

#### 4. EXAMPLES

In this section we demonstrate modal reasoning using our proof system.

Recall that $\varphi \rightarrow \psi \stackrel{\text{def}}{=} (1 \mid \varphi) \rightarrow \psi$. The usual modus ponens is then a *derived* rule:

$$\frac{\Gamma \vdash \varphi \rightarrow \psi @m \quad \Gamma \vdash \varphi @m}{\Gamma \vdash \psi @m}$$

This follows from the elimination rule because by Eq. (1) we have $\Gamma, \text{🖼}_1 = \Gamma$.

**Some general theorems about modal formulas** We begin by showing some theorems that hold irrespective of the choice of mode theory. This determines the nature of our modalities—which are shown to automatically preserve conjunctions—and showcases the various rules in action.

First, we can show that a modal antecedent $(\mu \mid \varphi)$ implies its corresponding modal formula. For any $\mu : n \rightarrow m$ and $\varphi \text{ wff } @n$ we have

$$\frac{1_\mu : \mu \Rightarrow \mu}{\frac{(\mu \mid \varphi), \text{🖼}_\mu \vdash \varphi @n}{(\mu \mid \varphi) \vdash \langle \mu \mid \varphi \rangle @m}} \\ \hline \vdash (\mu \mid \varphi) \rightarrow \langle \mu \mid \varphi \rangle @m$$

14

This proves one half of the claim that $(\mu \mid \varphi)$ and $\langle \mu \mid \varphi \rangle$ are equivalent. The other half cannot be shown as a theorem, as an implication cannot have $(\mu \mid \varphi)$ as a conclusion. However, the special case of the modal elimination rule for $\nu \stackrel{\text{def}}{=} 1$

$$\frac{\mu : n \rightarrow m \quad \Gamma \vdash \langle \mu \mid \varphi \rangle \circledcirc m \quad \Gamma, (\mu \mid \varphi) \vdash \psi \circledcirc m}{\Gamma \vdash \psi \circledcirc m}$$

(which follows because $\Gamma, \widehat{\bullet}_1 = \Gamma$ by Eq. (1)) shows how we can 'promote' a modal formula $\langle \mu \mid \varphi \rangle$ and use it as an assumption $(\mu \mid \varphi)$ in the context of another proof. This can be thought as a converse to above proof.

One can also show a version of the $\mathbf{K}$ axiom $\Box(\varphi \rightarrow \psi) \rightarrow \Box\varphi \rightarrow \Box\psi$, where the $\Box$ in the conclusion is replaced by a $\langle \mu \mid -\rangle$, and the two antecedents are tagged:

$$\frac{\frac{1_\mu : \mu \Rightarrow \mu}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi), \widehat{\bullet}_\mu \vdash \varphi \rightarrow \psi \circledcirc m} \quad \frac{1_\mu : \mu \Rightarrow \mu}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi), \widehat{\bullet}_\mu \vdash \psi \circledcirc m}}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi), \widehat{\bullet}_\mu \vdash \psi \circledcirc m} \\ \frac{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi) \vdash \langle \mu \mid \psi \rangle \circledcirc m}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi) \vdash \langle \mu \mid \psi \rangle \circledcirc m}$$

Consequently all the modalities in our system are necessity-type modalities.

It is interesting to ask how one can handle this type of reasoning *without* using modal antecedents in implications, i.e. replacing antecedents $(\mu \mid \varphi)$ with antecedents $(1 \mid \langle \mu \mid \varphi \rangle)$ with a trivial modal tag and a modal formula. Navigating the difference between $(\mu \mid \varphi)$ and $\langle \mu \mid \varphi \rangle$ is the domain of the modal elimination rule. For example, we can prove that we can eliminate conjunctions under modalities. Given $\varphi, \psi$ wff $\circledcirc n$ and writing $\Gamma \stackrel{\text{def}}{=} (1 \mid \langle \mu \mid \varphi \wedge \psi \rangle), (\mu \mid \varphi \wedge \psi)$ we have

$$\frac{\frac{1_{1_m} : 1_m \Rightarrow 1_m}{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle) \vdash \langle \mu \mid \varphi \wedge \psi \rangle \circledcirc m} \quad \frac{\frac{1_\mu : \mu \Rightarrow \mu}{\Gamma, \widehat{\bullet}_\mu \vdash \varphi \wedge \psi \circledcirc n}}{\Gamma, \widehat{\bullet}_\mu \vdash \varphi \circledcirc n}}{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle), (\mu \mid \varphi \wedge \psi) \vdash \langle \mu \mid \varphi \rangle \circledcirc m}}{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle) \vdash \langle \mu \mid \varphi \rangle \circledcirc m} \\ \frac{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle) \vdash \langle \mu \mid \varphi \rangle \circledcirc m}{\vdash \langle \mu \mid \varphi \wedge \psi \rangle \rightarrow \langle \mu \mid \varphi \rangle \circledcirc m}$$

Notice that the modal elimination rule is used to turn the modal formula $\langle \mu \mid \varphi \wedge \psi \rangle$ into an assumption $(\mu \mid \varphi \wedge \psi)$ which overpowers the $\mu$-lock. One can also prove the following theorems in a similar manner:

$$\begin{aligned} &\vdash \langle \mu \mid \varphi \rightarrow \psi \rangle \rightarrow \langle \mu \mid \varphi \rangle \rightarrow \langle \mu \mid \psi \rangle \circledcirc m \\ &\vdash \langle \mu \mid \varphi \wedge \psi \rangle \leftrightarrow \langle \mu \mid \varphi \rangle \wedge \langle \mu \mid \psi \rangle \circledcirc m \end{aligned} \tag{3}$$

Both of these are versions of the $\mathbf{K}$ axiom.

15

**Normality** Most modal logics are single-mode, single-modal-operator logics. Following our approach in §2 we want construct a mode theory consisting of a single object $\bullet$. The axioms of 2-categories then dictate that we define a category $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ of modalities and their transformations. The *objects* of this category are the modalities, and the *morphisms* are the transformations between them. There also needs to be a composition functor

$$\circ : \mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet) \times \mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet) \rightarrow \mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$$

On objects this functor maps any two modalities to their composite; on morphisms it maps two transformations of modalities to their *horizontal composite*.

Suppose that, as in §2, we define $\mathcal{M}_{\mathbf{K}}$ to be the free category on one generator, so that $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ is the *set* consisting of the modalities $\square^n : \bullet \rightarrow \bullet$ for each $n \in \mathbb{N}$. Defining $\square \varphi \stackrel{\mathrm{def}}{=} \langle \square \mid \varphi \rangle$ the proofs of Eq. (3) read

$$\begin{aligned} &\vdash \square(\varphi \rightarrow \psi) \rightarrow \square \varphi \rightarrow \square \psi \circledast m \\ &\vdash \square(\varphi \wedge \psi) \leftrightarrow \square \varphi \wedge \square \psi \circledast m \end{aligned}$$

Thus the 'simplest' mode theory $\mathcal{M}_{\mathbf{K}}$ generates a logic that is a lot like $\mathbf{K}$.

**Axioms as transformations** We will now demonstrate how the transformations of the mode theory gives rise to theorems that are usually axioms of normal modal logics.

To add axioms to the logic we can then promote the set $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ itself to be the free category on additional transformations. If we also freely add horizontal composites we get a *free 2-category*. For example, if as in §2 we generate the free 2-category on

$$4 : \square \Rightarrow \square^2$$

then we get a category with an infinite number of transformations, e.g.

$$\begin{array}{rcl} 4 & : & \square \Rightarrow \square^2 \\ 1_{\square} * 4 & : & \square^2 \Rightarrow \square^3 \\ 1_{\square} * 1_{\square} * 4 & : & \square^4 \Rightarrow \square^5 \\ & : & \end{array}$$

Axiom 4 then appears in the logic through the following proof: for any $\varphi$ wff $\circledast$,

$$\begin{array}{r} 4 : \square \Rightarrow \square^2 \\ \hline (1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi), \widehat{\square}_{\square^2} \vdash \varphi \circledast \\ 1_1 : 1 \Rightarrow 1 \\ \hline (1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi) \vdash \langle \square^2 \mid \varphi \rangle \circledast \\ \hline (1 \mid \langle \square \mid \varphi \rangle) \vdash \langle \square \mid \varphi \rangle \circledast \\ \hline (1 \mid \langle \square \mid \varphi \rangle) \vdash \langle \square^2 \mid \varphi \rangle \circledast \\ \hline \vdash \langle \square \mid \varphi \rangle \rightarrow \langle \square^2 \mid \varphi \rangle \circledast \end{array}$$

Similarly, we could have added an axiom

$$T : \square^1 \Rightarrow \square^0$$

16

which leads to the modal logic $\mathbf{T}$.

We would expect that combining axioms 4 and $T$ generates the modal logic $\mathbf{S4}$. We can indeed generate a free category out of these two generating transformations, but there is more subtlety involved. The reason is that our mode theory reifies axioms as transformations—actual objects that can be composed in more than one way. For example, we can immediately find three transformations $\alpha : \square \Rightarrow \square$. One is simply the identity $1_{\square} : \square \Rightarrow \square$. But there are also two more, which combine the $T$ and 4 axioms:

$$(T * 1_{\square}) \circ 4 : \square \Rightarrow \square$$

$$(1_{\square} * T) \circ 4 : \square \Rightarrow \square$$

Moreover, there are two ways to construct a transformation $\square \Rightarrow \square^3$:

$$(4 * 1_{\square}) \circ 4 : \square \Rightarrow \square^3$$

$$(1_{\square} * 4) \circ 4 : \square \Rightarrow \square^3$$

It is not unreasonable to postulate that these different ways of constructing the same transformation are equal, i.e. that

$$(T * 1_{\square}) \circ 4 = 1_{\square} = (1_{\square} * T) \circ 4 \quad (4)$$

$$(4 * 1_{\square}) \circ 4 = (1_{\square} * 4) \circ 4 \quad (5)$$

In category theory such equations are called *coherence equations*: they state that multiple ways of performing a certain transformation are in fact identical in their effect (coherent). The addition of coherence equations means that a category is no longer freely generated.

A mode theory that satisfies these equations can be constructed explicitly: its modalities are of the form $\square^n$ for $n \in \mathbb{N}$; a transformation $\alpha : \square^n \Rightarrow \square^m$ is just an order preserving function $\alpha : [m] \rightarrow [n]$ where $[m] \stackrel{\text{def}}{=} \{k \in \mathbb{N} \mid k < m\}$; and composition of modalities is just their sum [SS86]. Category theorists will recognise this as the *walking comonad*, i.e. a tiny 2-category **Comnd** such that 2-functors **Comnd** $\longrightarrow$ **Cat** classify all categories equipped with a specific comonad. The fact that this kind of object occurs in category theory provides external justification for why the above list of equations is sound and complete.

Of course, this could be seen as being far more work than necessary. We could have constructed a mode theory $\mathcal{M}_{\mathbf{K4}}^{\text{idem}}$ with one mode $\bullet$, and one modality $\square : \bullet \rightarrow \bullet$ that satisfies the equation

$$\square \circ \square = \square$$

and no non-identity transformations. In this mode theory there is a unique transformation $\alpha : \square \Rightarrow \square \circ \square$: because the boundaries of this transformation are equal, it is just the identity transformation $1_{\square}$ on $\square$. With this mode theory we can prove a theorem

17

corresponding to 4:

$$\begin{array}{c} \frac{1_{\square} : \square \Rightarrow \square \circ \square}{(1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi), \square_{\square}, \square_{\square} \vdash \varphi @ \bullet} \\ \frac{1_1 : 1_{\bullet} \Rightarrow 1_{\bullet}}{(1 \mid \langle \square \mid \varphi \rangle) \vdash \langle \square \mid \varphi \rangle @ \bullet} \quad \frac{(1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi), \square_{\square} \vdash \langle \square \mid \varphi \rangle @ \bullet}{(1 \mid \langle \square \mid \varphi \rangle), (\square \mid \varphi) \vdash \langle \square \mid \langle \square \mid \varphi \rangle @ \bullet} \\ \hline (1 \mid \langle \square \mid \varphi \rangle) \vdash \langle \square \mid \langle \square \mid \varphi \rangle @ \bullet \\ \hline \vdash \langle \square \mid \varphi \rangle \rightarrow \langle \square \mid \langle \square \mid \varphi \rangle @ \bullet \end{array}$$

where the leaf on the right branch works exactly because $\square \circ \square = \square$. This mode theory generates a version of the logic **K4**, which combines the $K$ and 4 axioms. We can also scale it to **S4** by adding a transformation $\varepsilon : \square \Rightarrow 1_{\bullet}$ from the $\square$ modality to the identity modality. This leads to the mode theory $\mathcal{M}_{\mathbf{S4}}^{\mathrm{idem}}$, a more explicit description of which is the following: there is one mode $\bullet$, and the hom-category $\mathrm{Hom}_{\mathcal{M}}(\bullet, \bullet)$ consists of two objects $\square$ and $1_{\bullet}$ with a single morphism $\epsilon : \square \Rightarrow 1_{\bullet}$ between them.

At this point it still appears as if the mode theory $\mathcal{M}_{\mathbf{S4}}$ generates almost exactly the same logic as the appreciably simpler mode theory $\mathcal{M}_{\mathbf{S4}}^{\mathrm{idem}}$. Modulo syntactic differences—e.g. that $\langle \square^2 \mid \varphi \rangle$ is the same as $\langle \square \mid \varphi \rangle$—this is true up to provability of formulas: the logic generated by this mode theory is indeed equivalent to (an intuitionistic variant of) **S4** at the level of provable theorems. However, at the level of *proofs*, the logics generated by $\mathcal{M}_{\mathbf{S4}}$ and $\mathcal{M}_{\mathbf{S4}}^{\mathrm{idem}}$ are wildly different! The reasons for that are easily understood only when we use the proofs-as-programs perspective of the Curry-Howard correspondence to study the dynamic behaviour of proofs. For category theorists we will simply mention that whereas $\mathcal{M}_{\mathbf{S4}}$ generates a logic whose modality can be interpreted by any comonad with a left adjoint, the mode theory $\mathcal{M}_{\mathbf{S4}}^{\mathrm{idem}}$ additionally requires that the said comonad be *idempotent*.

**Encoding multimodal logics** The flexibility afforded by the mode theory means that we can encode multimodal logics in our system. For example, we can encode a simple *epistemic logic*: if we start with a set of agents $\mathbb{I}$, we can generate a mode theory with a single mode $\bullet$ and an epistemic modality $K_i : \bullet \rightarrow \bullet$ for each $i \in \mathbb{I}$ (read as “agent $i$ knows”) [Ben10, §12]. If we then add enough transformations—as above—we can capture two of the most popular axioms of epistemic logic:

$$\begin{array}{ll} K_i \varphi \rightarrow \varphi & \text{veridicality} \\ K_i \varphi \rightarrow K_i(K_i \varphi) & \text{positive introspection} \end{array}$$

The axiom $\neg K_i \varphi \rightarrow K_i \neg K_i \varphi$ of *negative introspection* cannot be captured as negation is not a modality in our system (it cannot be: modalities preserve conjunctions).

To capture a basic *doxastic logic* [Ben10, §13] we could also add endomodalities $B_i$ (read “agent $i$ believes”) along with a transformation

$$\text{Aristotle} : K_i \Rightarrow B_i$$

18

which states that knowledge implies belief. We could also add a *strong introspection* transformation, that states that an agent knows what they believe:

$$\text{Introspe} : B_i \Rightarrow K_i \circ B_i$$

Whether any coherence laws naturally arise in this setting is yet to be determined.

**A multimode logic** Our discussion would not be complete without including a bona fide *multimode* logic. To our knowledge no such logics have appeared before. However, in our work on multimodal Martin-Löf type theory we have found multimode settings extremely useful, especially when there are two distinct ‘universes of discourse’ that we are trying to model. The scenario usually involves a universe of discourse in which some particular principle holds (e.g. some axiom or induction principle), and another in which it does not. These are related by modalities, so that the formulas in one are available in the other under a modality, and can also be related to the formulas of another mode.

We wish illustrate that perspective in the simplest possible way. Consider the mode theory consisting of two objects, int and cl, and a single modality

$$\mathbf{P} : \text{int} \rightarrow \text{cl}$$

The idea is that the mode cl corresponds to classical logic, and the mode int corresponds to intuitionistic logic. In this setup we are able to add the excluded middle axiom to the rules of the classical mode:

$$\frac{\varphi \text{ wff @ cl}}{\Gamma \vdash \varphi \vee \neg \varphi @ \text{ cl}}$$

We do *not* include this rule in the logic of the intuitionistic mode int. If we can prove $\vdash \langle \mathbf{P} \mid \varphi \rangle @ \text{ cl}$ then we know that $\varphi$ is a theorem of intuitionistic propositional logic. Thus, only the theorems of intuitionistic logic are available under the modality $\mathbf{P}$.

Notice that this modality $\mathbf{P}$ is not really an ‘inclusion.’ For example, we are not able to prove $\langle \mathbf{P} \mid \varphi \rangle \rightarrow \varphi @ \text{ cl}$. In fact, this formula need not even be well-formed! To form $\langle \mathbf{P} \mid \varphi \rangle \text{ wff @ cl}$ we must have that $\varphi \text{ wff @ int}$, and concluding that $\varphi \text{ wff @ cl}$ from that assumption is a non-trivial metatheorem about the logic.

In the classical mode we may infer that

$$\frac{\varphi \text{ wff @ int}}{\Gamma \vdash \langle \mathbf{P} \mid \varphi \rangle \vee \neg \langle \mathbf{P} \mid \varphi \rangle @ \text{ cl}}$$

That is: in the classical mode we can infer that it is either true or false that $\varphi$ is intuitionistically provable. Thus, the classical mode of this logic can be seen as a place where one may reason about provability in intuitionistic logic!

## 5. A MULTIMODAL $\lambda$-CALCULUS

In this final section we establish a *Curry-Howard correspondence* [Gal93; GLT89; How80; SU06] for multimodal logic. This is traditionally achieved as follows. Beginning with a

19

natural deduction system, we associate *variables* with assumptions of the logic. Then, we assign a *term* to each derivation. The terms themselves are linearly-written representations of proof trees, to which they correspond bijectively. This process is sometimes called *term assignment*.

If we annotate proof trees with terms, then we can view

- terms as computer programs
- formulas as the types of programs
- proof reduction as computation

In this setting the introduction and elimination rules for implication strongly resemble functional abstraction and function application. Thus, the system of proof terms is often a $\lambda$-calculus, and proof simplification can be seen as a *dynamics* of these proofs.

First, we describe the types of our system. These are exactly the same as the formulas, but we consistently replace $\varphi, \psi, \dots$ with $A, B, \dots, \wedge$ with $\times$, and $\vee$ with $+$. The *pre-types* of are generated by

$$A, B ::= p_i \mid \perp \mid \top \mid A + B \mid A \times B \mid (\mu \mid A) \rightarrow B \mid \langle \mu \mid A \rangle$$

The *types* are generated by the following judgement.

$$\frac{\overline{p_i \text{ type } @ m} \quad \overline{\top \text{ type } @ m} \quad \perp \text{ type } @ m \quad \frac{A \text{ type } @ m \quad B \text{ type } @ m}{A \times B \text{ type } @ m}}{\frac{A \text{ type } @ m \quad B \text{ type } @ m}{A + B \text{ type } @ m}}$$

$$\frac{\mu : n \rightarrow m \quad A \text{ type } @ n \quad B \text{ type } @ m}{(\mu \mid A) \rightarrow B \text{ type } @ m}$$

$$\frac{A \text{ type } @ n \quad \mu : n \rightarrow m}{\langle \mu \mid A \rangle \text{ type } @ m}$$

Second, we need to describe the *contexts* of the type system. These are again the same as the natural deduction system, but with the addition of a unique variable for each assumption. Contexts are generated by the rules

$$\frac{\Gamma \text{ ctx } @ m \quad A \text{ type } @ n \quad \mu : n \rightarrow m}{\Gamma, x : (\mu \mid A) \text{ ctx } @ m} \quad \frac{\Gamma \text{ ctx } @ m \quad \mu : n \rightarrow m}{\Gamma, \square_\mu \text{ ctx } @ n}$$

considered as before subject to Eqs. (1) and (2). A point of order: when we add a new binding to a context, we assume that no other assumption uses the same variable. This allows us to uniquely identify which assumption is being used in a proof term without any confusion.

We extend the definition of $\text{locks}(\cdot)$ to cover variables in the obvious way:

$$\text{locks}(\cdot) \stackrel{\text{def}}{=} 1$$

20

VAR

\[
\frac {\mu : n \to m \qquad \alpha : \mu \Rightarrow \mathsf {l o c k s} (\Delta)}{\Gamma , x : (\mu \mid A) , \Delta \vdash x ^ {\alpha} : A @ n}
\]

PAIR

\[
\frac {\Gamma \vdash M : A @ m \qquad \Gamma \vdash N : B @ m}{\Gamma \vdash (M , N) : A \times B @ m}
\]

PROJ

\[
\frac {\Gamma \vdash P : A _ {1} \times A _ {2} @ m}{\Gamma \vdash \pi_ {i} (P) : A _ {i} @ m}
\]

LAM

\[
\frac {\Gamma , x : (\mu \mid A) \vdash M : B @ m}{\Gamma \vdash \lambda x : (\mu \mid A) . M : (\mu \mid A) \to B @ m}
\]

APP

\[
\frac {\mu : n \to m \qquad \Gamma \vdash M : (\mu \mid A) \to B @ m \qquad \Gamma , \widehat {\mathbf {m}} _ {\mu} \vdash N : A @ n}{\Gamma \vdash M (N) _ {\mu} : B @ m}
\]

INJ

\[
\frac {\Gamma \vdash M : A _ {i} @ m}{\Gamma \vdash \mathsf {i n} _ {i} (M) : A _ {1} + A _ {2} @ m}
\]

CASE

\[
\frac {\Gamma \vdash M : A + B @ m \qquad \Gamma , x : (1 \mid A) \vdash P : C @ m \qquad \Gamma , y : (1 \mid B) \vdash Q : C @ m}{\Gamma \vdash \mathsf {c a s e} (M ; x _ {A} . P ; y _ {B} . Q) : C @ m}
\]

MOD

\[
\frac {\mu : n \to m \qquad \Gamma , \widehat {\mathbf {m}} _ {\mu} \vdash M : A @ n}{\Gamma \vdash \operatorname{mod} _ {\mu} (M) : \langle \mu \mid A \rangle @ m}
\]

LET

\[
\frac {\nu : o \to n \qquad \mu : n \to m \qquad \Gamma , \widehat {\mathbf {m}} _ {\mu} \vdash M : \langle \nu \mid A \rangle @ n \qquad \Gamma , x : (\mu \circ \nu \mid A) \vdash N : B @ m}{\Gamma \vdash \operatorname{let} _ {\mu} \operatorname{mod} _ {\nu} (x _ {A}) \leftarrow M \text {in} N : B @ m}
\]

Figure 2: Terms of Multimodal Logic

\[
\operatorname{locks} (\Gamma , x: (\mu \mid A)) \stackrel {{\text { def }}} {{=}} \operatorname{locks} (\Gamma)
\]

\[
\operatorname{locks} (\Gamma , \widehat {\mathbf {m}} _ {\mu}) \stackrel {{\text { def }}} {{=}} \operatorname{locks} (\Gamma) \circ \mu
\]

This operation clearly preserves Eqs. (1) and (2), and is hence well-defined on contexts. One can show by induction on pre-contexts that this operation is a homomorphism with respect to concatenation, i.e. that

\[
\operatorname{locks} (\Gamma , \Delta) = \operatorname{locks} (\Gamma) \circ \operatorname{locks} (\Delta)
\]

when both sides are defined. \( ^{2} \)

The term assignment system for multimodal logic is given in Fig. 2. The basic judgement is of the form \(\Gamma \vdash M: A @ m\), which means that \(M\) is a term of type \(A\) under

\( ^{2} \) Recall that concatenation is in general not an admissible rule of the judgment  \( \Gamma \)  ctx @ m, as locks may interfere with the mode  \( m \in M \) .

21

the context $\Gamma$, in mode $m$.

The typing rules closely correspond to the rules of the logic in Fig. 1. For example, we have replaced conjunction $\wedge$ by the Cartesian product $\times$. We may construct a proof $(M, N)$ of $A \times B$ by pairing together a proof $M$ of $A$ and $N$ of $B$. Hence, the Curry-Howard correspondence is readily apparent.

One subtle point is that the terms for the introduction of an implication, the elimination of a disjunction, and the elimination of modal term all create *bound variables*. For example, the variable $x$ is bound in the subterm $Q$ within $\text{case}(M; x_A, P; y_B, Q)$. Similarly, the variable $x$ is bound in $N$ within $\text{let}_\mu \text{mod}_\nu(x_A) \leftarrow M$ in $N$. Thus, the usual rules of capture avoidance need to be employed.

## 5.1. Metatheory

We have the following metatheoretic results on the term assignment system.

It is also worth noting that any metatheorem we establish about this system is also a metatheorem about the logic given in Fig. 1: all we have to do is *erase* the new ingredients (terms, variables, and so on). Thus, the theorems established in this section directly correspond to the claims in §3.5.

**Theorem 5.1** (Structural rules). *The following rules are admissible.*

$$\frac{\begin{array}{c} \text{VARWK} \\ \Gamma, x : (\mu \mid A), \Delta \text{ ctx } @ p \quad \Gamma, \Delta \vdash M : C @ p \\ \hline \Gamma, x : (\mu \mid A), \Delta \vdash M : C @ p \end{array}}{\text{VARWK}}$$

$$\frac{\begin{array}{c} \text{EXCH} \\ \Gamma, x : (\mu \mid A), y : (\nu \mid B), \Delta \vdash M : C @ p \\ \hline \Gamma, y : (\nu \mid B), x : (\mu \mid A), \Delta \vdash M : C @ p \end{array}}{\text{EXCH}}$$

*Proof.* By induction on the derivation of the premises.

As discussed in §3.5, we cannot be cavalier with adding locks to the context. The following rule describes how to weaken already extant locks. Given a 2-cell $\alpha$ and two (disjoint) pre-contexts $\Gamma$ and $\Delta$, we define the *partial* metatheoretic operation

$$M[\Gamma; \alpha; \Delta]$$

by the following clauses:

$$\begin{aligned} x^{\alpha'}[\Gamma, x : (\rho \mid A), \Gamma'; \alpha; \Delta] &\stackrel{\text{def}}{=} x^{(1_{\text{locks}(\Gamma')} * \alpha * 1_{\text{locks}(\Delta)}) \circ \alpha'} \\ x^{\alpha'}[\Gamma; \alpha; \Delta, x : (\rho \mid A), \Delta'] &\stackrel{\text{def}}{=} x^{\alpha'} \\ (\lambda x : (\xi \mid A), M)[\Gamma; \alpha; \Delta] &\stackrel{\text{def}}{=} \lambda x : (\xi \mid A), M[\Gamma; \alpha; \Delta, x : (\xi \mid A)] \\ (M(N)_\xi)[\Gamma; \alpha; \Delta] &\stackrel{\text{def}}{=} (M[\Gamma; \alpha; \Delta])(N[\Gamma; \alpha; \Delta, \text{🚆}_\xi])_\xi \\ \text{mod}_\xi(M)[\Gamma; \alpha; \Delta] &\stackrel{\text{def}}{=} \text{mod}_\xi(M[\Gamma; \alpha; \Delta, \text{🚆}_\xi]) \end{aligned}$$

22

$$\operatorname{let}_{\rho} \operatorname{mod}_{\xi}(x_{A}) \leftarrow M \text { in } N[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \operatorname{let}_{\rho} \operatorname{mod}_{\xi}(x_{A}) \leftarrow M[\Gamma ; \alpha ; \Delta, \widehat{\mathbf{0}}_{\rho}] \text { in } N[\Gamma ; \alpha ; \Delta, x:(\rho \circ \xi \mid A)]$$

$$(M, N)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} (M[\Gamma ; \alpha ; \Delta], N[\Gamma ; \alpha ; \Delta])$$

$$\pi_{i}(M)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \pi_{i}(M[\Gamma ; \alpha ; \Delta])$$

$$\operatorname{in}_{i}(M)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \operatorname{in}_{i}(M[\Gamma ; \alpha ; \Delta])$$

$$\operatorname{case}(M ; x_{A} . P ; y_{B} . Q)[\Gamma ; \alpha ; \Delta] \stackrel{\text { def }}{=} \operatorname{case}(M[\Gamma ; \alpha ; \Delta]; x_{A} . P[\Gamma ; \alpha ; \Delta, x:(1 \mid A)] ; y_{B} . Q[\Gamma ; \alpha ; \Delta, y:(1 \mid B)])$$

**Theorem 5.2** (Lock Weakening). *In the following rule the term in the conclusion is well-defined when the premises hold, and the rule itself is admissible.*

$$\frac{\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta \vdash M : A @ p \quad \alpha : \mu \Rightarrow \nu}{\Gamma, \widehat{\mathbf{0}}_{\nu}, \Delta \vdash M[\Gamma ; \alpha ; \Delta] : A @ p}$$

*Proof.* By induction on the derivation of $\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta \vdash M : A @ p$. We prove only the non-trivial cases: the rest follow by straightforward applications of the IH.

$$\operatorname{CASE}(\Gamma, x:(\rho \mid A), \Gamma', \widehat{\mathbf{0}}_{\mu}, \Delta \vdash x^{\alpha'} : A @ a).$$

We have that

$$x^{\alpha'}[\Gamma, x:(\rho \mid A), \Gamma'; \alpha ; \Delta] \stackrel{\text { def }}{=} x^{\operatorname{locks}(\Gamma') * \alpha * 1_{\operatorname{locks}(\Delta)} \circ \alpha'}$$

The result then follows, for $\alpha': \rho \Rightarrow \operatorname{locks}(\Gamma') \circ \mu \circ \operatorname{locks}(\Delta)$, whence

$$\operatorname{locks}(\Gamma') * \alpha * 1_{\operatorname{locks}(\Delta)} \circ \alpha': \rho \Rightarrow \operatorname{locks}(\Gamma') \circ \nu \circ \operatorname{locks}(\Delta)$$

$$\operatorname{CASE}(\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta, x:(\rho \mid A), \Delta' \vdash x^{\alpha'} : A @ a).$$

The result immediately follows because $x^{\alpha'}[\Gamma ; \alpha ; \Delta, x:(\rho \mid A), \Delta'] \stackrel{\text { def }}{=} x^{\alpha'}$.

$$\operatorname{CASE}(\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta \vdash \operatorname{mod}_{\xi}(M):\langle \xi \mid A \rangle @ p).$$

Writing $\xi: a \rightarrow p$, it must be that

$$\Gamma, \widehat{\mathbf{0}}_{\mu}, \Delta, \widehat{\mathbf{0}}_{\xi} \vdash M : A @ a$$

By the IH, we get that

$$\Gamma, \widehat{\mathbf{0}}_{\nu}, \Delta, \widehat{\mathbf{0}}_{\xi} \vdash M[\Gamma ; \alpha ; \Delta, \widehat{\mathbf{0}}_{\xi}] : A @ a$$

so by an application of MOD we have

$$\Gamma, \widehat{\mathbf{0}}_{\nu}, \Delta \vdash \operatorname{mod}_{\xi}(M[\Gamma ; \alpha ; \Delta, \widehat{\mathbf{0}}_{\xi}]):\langle \xi \mid A \rangle @ a$$

But as this is exactly $\operatorname{mod}_{\xi}(M)[\Gamma ; \alpha ; \Delta]$ we obtain the result.

23

CASE(Γ, ℍ_μ, Δ ⊢ let_ρ mod_ξ(x_A) ← M in N : B @ p).

Suppose ρ : q → p. We then know that

$$\begin{array}{l} \Gamma, \text{ℍ}_\mu, \Delta, \text{ℍ}_\rho \vdash M : \langle \xi \mid A \rangle @ q \\ \Gamma, \text{ℍ}_\mu, \Delta, x : (\rho \circ \xi \mid A) \vdash N : B @ p \end{array}$$

Then by the IH we have that

$$\begin{array}{l} \Gamma, \text{ℍ}_\nu, \Delta, \text{ℍ}_\rho \vdash M[\Gamma; \alpha; \Delta, \text{ℍ}_\rho] : \langle \xi \mid A \rangle @ p \\ \Gamma, \text{ℍ}_\nu, \Delta, x : (\rho \circ \xi \mid A) \vdash N[\Gamma; \alpha; \Delta, x : (\rho \circ \xi \mid A)] : B @ q \end{array}$$

so by a single application of LET we have

$$\Gamma, \text{ℍ}_\nu, \Delta \vdash \text{let}_\rho \text{ mod}_\xi(x_A) \leftarrow M[\Gamma; \alpha; \Delta, \text{ℍ}_\rho] \text{ in } N[\Gamma; \alpha; \Delta, x : (\rho \circ \xi \mid A)] : B @ p$$

But this term is by definition equal to (let_ρ mod_ξ(x_A) ← M in N)[Γ; α; Δ].

CASE(Γ, ℍ_μ, Δ ⊢ λx : (ξ | A). M : (ξ | A) → B @ p).

We know that

$$\Gamma, \text{ℍ}_\nu, \Delta, x : (\xi \mid A) \vdash M : B @ p$$

By the IH we have that

$$\Gamma, \text{ℍ}_\nu, \Delta, x : (\xi \mid A) \vdash M[\Gamma; \alpha; \Delta, x : (\xi \mid A)] : B @ p$$

So, as

$$(\lambda x : (\xi \mid A). M)[\Gamma; \alpha; \Delta] \stackrel{\text{def}}{=} \lambda x : (\mu \mid A). M[\Gamma; \alpha; \Delta, x : (\xi \mid A)]$$

the result follows by an application of LAM.

CASE(Γ, ℍ_μ, Δ ⊢ M(N)_ξ : B @ b).

Writing ξ : a → b, we know that

$$\begin{array}{l} \Gamma, \text{ℍ}_\mu, \Delta \vdash M : (\xi \mid A) \rightarrow B @ b \\ \Gamma, \text{ℍ}_\mu, \Delta, \text{ℍ}_\xi \vdash N : A @ a \end{array}$$

By the IH, we obtain

$$\begin{array}{l} \Gamma, \text{ℍ}_\nu, \Delta \vdash M[\Gamma; \alpha; \Delta] : (\xi \mid A) \rightarrow B @ b \\ \Gamma, \text{ℍ}_\nu, \Delta, \text{ℍ}_\xi \vdash N[\Gamma; \alpha; \Delta, \text{ℍ}_\xi] : A @ a \end{array}$$

By a single application of APP we obtain

$$\Gamma, \text{ℍ}_\nu, \Delta \vdash (M[\Gamma; \alpha; \Delta])(N[\Gamma; \alpha; \Delta, \text{ℍ}_\xi])_\xi : B @ b$$

and as this term is exactly the definiens of (M(N)_ξ)[Γ; α; Δ] we obtain the result.

24

With lock weakening at hand, we define a metatheoretic operation

$$N[\Gamma; M/x]$$

which stands for the *substitution* of $M$ for the variable $x$ under context $\Gamma$. In most cases this operation simply recurses appropriately through the structure of the term. The novel clauses are

$$\begin{aligned} &x^{\alpha}[\Gamma; M/x] \stackrel{\text{def}}{=} M[\Gamma; \alpha; \cdot] \\ &\text{mod}_{\xi}(N)[\Gamma; M/x] \stackrel{\text{def}}{=} \text{mod}_{\xi}(N[\Gamma; M/x]) \\ &(\text{let}_{\rho} \text{ mod}_{\xi}(y_A) \leftarrow N_0 \text{ in } N_1)[\Gamma; M/x] \stackrel{\text{def}}{=} \text{let}_{\rho} \text{ mod}_{\xi}(y_A) \leftarrow N_0[\Gamma; M/x] \text{ in } N_1[\Gamma; M/x] \end{aligned}$$

The rest of the clauses are according to custom. Notice that $\Gamma$ is a global parameter to this definition, and is only used in the base case in order to effect lock weakening.

**Theorem 5.3** (Cut). *The following rule is admissible:*

$$\frac{\Gamma, \widehat{\bullet}_{\mu} \vdash M : A \circledcirc n \quad \Gamma, x : (\mu \mid A), \Delta \vdash N : B \circledcirc b}{\Gamma, \Delta \vdash N[\Gamma; M/x] : B \circledcirc b}$$

*Proof.* By induction on the derivation of $\Gamma, x : (\mu \mid A), \Delta \vdash N : B \circledcirc b$. We show only the modal cases, the rest being according to custom.

$\text{CASE}(\Gamma, x : (\mu \mid A), \Delta \vdash x^{\alpha} : A \circledcirc b)$.

Writing $\mu : n \rightarrow m$, we have $\alpha : \mu \Rightarrow \text{locks}(\Delta)$, and hence $b = n$. By **Theorem 5.2** we have that

$$\Gamma, \widehat{\bullet}_{\text{locks}(\Delta)} \vdash M[\Gamma; \alpha; \cdot] : A \circledcirc n$$

Hence, by repeatedly using the equation $\Gamma, \widehat{\bullet}_{\mu}, \widehat{\bullet}_{\nu} = \Gamma, \widehat{\bullet}_{\mu \circ \nu} \text{ ctx } \circledcirc o$ on the context to unfuse the locks into the right arrangement, followed by repeated applications of the weakening rule **VARWK** shown admissible in **Theorem 5.1**, we deduce that

$$\Gamma, \Delta \vdash M[\Gamma; \alpha; \cdot] : A \circledcirc n$$

But as this is the definiens of $x^{\alpha}[\Gamma; M/x]$ we obtain the conclusion.

$\text{CASE}(\Gamma, x : (\mu \mid A), \Delta \vdash \text{mod}_{\xi}(N) : \langle \xi \mid A \rangle \circledcirc b)$.

Writing $\xi : a \rightarrow b$, we know that

$$\Gamma, x : (\mu \mid A), \Delta, \widehat{\bullet}_{\xi} \vdash N : A \circledcirc a$$

By the IH, we have that

$$\Gamma, \Delta, \widehat{\bullet}_{\xi} \vdash N[\Gamma; M/x] : A \circledcirc a$$

and hence by **MOD**

$$\Gamma, \Delta \vdash \text{mod}_{\xi}(N[\Gamma; M/x]) : \langle \xi \mid A \rangle \circledcirc b$$

But this is exactly the definiens of $\text{mod}_{\xi}(N)[\Gamma; M/x]$.

25

$$\operatorname{CASE}(\Gamma, x : (\mu \mid A), \Delta \vdash \operatorname{let}_{\rho} \operatorname{mod}_{\xi}(y_A) \leftarrow N_0 \text{ in } N_1 : B @ b).$$

Suppose $\rho : a \rightarrow b$. We then know that for some $C$

$$\begin{array}{l} \Gamma, x : (\mu \mid A), \Delta, \widehat{\bullet}_{\rho} \vdash N_0 : \langle \xi \mid C \rangle @ a \\ \Gamma, x : (\mu \mid A), \Delta, y : (\rho \circ \xi \mid C) \vdash N_1 : B @ b \end{array}$$

We deduce by the IH that

$$\begin{array}{l} \Gamma, \Delta, \widehat{\bullet}_{\rho} \vdash N_0[\Gamma; M/x] : \langle \xi \mid C \rangle @ a \\ \Gamma, \Delta, y : (\rho \circ \xi \mid C) \vdash N_1[\Gamma; M/x] : B @ b \end{array}$$

and hence

$$\Gamma, \Delta \vdash \operatorname{let}_{\rho} \operatorname{mod}_{\xi}(y_A) \leftarrow N_0[\Gamma; M/x] \text{ in } N_1[\Gamma; M/x] : B @ b$$

which is just $(\operatorname{let}_{\rho} \operatorname{mod}_{\xi}(y_A) \leftarrow N_0 \text{ in } N_1)[\Gamma; M/x]$.

**Equational theory** With the preceding metatheorems in hand we are now able to formulate an *equational theory of terms* for this system. The equational theory specifies a minimal set of equations between *proofs* of a certain formula/type. In particular, the cut elimination theorem suggests the following two $\beta$-rules:

$$\frac{\mu : n \rightarrow m \quad \Gamma, x : (\mu \mid A) \vdash M : B @ m \quad \Gamma, \widehat{\bullet}_{\mu} \vdash N : A @ n}{\Gamma \vdash (\lambda x : (\mu \mid A). M)(N)_{\mu} = M[\Gamma; N/x] : B @ m}$$

$$\frac{\mu : n \rightarrow m \quad \nu : o \rightarrow n \quad \Gamma, \widehat{\bullet}_{\mu}, \widehat{\bullet}_{\nu} \vdash M : A @ o \quad \Gamma, x : (\mu \circ \nu \mid A) \vdash N : B @ m}{\Gamma \vdash \operatorname{let}_{\mu} \operatorname{mod}_{\nu}(x_A) \leftarrow \operatorname{mod}_{\nu}(M) \text{ in } N = N[\Gamma; M/x] : B @ m}$$

A very similar equational theory was developed by Gratzer, Kavvos, Nuyts, and Birkedal [Gra+20; Gra+21], but for an algebraically-specified system of dependent types.

Finally, we could also make these equations *directed*, and consider them as *reductions* from one term to another. That way we could see this system as a programming language that is equipped with an *operational semantics*.

## 6. RELATED WORK

Multimode logics were inspired by the decomposition of the ! modality of Linear Logic [Gir87] into two adjoint functors/modalities. This was used by Benton [Ben95] to present Linear Logic through the LNL (linear-non-linear) calculus, which had two modes, linear and intuitionistic. Many years later this pattern was used by [Ree09] in an unpublished manuscript which presented *adjoint logic*, the first multimode and multimodal logic. The modes and modalities of the Reed's logic were presented through a mode theory that was a pre-order; in our terminology this means that the 2-category had no transformations,

26

and between two modes there was at most one modality. The 2-categorical specification of mode theories was introduced by Licata and Shulman [LS16], who presented a single-premise, single-conclusion, multimodal sequent calculus with adjoint modalities. This was later refined by Licata, Shulman, and Riley [LSR17] into a multimode and multimodal framework that also subsumes a number of substructural logics.

The work of of Reed, Licata, and collaborators concerned sequent calculi. Consequently, it was not directly applicable to modal Martin-Löf type theories, which employ the style of natural deduction. A decisive step towards that direction happened with the re-introduction of Fitch-style modal λ-calculi by [Clo18]. The Fitch style of natural deduction, which mirrors the classic opening and closing of proof boxes at the level of proof terms, was adapted to formulate two modal Martin-Löf type theories, one by Birkedal, Clouston, Mannaa, Møgelberg, Pitts, and Spitters [Bir+20] and one by Gratzer, Sterling, and Birkedal [GSB19]. These arise from a Fitch-style formulation of K and S4 respectively.

The next step, which was that of generalising modal Martin-Löf type theories to a multimode, multimodal setting, proved more challenging. The first solution was given by Gratzer, Kavvos, Nuyts, and Birkedal [Gra+20; Gra+21], who combined Reed's mode theories with a Fitch-style 'lock' operation on contexts, and an elimination rule the dual-context style of Davies and Pfenning [DP01; Kav20; PD01]. This particular combination proved to work well in practice, leading to many examples of multimodal type-theoretic reasoning. This type theory directly inspired the logic and modal λ-calculus in this paper. Unlike op. cit. we present the calculus in elementary terms, i.e. without using the machinery of generalised algebraic theories.

Before the work by Gratzer, Kavvos, Nuyts, and Birkedal [Gra+20; Gra+21] there was a limited number of type theories with multiple modalities. These were usually ad-hoc, as the approach was almost always guided by special properties of the modalities of interest. With no claims to completeness we mention the work of Pfenning [Pfe01], Shulman [Shu18], Nuyts, Vezzosi, and Devriese [NVD17], and Nuyts and Devriese [ND18].

# REFERENCES

[Awo10] Steve Awodey. Category Theory. Oxford Logic Guides. Oxford University Press, 2010. ISBN: 978-0-19-161255-8 (cit. on p. 4).

[Ben10] Johan van Benthem. Modal Logic for Open Minds. CSLI Lecture Notes 199. Center for the Study of Language and Information, 2010 (cit. on pp. 1, 18).

[Ben95] P. N. Benton. "A mixed linear and non-linear logic: Proofs, terms and models". In: Computer Science Logic (CSL 1994). Ed. by L. Pacholski and J. Tiuryn. Vol. 933. Lecture Notes in Computer Science. Springer, Berlin, Heidelberg, 1995, pp. 121–135. DOI: 10.1007/BFb0022251 (cit. on p. 26).

[Bir+20] Lars Birkedal, Ranald Clouston, Bassel Mannaa, Rasmus Ejlers Møgelberg, Andrew M. Pitts, and Bas Spitters. "Modal dependent type theory and dependent right adjoints". In: Mathematical Structures in Computer Science 30.2 (2020), pp. 118–138. DOI: 10.1017/S0960129519000197 (cit. on p. 27).

27

[BRV01] Patrick Blackburn, Maarten de Rijke, and Yde Venema. *Modal Logic*. Cambridge University Press, 2001. ISBN: 978-0-521-52714-9 (cit. on p. 4).
[Bor94] Francis Borceux. *Handbook of Categorical Algebra*. Vol. 1. Encyclopedia of Mathematics and its Applications. Cambridge University Press, 1994 (cit. on p. 6).
[CP08] Walter Carnielli and Claudio Pizzi. *Modalities and Multimodalities*. Dordrecht: Springer Netherlands, 2008. DOI: 10.1007/978-1-4020-8590-1. URL: http://link.springer.com/10.1007/978-1-4020-8590-1 (cit. on p. 1).
[Clo18] Ranald Clouston. “Fitch-Style Modal Lambda Calculi”. In: *Foundations of Software Science and Computation Structures*. Ed. by Christel Baier and Ugo Dal Lago. Springer International Publishing, 2018, pp. 258–275 (cit. on p. 27).
[DP01] Rowan Davies and Frank Pfenning. “A modal analysis of staged computation”. In: *Journal of the ACM* 48.3 (2001), pp. 555–604. DOI: 10.1145/382780.382785 (cit. on p. 27).
[DGL16] Stéphane Demri, Valentin Goranko, and Martin Lange. *Temporal logics in computer science: finite-state systems*. Cambridge Tracts in Theoretical Computer Science 58. Cambridge: Cambridge university press, 2016. ISBN: 978-1-107-02836-4 (cit. on p. 1).
[DHK08] Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi. *Dynamic Epistemic Logic*. Dordrecht: Springer Netherlands, 2008. ISBN: 978-1-4020-5839-4. DOI: 10.1007/978-1-4020-5839-4. (Visited on 04/05/2022) (cit. on p. 1).
[Fag+95] Ronald Fagin, Joseph Y. Halpern, Yoram Moses, and Moshe Y. Vardi. *Reasoning About Knowledge*. MIT Press, 1995 (cit. on p. 1).
[Gab+03] Dov M. Gabbay, A. Kurucz, F. Wolter, and M. Zakharyaschev. *Many-dimensional modal logics: theory and applications*. Studies in Logic and the Foundation of Mathematics 148. Elsevier Science B. V., 2003 (cit. on p. 1).
[Gal93] Jean Gallier. “Constructive logics Part I: A tutorial on proof systems and typed $\lambda$-calculi”. In: *Theoretical Computer Science* 110.2 (1993), pp. 249–339. DOI: 10.1016/0304-3975(93)90011-H (cit. on p. 19).
[Gir87] Jean-Yves Girard. “Linear logic”. In: *Theoretical Computer Science* 50.1 (1987), pp. 1–101. ISSN: 03043975. DOI: 10.1016/0304-3975(87)90045-4 (cit. on p. 26).
[GLT89] Jean-Yves Girard, Yves Lafont, and Paul Taylor. *Proofs and Types*. Cambridge Tracts in Theoretical Computer Science 7. Cambridge University Press, 1989 (cit. on pp. 1, 19).

28

[Gra+20] Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. “Multi-modal Dependent Type Theory”. In: *Proceedings of the 35th Annual ACM/IEEE Symposium on Logic in Computer Science*. ACM, 2020, pp. 492–506. ISBN: 978-1-4503-7104-9. DOI: 10.1145/3373718.3394736. URL: https://dl.acm.org/doi/10.1145/3373718.3394736 (visited on 08/18/2020) (cit. on pp. 2, 26, 27).
[Gra+21] Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. “Multi-modal Dependent Type Theory”. In: *Logical Methods in Computer Science* 17.3 (2021). DOI: 10.46298/lmcs-17(3:11)2021 (cit. on pp. 2, 26, 27).
[GSB19] Daniel Gratzer, Jonathan Sterling, and Lars Birkedal. “Implementing a Modal Dependent Type Theory”. In: *Proc. ACM Program. Lang.* 3.ICFP (2019). DOI: 10.1145/3341711. URL: https://doi.org/10.1145/3341711 (cit. on p. 27).
[HKT00] David Harel, Dexter Kozen, and Jerzy Tiuryn. *Dynamic Logic*. Foundations of Computing. MIT Press, 2000. ISBN: 978-0-262-08289-1 (cit. on p. 1).
[Har16] Robert Harper. *Practical Foundations for Programming Languages*. 2nd ed. Cambridge: Cambridge University Press, 2016. ISBN: 978-1-316-57689-2. DOI: 10.1017/CB09781316576892 (cit. on p. 7).
[How80] William A Howard. “The formulae-as-types notion of construction”. In: *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*. Ed. by Jonathan P. Seldin and J. Roger Hindley. Boston, MA: Academic Press, 1980, pp. 479–490. ISBN: 978-0-12-349050-6 (cit. on p. 19).
[HC96] G. E. Hughes and M. J. Cresswell. *A New Introduction to Modal Logic*. Routledge, 1996 (cit. on pp. 3, 4).
[Kav20] G. A. Kavvos. “Dual-Context Calculi for Modal Logic”. In: *Logical Methods in Computer Science* 16.3 (2020). DOI: 10.23638/LMCS-16(3:10)2020. URL: https://arxiv.org/abs/1602.04860 (cit. on p. 27).
[LS16] Daniel R. Licata and Michael Shulman. “Adjoint Logic with a 2-Category of Modes”. In: *Logical Foundations of Computer Science*. Ed. by Sergei Artemov and Anil Nerode. Springer International Publishing, 2016, pp. 219–235. DOI: 10.1007/978-3-319-27683-0_16 (cit. on p. 27).
[LSR17] Daniel R. Licata, Michael Shulman, and Mitchell Riley. “A Fibrational Framework for Substructural and Modal Logics”. In: *2nd International Conference on Formal Structures for Computation and Deduction (FSCD 2017)*. Ed. by Dale Miller. Vol. 84. Leibniz International Proceedings in Informatics (LIPIcs). Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, 2017, 25:1–25:22. DOI: 10.4230/LIPIcs.FSCD.2017.25 (cit. on p. 27).
[Mac78] Saunders Mac Lane. *Categories for the Working Mathematician*. Vol. 5. Graduate Texts in Mathematics. New York, NY: Springer New York, 1978. ISBN: 978-1-4419-3123-8. DOI: 10.1007/978-1-4757-4721-8 (cit. on pp. 4, 6).

29

[Mar96] Per Martin-Löf. “On the meanings of the logical constants and the justification of the logical laws”. In: Nordic Journal of Philosophy 1.1 (1996), pp. 11–60 (cit. on p. 7).
[NPS90] Bengt Nordström, Kent Petersson, and Jan M. Smith. Programming in Martin-Löf’s Type Theory: an Introduction. Oxford University Press, 1990. URL: http://www.cse.chalmers.se/research/group/logic/book/ (cit. on p. 2).
[ND18] Andreas Nuyts and Dominique Devriese. “Degrees of Relatedness”. In: Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science - LICS ’18. New York, New York, USA: ACM Press, 2018, pp. 779–788. ISBN: 978-1-4503-5583-4. DOI: 10.1145/3209108.3209119. URL: http://dl.acm.org/citation.cfm?doid=3209108.3209119 (cit. on p. 27).
[NVD17] Andreas Nuyts, Andrea Vezzosi, and Dominique Devriese. “Parametric quantifiers for dependent type theory”. In: Proceedings of the ACM on Programming Languages 1.ICFP (2017). DOI: 10.1145/3110276 (cit. on p. 27).
[Pfe01] F. Pfenning. “Intensionality, extensionality, and proof irrelevance in modal type theory”. In: Proceedings 16th Annual IEEE Symposium on Logic in Computer Science. IEEE, 2001, pp. 221–230. URL: https://www.cs.cmu.edu/~fp/papers/lics01.pdf (cit. on p. 27).
[PD01] Frank Pfenning and Rowan Davies. “A Judgmental Reconstruction of Modal Logic”. In: Mathematical Structures in Computer Science 11.4 (2001), pp. 511–540. DOI: 10.1017/S0960129501003322. URL: http://www.cs.cmu.edu/~fp/papers/mscs00.pdf (cit. on pp. 7, 27).
[Pit01] Andrew M. Pitts. “Categorical Logic”. In: Handbook of Logic in Computer Science. Ed. by S. Abramsky, Dov M. Gabbay, and T. S. E. Maibaum. Vol. 5. Clarendon Press, 2001 (cit. on p. 1).
[Pra65] Dag Prawitz. Natural Deduction: A Proof-theoretical Study. Almquist and Wiksell, 1965 (cit. on p. 2).
[Pra06] Dag Prawitz. Natural Deduction: A Proof-theoretical Study. Dover Books on Mathematics. Dover Publications, 2006. ISBN: 978-0-486-44655-4 (cit. on p. 2).
[Ree09] Jason Reed. “A Judgmental Deconstruction of Modal Logic”. 2009. URL: http://www.cs.cmu.edu/~jcreed/papers/jdml.pdf (cit. on p. 26).
[SS86] Stephen Schanuel and Ross Street. “The free adjunction”. In: Cahiers de topologie et géométrie différentielle catégoriques 27.1 (1986), pp. 81–83. URL: http://www.numdam.org/article/CTGDC_1986_27_1_81_0.pdf (cit. on p. 17).
[Shu18] Michael Shulman. “Brouwer’s fixed-point theorem in real-cohesive homotopy type theory”. In: Mathematical Structures in Computer Science 28.6 (2018), pp. 856–941. DOI: 10.1017/S0960129517000147 (cit. on p. 27).

30

[SU06] Morten Heine Sørensen and Pawel Urzyczyn. *Lectures on the Curry-Howard Isomorphism*. Elsevier, 2006. ISBN: 978-0-444-52077-7 (cit. on pp. 1, 19).
[Sti01] Colin Stirling. *Modal and Temporal Properties of Processes*. Ed. by David Gries and Fred B. Schneider. Texts in Computer Science. New York, NY: Springer New York, 2001. DOI: 10.1007/978-1-4757-3550-5. URL: http://link.springer.com/10.1007/978-1-4757-3550-5 (visited on 04/05/2022) (cit. on p. 1).

31