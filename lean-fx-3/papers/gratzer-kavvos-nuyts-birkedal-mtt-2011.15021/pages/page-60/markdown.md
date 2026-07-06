11:60

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

instance, it should be allowed for a valid type to depend on a merely true $\square A$. Making such an adjustment would not only present a typographical problem (with a type occurring to the left of one of its dependencies), it would render the introduction rule for $\square A$ nonsensical.

This restriction proves even more difficult to manage once there is not merely one modality, but two distinct modalities ones, say $\mu$ and $\nu$. Questions such as “should the $\mu$-modified types be allowed to depend on $\nu$-modified types?” defy general answers. These questions can be addressed for each specific modal situation. For example, both [Shu18] and [Zwa19] hand-craft a system for two modalities. However, these constructions strongly depend on the structure of the underlying model, encouraging the proliferation of tiresome metatheoretic work as we discussed in Section 1.

What is lacking with the dual-context style is the ability to work systematically with a large class of modal situations without reconsidering the properties of the system in each case. Some of the rules of MTT can be directly traced to rules in dual-context calculi (in particular, the elimination rule for modal types), but the structure of our contexts is radically different, in a way which is far more accommodating.

**11.2. Modal type theories based on left division.** A separate strand of modal type theories builds its syntax around a structure that is termed *left division* by [ND18]. Rather than having a fixed number of distinct modal and intuitionistic contexts, there is a single context consisting of variables with *modal annotations*. The earliest appearance of this pattern is in the work of [Pfe01], where the annotations described a variable as having various degrees of proof (ir)relevance.

In a non-dependent type system, the distinction between annotations and different contexts is artificial: we could simply sort variables by their annotation, and separate them into different context zones. However, once generalized to a dependent type theory have a distinct advantage: they do not impose a fixed dependence schedule between different contexts. Instead, a type may depend on anything preceding it in the context, but the nature of that dependence is moderated by the modal annotations.

The term ‘left division’ is chosen to describe this structure because of the behavior of the introduction rules for modal types. For instance, in [Pfe01], there is a rule for introducing a term in an irrelevant context:

$$\frac{\Gamma^{\oplus} \vdash M : A}{\Gamma \vdash M :_{\text{irr}} A}$$

Here $-^{\oplus}$ is a metatheoretic operation, which traverses the context and removes irrelevance annotations. The effect of this is that all the variables in $\Gamma^{\oplus}$ can be used freely when type-checking $M$. This is acceptable, because $M$ itself is irrelevant. Viewed properly this is a division operation which ‘divides’ all the annotations in $\Gamma$ by $irr$. The metatheory of a full dependent type theory based on this idea was considered by [AS12], who prove that modelling irrelevance in this way is sound and decidable.

More recent work by the third author [NVD17, ND18] has carried this idea to its natural conclusion by incorporating an entire hierarchy of modalities. In a related but distinct line of work, the Granule Project [GKO$^{+}$16, OLEI19] has exploited a similar structure to give a systematic account of substructurality. There is ongoing work to extend this to a full dependent type theory.

The modal annotations of MTT are very similar to the modal annotations of variables in calculi with left division. Contrasting MTT with [Pfe01] in particular, we find that there