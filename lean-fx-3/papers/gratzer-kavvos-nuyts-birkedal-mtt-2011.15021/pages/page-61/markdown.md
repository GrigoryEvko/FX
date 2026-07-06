Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:61

are three classes of variables in op. cit.: normal variables (written x : A), irrelevant variables (x ÷ A), and valid variables (x :: A). Such a situation would be modeled in MTT by a single mode that has three endomodalities: irrelevance, extensionality (the identity modality), and validity. A composition table for these modalities can be built from the relations in [Pfe01]'s calculus.

The rules for interacting with the modalities in op. cit. traverse the context and modify the binding used for each variable. This bulk operation is very different to MTT-style locks, but amounts to similar constraints on variable use. By tagging the context with a lock, every time we use a variable we must ensure that the annotated modality sufficiently strong to overcome the lock. When we bulk-update the context, the same restrictions occur but they are performed 'eagerly.'

The use of 'lazy' locks has several advantages over 'eager' bulk updates. For instance, we do not have to explain what it means to divide one modality by another, and non-trivial 2-cells are possible. Furthermore, when interpreting the calculus in a model, it is unnecessary to describe variable by variable how modality update affects the interpretation of the entire context (which can be challenging: see e.g. [Nuy18]).

11.3. Fitch-style modal type theories. A recent series of papers has used a judgmental structure that is similar to MTT in order to manage a variety of modalities [BGM17, BCM+20, GSB19a]. This kind of structure, informally often referred to as the Fitch-style [Clo18], divides the context into regions of variables separated by locks, but does not use annotations on individual variables. Locks are dynamically included or removed by the typing rules.

The central advantage of the Fitch-style is the impressively simple introduction rule for modalities: whenever we wish to introduce a modality we simply append a lock to the context—which tags the modal shift—and continue typechecking. In particular, we never need to remove variables from the context during the introduction of a modal term. Of course, like in MTT this style is only sound for a modality which comes equipped with some sort of left-adjoint-like operation.

Another desirable property of the Fitch-style calculi is their support for strong elimination rules for modalities. Instead of the pattern matching-style rules of other systems, Fitch-style calculi have had an open scope elimination rule for their modalities, which often permits a definitional η-rule for □A. It is generally of the following shape:

$$\frac{\mathfrak{F}(\Gamma) \vdash M : \Box A}{\Gamma \vdash \text{open}(M) : A}$$

ℑ is a meta-theoretic operation on contexts which removes some number of locks and variables from Γ. For instance, in [BCM+20] the operation ℑ(Γ) was defined by

$$\mathfrak{F}(\Gamma, \blacksquare, \Gamma') = \Gamma \text{ where } \blacksquare \notin \Gamma'.$$

This rule is convenient, and strictly more powerful than that of MTT (see Section 7). However, it is metatheoretically less than ideal. The source of the trouble in this case is that we must show that substitutions can be pushed under the open construct. For instance, suppose we have some substitution γ : Δ → Γ, ■, Γ'. It is necessary to ensure that this substitution uniquely gives rise to a substitution ℑ(γ) : ℑ(Δ) → Γ, which will then be applied to the body M of the term. This property can only be shown by lengthy induction on syntax. Such a property is proven laboriously in [GSB19a] for the MLTT_α type theory, and several complex and seemingly artificial typing rules are necessary to show it. The situation