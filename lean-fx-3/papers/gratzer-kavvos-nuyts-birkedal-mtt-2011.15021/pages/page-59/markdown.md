Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:59

## 11. RELATED WORK

Modal type theory has been an active area of research for two decades and, as with any active field, a precise taxonomy of modal type theories would be a paper in and of itself. Accordingly, we have not attempted such a task here, and have instead focussed on separating modal type theories into distinct strands based on their judgmental structure. Some of our characterizations are slightly artificial, in that these lines of work are not nearly so separate as we seem to suggest. We feel, however, that this is the simplest way to position MTT in relation to current work.

### 11.1. Dual-context modal calculi.

One of the first papers on (non-linear)$^{11}$ modal type theory was by [PD01], who constructed a proof theory for S4, i.e. a comonadic modality. The central idea of this approach was to reflect the distinction between modal and non-modal assumptions (referred to as 'truth vs. validity' in *op. cit.*) in the judgmental structure of the system itself. The judgments for this calculus then contained not just a context of true propositions, but rather two contexts: one for intuitionistic propositions, and one for modal ones. Following this methodology, Davies and Pfenning internalized previously known patterns of sequent calculus in a natural deduction style [Kav20].

This kind of judgment straightforwardly allows the incorporation of a product-preserving comonad. The type $\square A$ merely internalizes a restriction to modal contexts only:

$$
\frac{\Delta; \cdot \vdash A \text{ true}}{\Delta; \Gamma \vdash \square A \text{ true}} \quad \frac{A \in \Delta \cup \Gamma}{\Delta; \Gamma \vdash A \text{ true}} \quad \frac{\Delta; \Gamma \vdash \square A \text{ true} \quad \Delta, A; \Gamma \vdash B \text{ true}}{\Delta; \Gamma \vdash B \text{ true}}
$$

The second author showed that this pattern adapts well to the necessity fragment of a number of normal modal logics [Kav20]. The dual-context style has been successfully adapted to dependent types: see e.g. the work of [dR15], and the spatial and cohesive type theories of [Shu18]. Similarly, contextual modal type theory [NPP08, BP11, BBS15, PAF$^{+}$19] has used a dual-context-like structure in order to give a systematic account of higher-order abstract syntax.

[Zwa19] continues this program by formulating a precise categorical semantics based on Awodey's natural models for a dependent type theory with either an adjunction (AdjTT) or comonad (CoTT) [Zwa19]. The categorical semantics of MTT and AdjTT are closely related, though with minor differences in the precise definition of the modality. For instance, in MTT only the $\blacktriangle$ operator is required to act upon the context, while in AdjTT the modalities themselves must extend to contexts.$^{12}$ These differences arise because Zwanziger characterizes only a certain, semantically well-behaved subclass of models, while in Section 5 we describe more general models, which also support the syntactic model and the gluing model of Section 6. Syntactically, AdjTT is a multimode type theory that includes a mode for both ends of the adjunction.

Despite these stories of success, the dual-context style is difficult to generalize: as the complexity of the modal situation increases, so must the complexity of the context structure. For instance, the structure of a dependent dual-context type theory enforces that a 'modal' type (one belonging to $\Delta$) may not depend on an 'intuitionistic' type (one belonging to $\Gamma$). This is a reasonable restriction in the case of $\square$, but it is already somewhat limiting. For

$^{11}$The idea of dual contexts arose in linear logic: see [And92, Gir93, Plo93].

$^{12}$This is similar to the relation between a CwF+A and a CwDRA from [BCM$^{+}$20], and we expect a similar relation to exist between the semantics of MTT with a single modality and AdjTT.