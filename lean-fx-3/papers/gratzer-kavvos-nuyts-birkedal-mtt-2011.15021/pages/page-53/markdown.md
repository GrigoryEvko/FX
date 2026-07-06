Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:53

In **gDTT** the problem of ‘totalising’ a type—which corresponds to reasoning by coinduction—was not handled through the ‘always’ modality, but through clocks. In essence, **gDTT** does not come with a single ▶ modality, but rather with a collection of them, each one indexed by a clock name. There is a quantifier which allows clock names to be bound inside a particular type, and a crucial isomorphism:

$$\forall \kappa \cdot A \cong \forall \kappa \cdot \blacktriangleright^\kappa A \quad (*)$$

**gDTT** presents several technical complications. The syntactic problems pertaining to delayed substitutions were resolved by the introduction of Clocked Type Theory (CloTT) [BGM17], which uses additional judgmental structure. It is conjectured that type-checking is decidable for CloTT. The complexity of using clocks also appears in the semantics of clocked type theory. CloTT is modelled in a collection of presheaf categories, with multiple functors navigating between them [MM18].

It was hoped that some of the complexity could be circumvented by replacing clocks with a modality. This led Clouston et al. to introduce the comonadic ‘always’ modality □, which replaced the isomorphism (*) with □ ▶ $A \cong \square A$ [CBGB15]. The main advantage of using □ is that it can be interpreted in **PSh**($\omega$), which is a much simpler model. On the other hand, the interactions between □ and ▶ have proven difficult to capture in the syntax. In fact, the mere addition of □ to a dependent type theory poses a significant technical challenge: see [BGM17, BCM$^+$20, Shu18, GSB19a]. Despite this concentrated effort, there are still serious technical obstacles to adding ▶ to a type theory for □. **MTT** is the first syntax to accommodate both □, ▶, and validate □ ▶ $A \cong \square A$.

## 10. INTERNAL ADJOINTS

In many cases of interest, the need for a pair of *adjoint modalities* arises: we would like a pair of modalities $\mu : n \rightarrow m$ and $\nu : m \rightarrow n$ so that, in some sense,

$$\langle \nu \mid - \rangle \dashv \langle \mu \mid - \rangle$$

But what does it mean to have an adjunction between two modalities *within* **MTT**? Does it correspond to an external adjunction? And do all known results from category theory apply? The only thing that is certain is that this scenario is fundamental to modal type theory, as a number of intended models can be elegantly presented through adjunctions [SS12, ND18, Shu18].

In this section we show that when **MTT** is equipped with the *walking adjunction* as a mode theory, it becomes a useful syntax for reasoning about adjoint modalities. Of course, the adjoint modalities themselves are not exactly adjoint functors: they are something slightly weaker than DRAs, whose ‘left adjoints’ constitute an adjunction. Nevertheless, we prove that the induced modalities largely behave as expected: the unit and counit are internally definable; some limited forms of internal transposition can be recovered; and left adjoints preserve colimits, as expressed through *crisp induction principles*.