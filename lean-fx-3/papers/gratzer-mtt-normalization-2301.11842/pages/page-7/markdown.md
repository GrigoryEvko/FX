Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:7

type theory. In order to crystallize MTT precisely enough for the normalization result, we will view MTT as a particular generalized algebraic theory (GAT). Accordingly, binding is handled by De Bruijn indices and the theory uses explicit substitutions [ML92]. On the other hand, we will not use De Bruijn indices and explicit substitutions when working with MTT as a metalanguage. In these instances, we will treat MTT as a normal type theory and avail ourselves of conveniences similar to what a proof assistant like Agda might provide.

As a compromise, we introduce MTT in Sections 2.1 and 2.2 as a formal theory but go through several important constructions in Section 2.3 using the informal surface-language employed by much of Section 5. For a comprehensive account of both perspectives, we refer the reader to Gratzer et al. [GKNB21].

2.1. Mode-local connectives in MTT. Each mode in MTT constitutes its own separate type theory. In fact, each mode m is equipped with its own copy the of judgments of type theory e.g., $\Gamma \subset \mathbb{R} \otimes m$, $\Gamma \vdash A \otimes m$, $\Gamma \vdash M : A \otimes m$. Much of the theory of MTT is mode-local and only mentions a single copy of these judgments at a time. For these connectives the rules are precisely the standard rules from MLTT, replicated for each mode. The connectives of type theory—dependent sums, intensional identity types, booleans—are all incorporated in this fashion. Each mode also contains a weak universe à la Tarski. Explicitly, this means that there are separate codes and an $\mathsf{EI}(-)$ operation decoding a code to a type, but the decoding operation only commutes with connectives up to isomorphism. While the restriction to weak universes is not fundamental, it simplifies the proof and recent implementations have shown them to be practical [Red20].

2.2. Modalities in MTT. The novelty of MTT comes from those connectives which mix two modes: the modalities. MTT draws inspiration from Fitch-style type theories [Clo18, BCM$^{+}$20] and defines each modality together with an adjoint action on contexts. Accordingly, each $\mu : n \longrightarrow m$ defines a context former sending contexts in mode $m$ to contexts in mode $n$ and this is then used to define modal types $\langle \mu \mid A \rangle$:

$$\frac{\Gamma \subset \mathbb{R} \otimes m}{\Gamma \cdot \{\mu\} \subset \mathbb{R} \otimes n} \qquad \frac{\Gamma \cdot \{\mu\} \vdash A \otimes n}{\Gamma \vdash \langle \mu \mid A \rangle \otimes m} \qquad \frac{\Gamma \cdot \{\mu\} \vdash M : A \otimes n}{\Gamma \vdash \mathsf{mod}_{\mu}(M) : \langle \mu \mid A \rangle \otimes m}$$

These context operations assemble into a 2-functor $m \mapsto \mathsf{C}\mathsf{x}_m$ from $\mathcal{M}^{\mathsf{coop}}$ to the category of categories, selecting the various categories of contexts.$^4$ Concretely, a substitution $\Delta \vdash \gamma : \Gamma \otimes m$ lifts to a substitution $\Delta \cdot \{\mu\} \vdash \gamma \cdot \{\mu\} : \Gamma \cdot \{\mu\} \otimes n$ and each 2-cell $\alpha : \nu \longrightarrow \mu$ induces a substitution $\Gamma \cdot \{\mu\} \vdash \{\alpha\} : \Gamma \cdot \{\nu\} \otimes n$. These operations satisfy several equations to organize them into a 2-functor e.g., $\Gamma \cdot \{\mu\} \vdash \mathsf{id} \cdot \{\mu\} = \mathsf{id} : \Gamma \cdot \{\mu\} \otimes n$ and $\Gamma \cdot \{\mu\} \cdot \{\xi\} = \Gamma \cdot \{\mu \circ \xi\} \subset \mathbb{R} \otimes o$. We record these rules in Figure 1.

Two basic questions remain: what is the elimination principle for $\langle \mu \mid A \rangle$ and which terms can be constructed in the context $\Gamma \cdot \{\mu\}$? Both of these problems are addressed through the same idea, the final component of MTT. We generalize the context extension $\Gamma \cdot A$ from MLTT to annotate each variable with a modality:

$$\frac{\Gamma \subset \mathbb{R} \otimes m \qquad \Gamma \cdot \{\mu\} \vdash A \otimes n}{\Gamma \cdot (\mu \mid A) \subset \mathbb{R} \otimes m}$$

$^4$Given a 2-category $\mathcal{C}$, recall that $\mathcal{C}^{\mathsf{coop}}$ is a 2-category with the same objects as $\mathcal{C}$ but with 1- and 2-cells reversed.