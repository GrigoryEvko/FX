Logical Methods in Computer Science  
Volume 22, Issue 1, 2026, pp. 27:1–27:42  
<https://lmcs.episciences.org/>

Submitted Jan. 30, 2023  
Published Mar. 17, 2026

# NORMALIZATION FOR MULTIMODAL TYPE THEORY

DANIEL GRATZER

Aarhus University e-mail address: gratzer@cs.au.dk

**ABSTRACT.** We prove normalization for MTT, a general multimodal dependent type theory capable of expressing modal type theories for guarded recursion, internalized parametricity, and various other prototypical modal situations. We prove that deciding type checking and conversion in MTT can be reduced to deciding the equality of modalities in the underlying modal situation, immediately yielding a type checking algorithm for all instantiations of MTT in the literature. This proof uses a generalization of *synthetic Tait computability*—an abstract approach to gluing proofs—to account for modalities. This extension is based on MTT itself, so that this proof also constitutes a significant case study of MTT.

## 1. INTRODUCTION

If type theory is classically the study of objects invariant under change of context, modal type theory is the study of adding non-invariant connectives—*modalities*—to type theory. Given that many natural features of particular models of type theory are not invariant under substitution, modal type theories have sparked considerable interest. By nature, however, modal type theories must thread the needle of presenting modalities in such a way that the classical substitution theorems of type theory still hold.

Typically, modal type theories require modifications to the apparatus of contexts and substitutions. Unfortunately, these tweaks are often more art than science, with expert attention required even to make the most trivial modification to the modal structure of a type theory. In order to address this complexity, *general* modal type theories have been introduced [LSR17, GKNB20a]. These theories can be instantiated by a description of a modal situation to produce a system enjoying the theorems usually proved by experts.

### 1.1. Multimodal type theory.

We focus on one such general modal type theory: MTT [GKNB20a]. MTT can be instantiated with an arbitrary collection of modalities and transformations between them to yield a highly usable syntax. The modalities in MTT behave like (weak) dependent right adjoints (DRAs) [BCM$^{+}$20] so that MTT can be used to internalize nearly any right adjoint. This flexibility allows MTT to encode calculi for guarded recursion, internalized parametricity, and other handcrafted calculi.

More precisely, MTT can be instantiated by a *mode theory*, a strict 2-category describing modes, modalities, and natural transformations between these modalities. This 2-categorical structure is then reflected into the structure of substitutions in MTT, ensuring that e.g., a transformation between two modalities $\mu$ and $\nu$ gives rise to a function $\langle \mu \mid A \rangle \rightarrow \langle \nu \mid A \rangle$.

LOGICAL METHODS  
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-22(1:27)2026

© NORMALIZATION FOR MULTIMODAL TYPE THEORY  
Creative Commons