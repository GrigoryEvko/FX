11:4

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

MTT can be employed to reason about many models of interest, and that it is simple enough to be used in pen-and-paper calculations.

Contributions. In summary, we make the following contributions:

- We introduce MTT, a general type theory for multiple modes and multiple interacting modalities.
- We present a semantics, which constitute a category of models deriving from the generalized algebraic theory that underlies MTT.
- Using the semantics, we prove that—subject to a technical restriction—MTT satisfies canonicity, an important metatheoretic property. This is achieved through a modern gluing argument [Shu15, AK16, Coq19, KHS19].
- Finally, we instantiate MTT with various mode theories, and show its use in reasoning about two specific modal situations, viz. guarded recursion  \( [BGC^{+}16] \) , and internal adjunctions  \( [Shu18, LOPS18] \) .

## 2. THE SYNTAX OF MTT

As mentioned in the introduction, the syntax of MTT is parameterized by a small 2-category called a mode theory. We will later show how to instantiate MTT with a mode theory in order to reason about particular scenarios, but for now we will work over an arbitrary mode theory. We thus fix a mode theory M, and use m, n, o to stand for modes (the objects of M),  \( \mu, \nu, \tau \)  for modalities (the morphisms), and  \( \alpha, \beta, \gamma \)  for 2-cells.

In broad terms, MTT consists of a collection of type theories, one for each mode  \( m \in M \) . These type theories will eventually appear in one another, but only as spectres under a modality. We thus begin by describing the individual type theories at each mode, and then discuss how modalities are used to relate them.

2.1. The Type Theory at Each Mode. Each mode of MTT is inhabited by a standard Martin-Löf Type Theory (MLTT), and accordingly includes the usual judgments. For example, we have the judgment  \( \Gamma \)  ctx @ m which states that  \( \Gamma \)  is a well-formed context in that particular mode m. There are likewise judgments for types, terms, and substitutions at each mode.

\[
\boxed {\Gamma \vdash A \mathsf {t y p e} _ {\ell} @ m}
\]

\[
\frac {\Gamma \mathsf {c t x} @ m}{\Gamma \vdash \mathsf {U} \mathsf {t y p e} _ {1} @ m} \qquad \frac {\Gamma \mathsf {c t x} @ m}{\Gamma \vdash \mathbb {B} \mathsf {t y p e} _ {\ell} @ m} \qquad \frac {\Gamma \mathsf {c t x} @ m \qquad \Gamma \vdash A \mathsf {t y p e} _ {\ell} @ m \qquad \ell \leq \ell^ {\prime}}{\Gamma \vdash \Uparrow A \mathsf {t y p e} _ {\ell^ {\prime}} @ m}
\]

\[
\frac {\Gamma \mathsf {c t x} @ m \qquad \Gamma \vdash A \mathsf {t y p e} _ {\ell} @ m \qquad \Gamma \vdash M , N : \Uparrow A @ m}{\Gamma \vdash \mathsf {I d} _ {A} (M , N) \mathsf {t y p e} _ {\ell} @ m}
\]

\[
\frac {\Gamma \mathsf {c t x} @ m \qquad \Gamma \vdash A \mathsf {t y p e} _ {\ell} @ m \qquad \Gamma , x : \Uparrow A \vdash B \mathsf {t y p e} _ {\ell} @ m}{\Gamma \vdash (x : A) \to B \mathsf {t y p e} _ {\ell} @ m \qquad \Gamma \vdash (x : A) \times B \mathsf {t y p e} _ {\ell} @ m}
\]

Figure 1: Selected mode-local rules.