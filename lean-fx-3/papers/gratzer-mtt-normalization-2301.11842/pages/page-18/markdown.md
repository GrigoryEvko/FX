27:18

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

an MTT cosmos as a sequence of constants, thereby reducing its construction to a series of programming exercises. It is this characterization of MTT-cosmoi that we will use in Section 5 to construct the normalization cosmos.

Remark 3.13. Some caution is required here, as a presheaf cosmos will frequently host more than one interpretation of MTT, with different universes of types. In particular, if we consider the collection of presheaf categories \( E = \mathbf{PSh}(F(-)) \) where \( F \) is a strict 2-functor coming from a model of MTT, we may interpret MTT into \( E \) either by choosing types to be arbitrary families of presheaves, or locally representable families of presheaves. This is comparable to Diagram 3.1, where type theory is used to describe a model of type theory.

Within this internal language, the universe \(\tau_{m}:\mathcal{T}_{m}^{\bullet}\longrightarrow\mathcal{T}_{m}\) is encoded by a pair of types:

\[
\mathsf {T y} _ {m}: \mathsf {U} _ {0} \qquad \mathsf {T m} _ {m}: (A: \mathsf {T y} _ {m}) \to \mathsf {U} _ {0}
\]

Each of the diagrams discussed in Sections 3.1 and 3.2 can then be translated into constants within this language with the use of dependent types automatically encoding commutativity. For instance, Diagram 3.4 becomes the following pair of constants:

\[
\mathsf {M o d} _ {\mu}: (\mu \mid \mathsf {T y} _ {n}) \to \mathsf {T y} _ {m} \qquad \mathsf {m} _ {\mu}: (\mu \mid A: \mathsf {T y} _ {n}) (\mu \mid \mathsf {T m} _ {n} (A)) \to \mathsf {T m} _ {m} (\mathsf {M o d} _ {\mu} (A))
\]

In this language it is far easier to specify the modal elimination principle:

letmod \( _{\mu;\nu} \) :

\[
(\nu \circ \mu \mid A: \mathsf {T y} _ {n}) (B: (\nu \mid \mathsf {T m} _ {n} (\mathsf {M o d} _ {\mu} (A))) \to \mathsf {T y} _ {o})
\]

\[
\left(b: \left(\nu \circ \mu \mid x: \mathsf {T m} _ {n} (A)\right)\rightarrow \mathsf {T m} _ {o} \big (B (\mathsf {m} _ {\mu} (A, x)) \big)\right)
\]

\[
\rightarrow (\nu \mid a: \mathsf {T m} _ {m} (\mathsf {M o d} _ {\mu} (A))) \rightarrow \mathsf {T m} _ {o} (B (a))
\]

Each argument to  \( letmod_{\mu;\nu} \)  corresponds directly to a premise of the rule given in Section 2. The hypothetical judgment is encoded by the dependent products in the language and each occurrence of  \( -.\{-\} \)  is replaced with an occurrence of the corresponding modal type within the metalanguage. The  \( \beta \) -rule for this elimination principle is encoded by another constant inhabiting the equality type:

Mod/beta \( _{\mu;\nu} \) :

\[
(\nu \circ \mu \mid A: \mathsf {T y} _ {n}) (B: (\nu \mid \mathsf {T m} _ {n} (\mathsf {M o d} _ {\mu} (A))) \to \mathsf {T y} _ {o})
\]

\[
\left(b: \left(\nu \circ \mu \mid x: \mathsf {T m} _ {n} (A)\right)\rightarrow \mathsf {T m} _ {o} \big (B (\mathsf {m} _ {\mu} (A, x)) \big)\right)
\]

\[
\rightarrow (\nu \circ \mu \mid a: \mathsf {T m} _ {m} (A)) \rightarrow \mathsf {l e t m o d} _ {\mu ; \nu} (A, B, b, \mathsf {m} _ {\mu} (A, a)) = b (a)
\]

The remaining connectives are detailed in Figure 4.

## 4. MULTIMODAL SYNTHETIC TAIT COMPUTABILITY

In light of Section 3, we revise the proof outlined in Section 1: instead of constructing a glued model of MTT, we will construct a glued MTT cosmos. In fact, we will construct a glued presheaf cosmos, and take advantage of the internal language discussed in Section 3.3 to upgrade it to an MTT cosmos with a projection onto S. Prior to this, however, we must show that (1) a pair of cosmoi can be glued together and (2) that each mode of the internal language of the resulting cosmos can be extended with synthetic Tait computability primitives compatible with the already-present MTT modalities.