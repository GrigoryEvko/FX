ELECTRONIC NOTES IN
THEORETICAL INFORMATICS
AND COMPUTER SCIENCE

ENTICS
HTTPS://ENTICS.EPISCIENCES.ORG

VOLUME 3
PROCEEDINGS OF
MFPS 2023

# Semantics of Multimodal Adjoint Type Theory*

Michael Shulman$^{a,1}$

$^{a}$ Department of Mathematics
University of San Diego
San Diego, CA, USA

## Abstract

We show that contrary to appearances, Multimodal Type Theory (MTT) over a 2-category $\mathcal{M}$ can be interpreted in any $\mathcal{M}$-shaped diagram of categories having, and functors preserving, $\mathcal{M}$-sized limits, without the need for extra left adjoints. This is achieved by a construction called “co-dextrification” that co-freely adds left adjoints to any such diagram, which can then be used to interpret the “context lock” functors of MTT. Furthermore, if any of the functors in the diagram have right adjoints, these can also be internalized in type theory as negative modalities in the style of FitchTT. We introduce the name Multimodal Adjoint Type Theory (MATT) for the resulting combined general modal type theory. In particular, we can interpret MATT in any finite diagram of toposes and geometric morphisms, with positive modalities for inverse image functors and negative modalities for direct image functors.

Keywords: dependent type theory, modalities, modal type theory, categorical semantics

## 1 Introduction

Modal type theories involve type-forming operations, such as the classical $\square$ (necessity) and $\diamond$ (possibility), whose introduction and elimination rules modify the accessibility of previous hypotheses. The increasing number of modal type theories has led to a need for general frameworks that can be instantiated to any new example, to avoid having to develop the metatheory of each new modal type theory from scratch.

After [26,27], each instantiation of a general modal type theory is determined by a 2-category $\mathcal{M}$, the “mode theory”. Its objects denote “modes”, its morphisms generate modal operators relating types at different modes, and its 2-cells govern their interaction. However, the “LSR” theory of [26,27] is only simply typed, its definitional equality is ill-behaved, and it uses awkward global context operations.

The more recent frameworks MTT [12] and FitchTT [11] resolve these problems: they are dependently typed, with a well-behaved definitional equality, and only ever extend the context; all indications suggest their implementability [10,40]. However, their naïve semantics requires the functors interpreting the modal operators to have additional left adjoints (“context locks”), which are not visible internally in the syntax.

We will show that this defect is, for the most part, only apparent. Namely, from any suitable $\mathcal{M}$-shaped diagram of categories, we construct a new diagram whose functors all do have left adjoints, enabling an

* This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.

$^1$ Email: shulman@sandiego.edu

PUBLISHED NOVEMBER 15, 2023

10.46298/entics.12300

PROCEEDINGS AVAILABLE ONLINE AT

HTTPS://DOI.ORG/10.46298/ENTICS.PROCEEDINGS.MFPS39

© M. SHULMAN

CREATIVE COMMONS

18-2

Semantics of multimodal adjoint type theory

$$\frac{\Gamma \vdash_p a : A}{\Gamma \mid \Delta \vdash_q \mathsf{mod}(a) : \mu \boxdot A}$$

(a) The split-context rule

$$\frac{\Gamma/\mu \vdash_p a : A}{\Gamma \vdash_q \mathsf{mod}(a) : \mu \boxdot A}$$

(b) The division rule

Fig. 1. Comparison of modal introduction rules

interpretation of MTT and FitchTT. Moreover, the types in the new diagram are induced from the original ones, so this interpretation directly yields information about the original diagram. We call this the co-dextrification, since it makes existing functors into right adjoints and has a “cofree” universal property.

To explain the co-dextrification, consider first split-context modal type theories, e.g. as in [33,37,43]. As an example, let $\mathcal{M}$ have two objects and one morphism $\mu : p \to q$; we want to interpret modal type theory in a diagram of two categories and a functor $\mathcal{C}_\mu : \mathcal{C}_p \to \mathcal{C}_q$. The split-context theory has ordinary $p$-judgments $\Gamma \vdash_p \mathcal{J}$, but $q$-judgments $\Gamma \mid \Delta \vdash_q \mathcal{J}$ with the context split into a $p$-part $\Gamma$ and a $q$-part $\Delta$, where $\Delta$ can depend on $\Gamma$. We consider the types in $\Gamma$ to implicitly have $\mathcal{C}_\mu$ applied. The modal rules then rearrange these context parts: Figure 1a shows the split-context introduction rule for the $\mu$-modality.

Following [43], the $q$-contexts $(\Gamma \mid \Delta)$ suggest semantics in the comma category $\widehat{\mathcal{C}}_q = (\mathcal{C}_q \downarrow \mathcal{C}_\mu)$, whose objects are triples $(\Gamma, \Gamma \triangleright \Delta, \mathsf{p}_\Delta)$ where $\Gamma \in \mathcal{C}_p$, $\Gamma \triangleright \Delta \in \mathcal{C}_q$, and $\mathsf{p}_\Delta : \Gamma \triangleright \Delta \to \mathcal{C}_\mu(\Gamma)$. This matches the split-context syntax, but can also be thought of as introducing a context lock functor in a “universal” way: the functor $\widehat{\mathcal{C}}_\mu : \mathcal{C}_p \to \widehat{\mathcal{C}}_q$ sending $\Gamma$ to $(\Gamma, \mathcal{C}_\mu(\Gamma), 1_{\mathcal{C}_\mu(\Gamma)})$ has a left adjoint $(-)/_\mu$, defined by $(\Gamma, \Gamma \triangleright \Delta, \mathsf{p}_\Delta)/_\mu = \Gamma$. Thus, the rule in Figure 1a can also be written as in Figure 1b.

For general $\mathcal{M}$, there is no obvious way to split the context by restricting dependency. Instead, the spiritual generalizations of split-context theories, sometimes called left-division theories (e.g. [32,31]), annotate each context variable with a morphism of $\mathcal{M}$ that is implicitly applied to it, and the modal rules modify these annotations. In our simple example, each variable in a $q$-context is annotated with $\mu$ or $1_q$, and the operation $\Gamma/\mu$ deletes the $1_q$-annotated variables and uses the others to form a $p$-context. For more general $\mathcal{M}$, when defining $\Gamma/\nu$, each annotated variable $x :^\mu A$ in $\Gamma$ is replaced by zero or more variables annotated by a family of morphisms $\varrho_i$ equipped with 2-cells $\alpha_i : \mu \Rightarrow \nu \circ \varrho_i$ forming a left multi-lifting, i.e. such that for any $\beta : \mu \Rightarrow \nu \circ \sigma$ there is a unique $i$ and factorization of $\beta$ through $\alpha_i$ by some $\varrho_i \Rightarrow \sigma$.

Unfortunately, a fully general $\mathcal{M}$ may not have all left multi-liftings. In LSR, each rule application is instead allowed to choose any morphism $\varrho$ with $\alpha : \mu \Rightarrow \nu \circ \varrho$; the problems of LSR stem from the non-uniqueness of such a choice. MTT and FitchTT solve this by delaying the choice of 2-cells, treating $(-)/_\mu$ as a constructor of contexts rather than an operation on them that computes. (It is then sometimes written as $\Gamma \bullet_\mu$ or $\Gamma \cdot \{\mu\}$, but I see no reason not to stick with $\Gamma/\mu$.)

Figure 1b shows $\mu \boxdot(-)$ is “right adjoint” to $(-)/_\mu$, so the semantics of these theories appears to require the modality functors to have left adjoints. This contrasts with how we interpreted the split-context theory in a comma category, creating a new left adjoint. Some work [38,24] tried to generalize this by mimicking annotated contexts in semantics, but this was complicated and difficult. Instead, we change perspective: rather than regarding an object of $(\mathcal{C}_q \downarrow \mathcal{C}_\mu)$ as an object $\Gamma \in \mathcal{C}_p$ together with an object $\Gamma \triangleright \Delta \in \mathcal{C}_q$ that depends on $\mathcal{C}_\mu(\Gamma)$, we regard it as an object $\Delta \in \mathcal{C}_q$ together with a “specified value of $\Delta/\mu$” in $\mathcal{C}_p$, and a weakening substitution from $\Delta$ to $\mathcal{C}_\mu(\Delta/\mu)$. How a context is built from annotated types — like the fact that it is built from types at all — is a property of syntax that doesn’t need to be reflected in semantics. We can now generalize to any $\mathcal{M}$: each $\widehat{\mathcal{C}}_q$ is an oplax limit of the $\mathcal{C}_p$ over a slice 2-category.

It remains to specify how to extend such a context by a type, i.e. how do we compute $(\Gamma, x :^\mu A)/_\nu$ in terms of $\Gamma/\nu$ and $A$? Instead of choosing one pair $(\varrho, \alpha)$ as in LSR, or a universal family of them as in a multi-lifting theory, we use all of them. More precisely, we define $(\Gamma, x :^\mu A)/_\nu$ to be the extension of $\Gamma/\nu$ by the limit of $x :^\varrho A$ over all such $(\varrho, \alpha)$. It is unclear whether this can be done syntactically, but semantically it is unproblematic. When a left multi-lifting exists, this limit reduces to the product of $x :^\varrho A$ over the elements of the multi-lifting. And if there are no such $\varrho$, the limit is a terminal object and $A$ is simply deleted, as happens to $\Delta$ in Figure 1a.

This is the essential idea of co-dextrification. It is formally similar to Hofmann’s “right adjoint splitting” [15] for strict pullbacks, suggesting it can similarly be regarded as a sort of coherence theorem.

Shulman

18–3

The co-dextrification does require each $\mathcal{C}_p$ to have, and each $\mathcal{C}_\mu$ to preserve, limits of the size of $\mathcal{M}$. This is unproblematic if $\mathcal{M}$ is finite, but modal operators often come in adjoint pairs (e.g. as geometric morphisms of topoi), and as soon as $\mathcal{M}$ contains a generic adjunction it is infinite. Fortunately, if some $\mathcal{C}_\mu$ has a right adjoint, that adjoint automatically lifts to a *dependent right adjoint* of $\tilde{\mathcal{C}}_\mu$. Thus, it suffices to apply co-dextrification over a smaller 2-category $\mathcal{L}$ that generates $\mathcal{M}$ by adding some right adjoints.

The resulting type theory represents the morphisms in $\mathcal{L}$ by positive modalities as in MTT, but their right adjoints by negative modalities as in FitchTT. (For a particular $\mathcal{L}$, such a combination appeared in [5].) The positive elimination rules also restrict which morphisms of $\mathcal{M}$ can appear as “framings”: this would be problematic for internalizing functoriality, except for the stronger elimination rule of the negative modalities. We call this theory **Multimodal Adjoint Type Theory (MATT)**. If we regard $\mathcal{L}$, rather than $\mathcal{M}$, as the fundamental parameter of MATT, then it restores the symmetry of [26,27] in which each morphism (of $\mathcal{L}$) generates a positive/negative pair of modalities that are automatically adjoint.

## Acknowledgement

I am extremely grateful to Daniel Gratzer, for many long and illuminating conversations about modal type theories, for many concrete suggestions about MATT (including the name), and for careful reading and bugfixes. Dan Licata also contributed useful ideas to some of these conversations.

## 2 Multimodal Adjoint Type Theory

For a 2-category $\mathcal{M}$ we write its objects as $p, q, r, s, \dots$, its morphisms as $\mu, \nu, \varrho, \sigma, \dots$, and its 2-cells as $\alpha, \beta, \dots$. We use $\circ$ for both composition of morphisms and vertical composition of 2-cells, and write $\mu \triangleleft \beta$ and $\alpha \triangleright \nu$ for whiskering. We will not use horizontal composition of 2-cells.

Although our semantics will have a mode theory with right adjoints added freely, it is simpler to formulate syntax using an arbitrary 2-category $\mathcal{M}$ equipped with placeholders for the necessary restrictions.

**Definition 2.1** An **adjoint mode theory** is a 2-category $\mathcal{M}$ equipped with four classes of morphisms in $\mathcal{M}$ called **tangible**, **sharp**, **transparent**, and **sinister**, such that

- Every identity morphism is transparent and sharp.
- If $\mu : p \rightarrow q$ is sharp and $\nu : q \rightarrow r$ is transparent, then $\nu \circ \mu : p \rightarrow r$ is tangible. (Thus, every transparent or sharp morphism, and in particular every identity morphism, is tangible.)
- Every sinister morphism $\mu : p \rightarrow q$ has a right adjoint $\mu^\dagger : q \rightarrow p$ in $\mathcal{M}$, with unit $\eta_\mu : 1 \Rightarrow \mu^\dagger \circ \mu$ and counit $\epsilon_\mu : \mu \circ \mu^\dagger \Rightarrow 1$.

MATT over an adjoint mode theory $\mathcal{M}$ is MTT [12] over $\mathcal{M}$ with a few modifications. We write $x :^\mu A$ in place of $x : (\mu \mid A)$, and $\mu \square A$ in place of $(\mu \mid A)$. We will show the most important MTT rules, but we omit technical details of substitutions. We now list the substantive modifications.

(1) The modalities annotating variables in contexts must be tangible. Tangibility of identities yields ordinary type theories at each mode. The context rules are shown in Figure 2, along with a substitution rule that combines functoriality and naturality (the other substitution rules are more ordinary), and the variable-use rule in Figure 3 along with the rule for substituting keys into variables.²
(2) The modalities $\mu$ that annotate domains of function-types $(x :^\mu A) \rightarrow B$ must be sharp. Sharpness of identities yields ordinary function-types, and tangibility of sharp morphisms is required for the formation and introduction rules. All the rules are shown in Figure 4.
(3) The modalities $\mu$ that generate positive modal operators $\mu \square A$ must be sharp, and the “framing” modality in its elimination rule must be transparent. The rules for positive modal operators are shown in Figure 5. The elimination rule requires both transparent morphisms, and composites of transparent and sharp morphisms, to be tangible.

² The latter is not fully precise, e.g. we have not defined the “weakening” substitution $\uparrow^\alpha$. In the formal presentation of [12] there is only a zero-variable, to which can be applied substitutions involving 2-cell keys and weakening.

18-4

Semantics of multimodal adjoint type theory

\[
\frac {}{\diamond_ {p} \operatorname{ctx} _ {p}} \qquad \frac {\Gamma \operatorname{ctx} _ {q} \quad \mu : p \to q}{\Gamma / \mu \operatorname{ctx} _ {p}} \qquad \frac {\Gamma \operatorname{ctx} _ {q} \quad \mu : p \to q \text {tangible} \quad \Gamma / \mu \vdash A \operatorname{type} _ {p}}{(\Gamma , x : ^ {\mu} A) \operatorname{ctx} _ {q}}
\]

\[
\frac {\Gamma \operatorname{ctx} _ {r} \qquad \mu : q \to r \qquad \nu : p \to q}{\Gamma / _ {\mu} / _ {\nu} = \Gamma / _ {\{\mu \circ \nu \}}} \qquad \frac {\Gamma \operatorname{ctx} _ {p}}{\Gamma / _ {1 _ {p}} = \Gamma} \qquad \frac {\theta : \Gamma \to_ {q} \Delta \qquad \mu , \nu : p \to q \qquad \alpha : \mu \Rightarrow \nu}{\theta / _ {\alpha} : \Gamma / _ {\nu} \to_ {p} \Delta / _ {\mu}}
\]

Fig. 2. Contexts and substitutions in MATT

\[
\begin{array}{l} \operatorname{locks} \left(\diamond_ {p}\right) = 1 _ {p} \quad \operatorname{locks} \left(\Gamma , x: ^ {\mu} A\right) = \operatorname{locks} (\Gamma) \quad \operatorname{locks} \left(\Gamma / _ {\mu}\right) = \operatorname{locks} (\Gamma) \circ \mu \\ \frac {\alpha : \mu \Rightarrow \operatorname{locks} (\Delta)}{\Gamma , x : ^ {\mu} A , \Delta \vdash x ^ {\alpha} : A [ \uparrow^ {\alpha} ]} \quad \frac {\alpha : \mu \Rightarrow \operatorname{locks} (\Delta) \circ \nu \quad \beta : \nu \Rightarrow \varrho}{(\Gamma , x : ^ {\mu} A , \Delta) / _ {\varrho} \vdash x ^ {\alpha} [ 1 _ {(\Gamma , x : ^ {\mu} A , \Delta)} / _ {\beta} ] = x ^ {(\operatorname{locks} (\Delta) \circ \beta) \circ \alpha}} \\ \end{array}
\]

Fig. 3. Variables in MATT

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma / _ {\mu} \vdash A \text { type } _ {p} \qquad \Gamma , x : ^ {\mu} A \vdash B \text { type } _ {q}}{\Gamma \vdash (x : ^ {\mu} A) \to B \text { type } _ {q}}
\]

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma / _ {\mu} \vdash A \text { type } _ {p} \qquad \Gamma , x : ^ {\mu} A \vdash b : B}{\Gamma \vdash (\lambda x . b) : (x : ^ {\mu} A) \to B}
\]

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma \vdash f : (x : ^ {\mu} A) \to B \qquad \Gamma / _ {\mu} \vdash a : A}{\Gamma \vdash f   a : B [ x \leftarrow a ]}
\]

\[
\frac {\mu : p \to q \text { sharp } \qquad \Gamma , x : ^ {\mu} A \vdash b : B \qquad \Gamma / _ {\mu} \vdash a : A}{\Gamma \vdash (\lambda x . b)   a = b [ x \leftarrow a ] : B [ x \leftarrow a ]} \qquad \frac {\mu : p \to q \text { sharp } \qquad \Gamma , x : ^ {\mu} A \vdash f   x = g   x : B}{\Gamma \vdash f = g : (x : ^ {\mu} A) \to B}
\]

Fig. 4. Modal function-types in MATT

(4) Every sinister morphism generates a negative modal operator. These are not in MTT. Their rules are shown in Figure 6; they simplify those of [11] by using right adjoints instead of parametric ones.

Remark 2.2 If \(\mu\) is both sharp and sinister, the formation and introduction rules of \(\mu \diamondsuit A\) are identical to those of \(\mu^{\dagger} \boxdot A\). Daniel Gratzer has shown that \(\mu \diamondsuit A\) actually satisfies all the rules of \(\mu^{\dagger} \boxdot A\), while conversely if \(\mu\) is transparent then \(\mu^{\dagger} \boxdot A\) satisfies all the rules of \(\mu \diamondsuit A\) except definitional \(\eta\)-conversion.

The flexibility in choosing the tangible, sharp, transparent, and sinister morphisms allows us to compare MATT easily to other modal type theories.

(i) If \(\mathcal{M}\) is any 2-category, and we take all morphisms to be tangible, sharp, and transparent, but none to be sinister, then MATT reduces to MTT.
(ii) For any 2-category \(\mathcal{L}\), let \(\mathcal{M} = \mathcal{L}[\dagger \mathcal{L}]\) be obtained by formally adjoining a left adjoint \(\dagger \mu\) to each \(\mu\) in \(\mathcal{L}\). We take only identities to be tangible, sharp, and transparent, and the sinister morphisms to be these left adjoints \(\dagger \mu\); then MATT reduces to FitchTT [11] over \(\mathcal{L}\) with actual left adjoints.
(iii) The closest match with theories such as [27,37,31] occurs when \(\mathcal{M} = \mathcal{L}[\mathcal{L}^{\dagger}]\) is obtained by formally adjoining a right adjoint \(\mu^{\dagger}\) to each morphism \(\mu\) of \(\mathcal{L}\). In this case we take the tangible, sharp, and sinister morphisms to be the image of \(\mathcal{L}\) in \(\mathcal{L}[\mathcal{L}^{\dagger}]\); thus all the modal operators come in adjoint pairs. Different theories make different choices about transparency: in [37] only identities are transpar

Shulman

18-5

$$\frac{\mu : p \to q \text{ sharp } \quad \Gamma/\mu \vdash A \text{ type}_p}{\Gamma \vdash \mu \boxdot A \text{ type}_q} \quad \frac{\mu : p \to q \text{ sharp } \quad \Gamma/\mu \vdash a : A}{\Gamma \vdash \text{mod}_\mu(a) : \mu \boxdot A}$$

$$\begin{array}{l} \mu : p \to q \text{ sharp } \quad \nu : q \to r \text{ transparent } \quad \Gamma/\nu \vdash d : \mu \boxdot A \\ \Gamma, y :^\nu \mu \boxdot A \vdash B \text{ type}_r \quad \Gamma, x :^{\nu \circ \mu} A \vdash b : B [y \leftarrow \text{mod}_\mu(x)] \\ \hline \Gamma \vdash \text{let}_\nu \text{ mod}_\mu(x) \leftarrow d \text{ in } b : B [y \leftarrow d] \end{array}$$

$$\begin{array}{l} \mu : p \to q \text{ sharp } \quad \nu : q \to r \text{ transparent } \quad \Gamma/(\nu \circ \mu) \vdash a : A \\ \Gamma, y :^\nu \mu \boxdot A \vdash B \text{ type}_r \quad \Gamma, x :^{\nu \circ \mu} A \vdash b : B [y \leftarrow \text{mod}_\mu(x)] \\ \hline \Gamma \vdash (\text{let}_\nu \text{ mod}_\mu(x) \leftarrow \text{mod}_\mu(a) \text{ in } b) = b [x \leftarrow a] \end{array}$$

Fig. 5. Positive modalities in MATT

$$\begin{array}{l} \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu^\dagger \vdash A \text{ type}_q}{\Gamma \vdash \mu \diamond \to A \text{ type}_p} \quad \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu^\dagger \vdash M : A}{\Gamma \vdash \mu \mapsto M : \mu \diamond \to A} \\ \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu \vdash M : \mu \diamond \to A}{\Gamma \vdash M \circledast \mu : A [1_\Gamma/\epsilon_\mu]} \quad \frac{\mu : p \to q \text{ sinister } \quad \Gamma/(\mu \circ \mu^\dagger) \vdash M : A}{\Gamma \vdash (\mu \mapsto M) \circledast \mu = M [1_\Gamma/\epsilon_\mu] : A [1_\Gamma/\epsilon_\mu]} \\ \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu^\dagger \vdash (M [1_\Gamma/\eta_\mu]) \circledast \mu = (N [1_\Gamma/\eta_\mu]) \circledast \mu : A}{\Gamma \vdash M = N : \mu \diamond \to A} \end{array}$$

Fig. 6. Negative modalities in MATT

ent, while in [31] the transparent morphisms are also the image of $\mathcal{L}$. But in fact, if a morphism is both sinister and tangible, then it “might as well” be transparent, in that elimination rules with it as framing can be deduced from those with identity framing; the proof follows [37, Lemma 5.1].

Our semantics in the co-dextrification will apply to the following case.

Example 2.3 Let $\mathcal{L}$ be any 2-category and $\mathcal{S}$ a class of morphisms in it, and let $\mathcal{M} = \mathcal{L}[\mathcal{S}^\dagger]$ be the result of freely adjoining a right adjoint $\mu^\dagger$ for every morphism $\mu$ in $\mathcal{S}$. We identify $\mathcal{L}$ with its image in $\mathcal{L}[\mathcal{S}^\dagger]$. We take this image $\mathcal{L}$ to be the transparent morphisms, $\mathcal{S}$ to be the sinister morphisms, and the tangible and sharp morphisms to be those that are isomorphic to one of the form $\mu \circ \nu^\dagger$ where $\mu \in \mathcal{L}$ and $\nu \in \mathcal{S}$. This choice of tangible and sharp morphisms appears necessitated by our semantics (see Lemma 5.5), and $\mathcal{L}$ is then the largest class of transparent morphisms satisfying the composition axiom.

Assumption 2.4 We always consider $\mathcal{L}[\mathcal{S}^\dagger]$ to be an adjoint mode theory as in Example 2.3.

Example 2.5 We can regard Two-Level Type Theory [1] as an instance of MATT with two modes, f for (fibrant/inner) types and e for (non-fibrant/outer) exotypes, and an isomorphism $\iota : e \cong f$. We let all the morphisms be tangible, but we take only identities as sharp and transparent, and only the morphism $\iota : e \to f$ as sinister. Then $\iota \diamond \to -$ is the coercion from types to exotypes (c in [1]), with a bijection between terms of types $A$ and $\iota \diamond \to A$. Allowing $\iota$ to be sharp would produce fibrant replacements $\iota \boxdot A$, which are inconsistent [1, §2.7] with univalence for fibrant types and UIP for exotypes. Inspecting the proof shows that the same conclusion would follow if we had modal function-types $(x :^\iota A) \to B$.

Remark 2.6 It seems likely that normalization for MTT [10] extends to MATT. But to deduce decidability of type-checking from this requires decidability of equality for $\mathcal{M}$, whereas $\mathcal{L}[\mathcal{S}^\dagger]$ can fail to have decidable equality even if $\mathcal{L}$ does [7]. However, we can hope that $\mathcal{L}[\mathcal{S}^\dagger]$ will have decidable equality if $\mathcal{L}$

18-6

Semantics of multimodal adjoint type theory

is, say, locally finite (this is true for for 1-categories [6]).

## 3 Natural models of MATT

We now generalize the modal natural models of [12] to MATT. We first recall some definitions.

- A natural model [2] is a representable morphism \(\tau : \mathrm{Tm} \to \mathrm{Ty}\) in a presheaf category \(\mathcal{P}\mathcal{D}\). Thus for any \(A \in \mathrm{Ty}(\Gamma)\) we have an object \(\Gamma \triangleright A \in \mathcal{D}\), a morphism \(\mathfrak{p}_A : \Gamma \triangleright A \to \Gamma\), and a pullback square

\[
\begin{array}{c} \mathfrak {L} (\Gamma \triangleright A) \longrightarrow \mathrm{Tm} \\ \mathfrak {p} _ {A} \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \\ \mathfrak {L} (\Gamma) \xrightarrow [ A ]{} \mathrm{Ty} \end{array} \tag {3.1}
\]

where \(\mathfrak{L}:\mathcal{D}\to \mathcal{P}\mathcal{D}\) denotes the Yoneda embedding. A natural model is equivalent to a category with families. We refer to \(\Gamma \triangleright A\) as the comprehension of \(A\), and \(\mathfrak{p}_A\) as its type projection.

- A modal context structure [12, Definition 5.1] is a 2-functor \(\mathcal{D}:\mathcal{M}^{\mathrm{coop}}\to \mathcal{C}at\) such that each \(\mathcal{D}_p\) has a terminal object. We write its action on morphisms and 2-cells as \(\mathcal{D}^{\mu}\) and \(\mathcal{D}^{\alpha}\) respectively.
- A modal natural model [12, Definition 5.4] is a modal context structure \(\mathcal{D}\) with a morphism \(\tau_p: \mathrm{Tm}_p \to \mathrm{Ty}_p\) in each presheaf category \(\mathcal{P}\mathcal{D}_p\), such that for any \(\mu: p \to q\) in \(\mathcal{M}\), the transformation \((\mathcal{D}^\mu)^*\tau_p\) is representable in \(\mathcal{P}\mathcal{D}_q\). (Taking \(\mu = 1_p\), this implies that each \(\mathcal{D}_p\) is a natural model.) We write the comprehension of \(A \in \tau_p(\mathcal{D}^\mu(\Gamma))\) as \(\mathfrak{p}_A^\mu: \Gamma \triangleright^\mu A \to \Gamma\), and write \(\Gamma \triangleright^1 A\) as \(\Gamma \triangleright A\).

Definition 3.2 Let \(\mathcal{M}\) be an adjoint mode theory. A modal context structure \(\mathcal{D}:\mathcal{M}^{\mathrm{coop}}\to \mathcal{C}at\) is an adjoint modal natural model if we have a morphism \(\tau_p:\mathrm{Tm}_p\to \mathrm{Ty}_p\) in each \(\mathcal{P}\mathcal{D}_p\) such that \((\mathcal{D}^{\mu})^{*}\tau_{p}\) is representable for all tangible \(\mu\). (Since identities are tangible, each \(\mathcal{D}_p\) is still a natural model.)

Definition 3.3 (See [12, §5.2.1]) A \(\Pi\)-structure on an adjoint modal natural model \(\mathcal{D}\) consists of, for any sharp \(\mu : p \to q\), and any \(\Gamma \in \mathcal{D}_q\) and \(A \in \mathrm{Ty}_p(\mathcal{D}^\mu(\Gamma))\) with \(B \in \mathrm{Ty}_q(\Gamma \triangleright^\mu A)\), a type \(\Pi(A, B) \in \mathrm{Ty}_q(\Gamma)\) such that \(\Gamma \triangleright \Pi(A, B)\) is a pushforward of \(\Gamma \triangleright^\mu A \triangleright B\) along \(\mathfrak{p}_A : \Gamma \triangleright^\mu A \to A\), all natural in \(\Gamma\).

Definition 3.4 (See [12, §5.2.2]) An adjoint modal natural model \(\mathcal{D}\) has positive modalities if for any sharp \(\mu : p \to q\) we have:

(i) For any \(\Gamma \in \mathcal{D}_q\) and \(A \in \mathrm{Ty}_p(\mathcal{D}^\mu(\Gamma))\), we have a type \(\mu \boxdot A \in \mathrm{Ty}_q(\Gamma)\) and a map \(j_{\Gamma, A}^\mu : \Gamma \triangleright^\mu A \to \Gamma \triangleright (\mu \boxdot A)\) over \(\Gamma\), all varying naturally in \(\Gamma\).
(ii) For any transparent \(\varrho: q \to r\) and \(\Gamma \in \mathcal{D}_r\) with \(A \in \mathrm{Ty}_p(\mathcal{D}^{\varrho \circ \mu}(\Gamma))\), define the dashed map \(\ell\) below by the universal property of pullbacks and full-faithfulness of \(\mathfrak{L}\):

\[
\begin{array}{c c} \mathfrak {L} (\Gamma \triangleright^ {\varrho \circ \mu} A) \xrightarrow {\mathfrak {L} (\ell)} \mathfrak {L} (\Gamma \triangleright^ {\varrho} (\mu \boxdot A)) \longrightarrow (\mathcal {D} ^ {\varrho}) ^ {*} \mathrm{Tm} _ {q} & = \\ \Big \downarrow & \Big \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \\ \mathfrak {L} (\Gamma) \xlongequal {} \mathfrak {L} (\Gamma) \xrightarrow [ \mu \boxdot A ]{\text {   }} (\mathcal {D} ^ {\varrho}) ^ {*} \mathrm{Ty} _ {q} & = \\ & \Big \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \end{array}
\]

Then for any commutative square as below there is a chosen diagonal filler, natural in \(\Gamma\):

\[
\begin{array}{c} \Gamma \triangleright^ {\varrho \circ \mu} A \longrightarrow \Gamma \triangleright^ {\varrho} (\mu \boxdot A) \triangleright B \\ \ell \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Gamma \triangleright^ {\varrho} (\mu \boxdot A) = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = \\ \end{array}
\]

Definition 3.5 (See [11, Definition 4]) An adjoint modal natural model \(\mathcal{D}\) has negative modalities if

Shulman

18–7

for any sinister $\mu : p \to q$, the functor $\mathcal{D}^{\mu^{\dagger}}$ has a dependent right adjoint [4], i.e. there is a pullback square

$$\begin{array}{c} (\mathcal{D}^{\mu^{\dagger}})^* \mathrm{Tm}_q \longrightarrow \mathrm{Tm}_p \\ (\mathcal{D}^{\mu^{\dagger}})^* \tau_q \Big\downarrow \quad \text{↵} \quad \Big\downarrow \tau_p \\ (\mathcal{D}^{\mu^{\dagger}})^* \mathrm{Ty}_q \longrightarrow \mathrm{Ty}_p. \end{array}$$

Example 3.6 Let $\mathcal{M}$ be the adjoint mode theory for Two-Level Type Theory from Example 2.5, and let $\mathcal{C}$ be a two-level model as in [1, Definition 2.8]. If we ignore universes, this means it has two natural models $\tau^{\mathrm{f}} : \mathrm{Tm}^{\mathrm{f}} \to \mathrm{Ty}^{\mathrm{f}}$ and $\tau^{\mathrm{e}} : \mathrm{Tm}^{\mathrm{e}} \to \mathrm{Ty}^{\mathrm{e}}$, and that $\tau^{\mathrm{f}}$ is a pullback of $\tau^{\mathrm{e}}$. Let $\mathcal{D} : \mathcal{M}^{\mathrm{coop}} \to \mathcal{C}at$ be constant at $\mathcal{C}$, but where $\mathcal{D}_{\mathrm{f}} = \mathcal{C}$ is equipped with $\tau^{\mathrm{f}}$ while $\mathcal{D}_{\mathrm{e}} = \mathcal{C}$ is equipped with $\tau^{\mathrm{e}}$. This is an adjoint modal natural model with negative modalities, since the assumption that $\tau^{\mathrm{f}}$ is a pullback of $\tau^{\mathrm{e}}$ says exactly that the identity functor $(\mathcal{C}, \tau^{\mathrm{e}}) \to (\mathcal{C}, \tau^{\mathrm{f}})$ has a dependent right adjoint.

## 4 Co-dextrification

Assumption 4.1 For all of this section, let $\mathcal{L}$ be an arbitrary 2-category, let $\mathcal{C} : \mathcal{L} \to \mathcal{C}at$ be a pseudo-functor, and let $\kappa$ be an infinite regular cardinal such that $\mathcal{L}$ is $\kappa$-small, each category $\mathcal{C}_p$ has $\kappa$-small limits, and each functor $\mathcal{C}_{\mu} : \mathcal{C}_p \to \mathcal{C}_q$ preserves $\kappa$-small limits. Often, $\kappa$ will be $\omega$.

Definition 4.2 For $r \in \mathcal{L}$, let $\mathcal{L} \mathbin{//} r$ denote the lax slice 2-category:

- Its objects are morphisms $\mu : p \to r$ in $\mathcal{L}$.
- Its morphisms from $\mu : p \to r$ to $\nu : q \to r$ are pairs $(\varrho : p \to q, \alpha : \mu \Rightarrow \nu \circ \varrho)$.
- Its 2-cells from $(\varrho, \alpha)$ to $(\sigma, \beta)$ are 2-cells $\gamma : \varrho \Rightarrow \sigma$ such that $(\nu \triangleleft \gamma) \circ \alpha = \beta$.

By postcomposition, we have a 2-functor $\mathcal{L} \mathbin{//} - : \mathcal{L} \to 2\text{-}\mathcal{C}at$, with projection functors $\pi_r : \mathcal{L} \mathbin{//} r \to \mathcal{L}$.

Definition 4.3 For $r \in \mathcal{L}$, let $\widehat{\mathcal{C}}_r$ denote the oplax limit of the $(\mathcal{L} \mathbin{//} r)$-shaped diagram $\mathcal{C} \circ \pi_r : \mathcal{L} \mathbin{//} r \to \mathcal{C}at$ in $\mathcal{C}at$. Thus, an object $\Gamma \in \widehat{\mathcal{C}}_r$ consists of:

(i) For each $\mu : p \to r$ in $\mathcal{L}$, an object $\Gamma^{\mu} \in \mathcal{C}_p$.
(ii) For each $\varrho : p \to q$ and $\alpha : \mu \Rightarrow \nu \circ \varrho$, a morphism $\Gamma^{\alpha} : \Gamma^{\nu} \longrightarrow \mathcal{C}_{\varrho}(\Gamma^{\mu})$ in $\mathcal{C}_q$. (The notation is abusive, as $\Gamma^{\alpha}$ depends not just on $\alpha$ but on the decomposition of its codomain as a composite.)
(iii) For $\alpha = 1_{\mu} : \mu \Rightarrow \mu \circ 1_p$, we have $\Gamma^{1_{\mu}} = 1_{\Gamma^{\mu}}$.
(iv) For $\alpha : \mu \Rightarrow \nu \circ \varrho$ and $\beta : \nu \Rightarrow \varpi \circ \sigma$, we have $\mathcal{C}_{\sigma}(\Gamma^{\alpha}) \circ \Gamma^{\beta} = \Gamma^{(\beta \circ \varrho) \circ \alpha}$, modulo pseudofunctoriality.
(v) For $\alpha : \mu \Rightarrow \nu \circ \varrho$ and $\beta : \varrho \Rightarrow \sigma$, we have $\mathcal{C}_{\beta}(\Gamma^{\mu}) \circ \Gamma^{\alpha} = \Gamma^{(\nu \triangleleft \beta) \circ \alpha}$.

Similarly, a morphism $\boldsymbol{\theta} : \boldsymbol{\Gamma} \to \boldsymbol{\Delta}$ in $\widehat{\mathcal{C}}_r$ consists of:

(vi) For each $\mu : p \to r$, a morphism $\boldsymbol{\theta}^{\mu} : \boldsymbol{\Gamma}^{\mu} \to \boldsymbol{\Delta}^{\mu}$.

(vii) For $\alpha : \mu \Rightarrow \nu \circ \varrho$, we have $\mathcal{C}_{\varrho}(\boldsymbol{\theta}^{\mu}) \circ \boldsymbol{\Gamma}^{\alpha} = \boldsymbol{\Delta}^{\alpha} \circ \boldsymbol{\theta}^{\nu}$.

Lemma 4.4 The categories $\widehat{\mathcal{C}}_p$ are the action on objects of a modal context structure $\widehat{\mathcal{C}} : \mathcal{L}^{\mathrm{coop}} \to \mathcal{C}at$.

Proof. The functorial action is by composition: $(\widehat{\mathcal{C}}^{\mu}(\Gamma))^{\nu} = \Gamma^{\mu \circ \nu}$ and $(\widehat{\mathcal{C}}^{\beta}(\Gamma))^{\varrho} = \Gamma^{\beta \circ \varrho}$.

For $\mu : p \to q$, write $\mathsf{L}^{\mu} : \widehat{\mathcal{C}}_q \to \mathcal{C}_p$ for the functor defined by $\mathsf{L}^{\mu}(\Gamma) = \Gamma^{\mu}$.

Lemma 4.5 Each $\widehat{\mathcal{C}}_p$ has $\kappa$-small limits, and each functor $\mathsf{L}^{\mu}$ and $\widehat{\mathcal{C}}^{\mu}$ preserves them. Furthermore:

(i) If each $\mathcal{C}_p$ has some shape of colimits, then so does each $\widehat{\mathcal{C}}_p$, and each $\mathsf{L}^{\mu}$ and $\widehat{\mathcal{C}}^{\mu}$ preserves them.
(ii) If each $\mathcal{C}_p$ is locally cartesian closed or an elementary topos, so is each $\widehat{\mathcal{C}}_p$.
(iii) If each $\mathcal{C}_p$ is locally presentable, and each $\mathcal{C}_{\mu}$ is accessible, then each $\widehat{\mathcal{C}}_p$ is also locally presentable.
(iv) If each $\mathcal{C}_p$ is a Grothendieck topos, and each $\mathcal{C}_{\mu}$ is an inverse or direct image, then so is each $\widehat{\mathcal{C}}_p$.

18–8

Semantics of multimodal adjoint type theory

Proof. The limits, and colimits in (i), are defined pointwise. For (ii), an oplax limit is the category of coalgebras for a finitely continuous comonad on a product category (see [42] or [19, B3.4.6]), and the stated properties are closed under products and such coalgebras (e.g. [19, A4.2.1]). For (iii), by [30, Theorem 5.1.6] accessible categories and functors are closed under limits, and an accessible category is locally presentable if and only if it is cocomplete. For (iv), we use (ii) and (iii), since Grothendieck topoi are the locally presentable elementary topoi [19, C2.2.8], and left and right adjoints are accessible. \(\square\)

Lemma 4.6 For \(\varpi : r \to s\), the functor \(\mathsf{L}^{\varpi} : \widehat{\mathcal{C}}_s \to \mathcal{C}_r\) has a right adjoint, which we write \(\mathbf{R}_{\varpi}\).

Proof. Given \(\Gamma \in \mathcal{C}_r\), we must first define \((\mathbf{R}_{\varpi}\Gamma)^{\nu} \in \mathcal{C}_p\) for any \(\nu : p \to s\). Let \((\varpi \downarrow (\nu \circ -))\) be the category of pairs \((\sigma : r \to p, \beta : \varpi \Rightarrow \nu \circ \sigma)\). Any such \((\sigma, \beta)\) induces an object \(\mathcal{C}_{\sigma}(\Gamma) \in \mathcal{C}_p\); we define

\[
(\mathbf {R} _ {\varpi} \Gamma) ^ {\nu} = \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\nu \circ -))} \mathcal {C} _ {\sigma} (\Gamma).
\]

Now suppose given also \(\varrho : p \to q\) and \(\alpha : \mu \Rightarrow \nu \circ \varrho\). Then \((\mathbf{R}_{\varpi}\Gamma)^{\alpha}\) should be a morphism

\[
(\mathbf {R} _ {\varpi} \Gamma) ^ {\nu} = \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\nu \circ -))} \mathcal {C} _ {\sigma} (\Gamma) \longrightarrow \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\mu \circ -))} \mathcal {C} _ {\varrho} \mathcal {C} _ {\sigma} (\Gamma) \stackrel {{\cong}} {{\to}} \mathcal {C} _ {\varrho} ((\mathbf {R} _ {\varpi} \Gamma) ^ {\mu}).
\]

If \((\sigma, \beta) \in (\varpi \downarrow (\mu \circ -))\) indexes a factor \(\mathcal{C}_{\varrho} \mathcal{C}_{\sigma}(\Gamma)\) of this codomain, then \((\varrho \circ \sigma, (\alpha \triangleright \sigma) \circ \beta) \in (\varpi \downarrow (\nu \circ -))\), and the factor \(\mathcal{C}_{\varrho \circ \sigma}(\Gamma)\) of the domain is isomorphic to \(\mathcal{C}_{\varrho} \mathcal{C}_{\sigma}(\Gamma)\). Thus, this determines a map \((\mathbf{R}_{\varpi} \Gamma)^{\alpha}\) between the limits. This defines \(\mathbf{R}_{\varpi} \Gamma \in \widehat{\mathcal{C}}_s\). Now we observe that

\[
(\mathbf {R} _ {\varpi} \Gamma) ^ {\varpi} = \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\varpi \circ -))} \mathcal {C} _ {\sigma} (\Gamma).
\]

Since \((1_r, 1_\varpi) \in (\varpi \downarrow (\varpi \circ -))\), with \(\mathcal{C}_{1_r}(\Gamma) \cong \Gamma\), there is a projection \(\epsilon_\Gamma : (\mathbf{R}_\varpi \Gamma)^\varpi \to \Gamma\). We claim this is a universal arrow from \(\mathsf{L}^\varpi\). For \(\Delta \in \widehat{\mathcal{C}}_s\), a map \(\theta : \Delta \to \mathbf{R}_\varpi \Gamma\) consists of, for any \(\nu : p \to r\) and any \((\sigma, \beta) \in (\varpi \downarrow (\nu \circ -))\), a morphism \(\theta^{\nu, (\sigma, \beta)} : \Delta^\nu \to \mathcal{C}_\sigma \Gamma\), such that for any \(\alpha : \mu \Rightarrow \nu \circ \varrho\) and \(\beta : \varpi \Rightarrow \mu \circ \sigma\):

\[
\begin{array}{c} \boldsymbol {\Delta} ^ {\nu} \xrightarrow {\boldsymbol {\Delta} ^ {\alpha}} \mathcal {C} _ {\varrho} (\boldsymbol {\Delta} ^ {\mu}) \\ \left( \begin{array}{c c c} \mathcal {C} _ {\varrho} (\boldsymbol {\theta} ^ {\nu}) & & \boldsymbol {\theta} ^ {\mu} \\ \downarrow & & \downarrow \\ (\mathbf {R} _ {\varpi} \Gamma) ^ {\nu} & \xrightarrow {(\mathbf {R} _ {\varpi} \Gamma) ^ {\alpha}} & \mathcal {C} _ {\varrho} ((\mathbf {R} _ {\varpi} \Gamma) ^ {\mu}) \\ \downarrow & & \downarrow \\ \mathcal {C} _ {\varrho \circ \sigma} \Gamma & \xrightarrow {\cong} & \mathcal {C} _ {\varrho} \mathcal {C} _ {\sigma} \Gamma . \end{array} \right) \boldsymbol {\theta} ^ {\mu , (\sigma , \beta)} \end{array}
\]

Taking \(\nu = \varpi\) and \(\sigma = 1_r\) with \(\beta = 1_{\varpi}\) yields the composite \(\Delta^{\varpi} \xrightarrow{\theta^{\varpi}} (\mathbf{R}_{\varpi}\Gamma)^{\varpi} \xrightarrow{\epsilon_{\Gamma}} \Gamma\). Moreover, if in the above condition we take \(\mu = \varpi\) with \((\sigma, \beta) = (1_r, 1_{\varpi})\), then the left-hand vertical composite becomes \(\theta^{\nu, (\varrho, \alpha)}\), which is fully general; thus all the components of \(\theta\) are determined by \(\theta^{\varpi, (1_r, 1_{\varpi})}\).

Now, given \(\vartheta : \Delta^{\varpi} \to \Gamma\), for any \(\nu\) and \((\sigma, \beta)\) we have a composite \(\Delta^{\nu} \xrightarrow{\Delta^{\beta}} \mathcal{C}_{\sigma}(\Delta^{\varpi}) \xrightarrow{\mathcal{C}_{\sigma}(\vartheta)} \mathcal{C}_{\sigma}\Gamma\). The above compatibility condition follows from the axioms of Definition 4.3, so we have a map \(\Delta \to \mathbf{R}_{\varpi}\Gamma\). Its underlying map \(\Delta^{\varpi} \to \Gamma\) is \(\Delta^{\varpi} \xrightarrow{\Delta^{1_{\varpi}}} \mathcal{C}_{1_r}(\Delta^{\varpi}) \xrightarrow{\mathcal{C}_{1_{\varpi}}(\vartheta)} \mathcal{C}_{1_{\varpi}}\Gamma \cong \Gamma\), which is equal to \(\vartheta\).

When \(\varpi = 1_r\), we write \(\mathsf{L}^r = \mathsf{L}^{1_r}\) and \(\mathbf{R}_r = \mathbf{R}_{1_r}\).

Lemma 4.7 The functor \(\mathbf{R}_r:\mathcal{C}_r\to \widehat{\mathcal{C}}_r\) is fully faithful.

Shulman

18-9

Proof. When $\varpi = 1_r$, the element $(1_r, 1_{1_r})$ of $(1_r \downarrow (1_r \circ -))$ is initial. Thus, the domain of $\epsilon_\Gamma$ is evaluation at that object, which is $\mathcal{C}_{1_r}(\Gamma) \cong \Gamma$. So $\epsilon$ is an isomorphism, hence $\mathbf{R}_r$ is fully faithful. $\square$

Lemma 4.8 Let $\mu : p \to r$, $\nu : q \to r$, $\varrho : p \to q$, and $\alpha : \mu \Rightarrow \nu \circ \varrho$. Then for any $\Gamma \in \mathcal{C}_p$ there is a map $\mathbf{R}_\alpha(\Gamma) : \mathbf{R}_\mu(\Gamma) \to \mathbf{R}_\nu(\mathcal{C}_\varrho\Gamma)$, which varies naturally in $\Gamma$; it is the mate of $\boldsymbol{\Delta}^\alpha : \boldsymbol{\Delta}^\nu \to \mathcal{C}_\varrho(\boldsymbol{\Delta}^\mu)$. $\square$

Lemma 4.9 For any $\varpi : r \to s$, the functor $\widehat{\mathcal{C}}^\varpi : \widehat{\mathcal{C}}_s \to \widehat{\mathcal{C}}_r$ has a right adjoint $\widehat{\mathcal{C}}_\varpi : \widehat{\mathcal{C}}_r \to \widehat{\mathcal{C}}_s$.

Proof. Let $\Gamma \in \widehat{\mathcal{C}}_s$ and $\boldsymbol{\Delta} \in \widehat{\mathcal{C}}_r$. By definition, a morphism $\boldsymbol{\theta} : \widehat{\mathcal{C}}^\varpi(\Gamma) \to \boldsymbol{\Delta}$ consists of components $\boldsymbol{\theta}^\mu : \Gamma^{\varpi \circ \mu} \to \boldsymbol{\Delta}^\mu$ for all $\mu : p \to r$ such that for any $\alpha : \mu \Rightarrow \nu \circ \varrho$ the following diagram commutes:

$$\begin{array}{c} \Gamma^{\varpi \circ \nu} \xrightarrow{\Gamma^{\varpi \circ \alpha}} \mathcal{C}_\varrho(\Gamma^{\varpi \circ \mu}) \\ \boldsymbol{\theta}^\nu \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \boldsymbol{\Delta}^\mu \xrightarrow{\boldsymbol{\Delta}^\alpha} \mathcal{C}_\varrho(\boldsymbol{\Delta}^\mu) \end{array} \tag{4.10}$$

To give $\boldsymbol{\theta}^\mu$ is equivalent to give $\overline{\boldsymbol{\theta}^\mu} : \Gamma \to \mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\Delta}^\mu)$. We will define $\widehat{\mathcal{C}}_\varpi(\boldsymbol{\Delta}) \in \widehat{\mathcal{C}}_s$ as the limit of a diagram of objects $\mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\Delta}^\mu)$, so that a map $\Gamma \to \widehat{\mathcal{C}}_\varpi(\boldsymbol{\Delta})$ is determined by maps $\overline{\boldsymbol{\theta}^\mu}$ satisfying a cone condition that is equivalent to (4.10). We start by writing down the naturality square for the transformation $\mathbf{R}_{\varpi \circ \alpha}$ of Lemma 4.8 at $\boldsymbol{\theta}^\mu$, and composing it with the adjunction unit $\Gamma \to \mathbf{R}_{\varpi \circ \mu}(\Gamma^{\varpi \circ \mu})$:

$$\begin{array}{c} \Gamma \xrightarrow{} \mathbf{R}_{\varpi \circ \mu}(\Gamma^{\varpi \circ \mu}) \xrightarrow{\mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\theta}^\mu)} \mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\Delta}^\mu) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\Gamma^{\varpi \circ \mu})) \xrightarrow[\mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\boldsymbol{\theta}^\mu))]{} \mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\boldsymbol{\Delta}^\mu)) \end{array} \tag{4.11}$$

We also transpose (4.10) across $\mathsf{L}^{\varpi \circ \nu} \dashv \mathbf{R}_{\varpi \circ \nu}$ to obtain an equivalent condition as at left below:

$$\begin{array}{ccc} \Gamma & \longrightarrow & \mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\Gamma^{\varpi \circ \mu})) \\ \downarrow & & \downarrow \\ \mathbf{R}_{\varpi \circ \nu}(\boldsymbol{\Delta}^\nu) & \longrightarrow & \mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\boldsymbol{\Delta}^\mu)) \end{array} \qquad \begin{array}{c} \Gamma \xrightarrow{\overline{\boldsymbol{\theta}}^\nu} \mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\Delta}^\mu) \\ \overline{\boldsymbol{\theta}}^\nu \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf{R}_{\varpi \circ \nu}(\boldsymbol{\Delta}^\nu) & \longrightarrow & \mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\boldsymbol{\Delta}^\mu)) \end{array} \tag{4.12}$$

The left-bottom composite in (4.11) is equal to the top-right composite at left in (4.12). Thus, we can replace this part of the square at left in (4.12) by the top-right composite in (4.11) to obtain the equivalent condition at right in (4.12). Now we define $\widehat{\mathcal{C}}_\varpi(\boldsymbol{\Delta})$ to be the limit in $\widehat{\mathcal{C}}_s$ of the diagram consisting of the objects $\mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\Delta}^\mu)$, for all $\mu : p \to r$, and the cospans $\mathbf{R}_{\varpi \circ \nu}(\boldsymbol{\Delta}^\nu) \to \mathbf{R}_{\varpi \circ \nu}(\mathcal{C}_\varrho(\boldsymbol{\Delta}^\mu)) \leftarrow \mathbf{R}_{\varpi \circ \mu}(\boldsymbol{\Delta}^\mu)$ for all $\alpha : \mu \Rightarrow \nu \circ \varrho$. Then $\Gamma \to \widehat{\mathcal{C}}_\varpi(\boldsymbol{\Delta})$ consists of $\overline{\boldsymbol{\theta}^\mu}$ satisfying (4.12), hence maps $\boldsymbol{\theta}^\mu$ satisfying (4.10). $\square$

Corollary 4.13 We have a 2-functor $\widehat{\mathcal{C}} : \mathcal{L}[\mathcal{L}^\dagger]^{\mathrm{coop}} \to \mathcal{C}at$, with $\widehat{\mathcal{C}}^{\mu\dagger} = \widehat{\mathcal{C}}_\mu$. In particular, considering only the right adjoints, we have a pseudofunctor $\widehat{\mathcal{C}} : \mathcal{L} \to \mathcal{C}at$. $\square$

We call this pseudofunctor $\widehat{\mathcal{C}}$ the co-dextrification of $\mathcal{C}$.

Lemma 4.14 The functors $\mathsf{L}^r : \widehat{\mathcal{C}}_r \to \mathcal{C}_r$ are a pseudonatural transformation of pseudofunctors $\mathcal{L} \to \mathcal{C}at$.

Proof. Let $\varpi : r \to s$ and $\Gamma \in \widehat{\mathcal{C}}_r$; we must show that $\widehat{\mathcal{C}}_\varpi(\Gamma)^{1_s} \cong \mathcal{C}_\varpi(\Gamma^{1_s})$. Since $\mathsf{L}^s = \mathsf{L}^{1_s}$ preserves $\kappa$-small limits, $\widehat{\mathcal{C}}_\varpi(\Gamma)^{1_s}$ is the limit of the diagram consisting of the objects $(\mathbf{R}_{\varpi \circ \mu}(\Gamma^\mu))^{1_s}$, for all $\mu : p \to r$, and the analogous cospans. And by definition of $\mathbf{R}_{\varpi \circ \mu}$, each of these objects is the limit

$$(\mathbf{R}_{\varpi \circ \mu}(\Gamma^\mu))^{1_s} = \lim_{(\sigma, \beta) \in ((\varpi \circ \mu) \downarrow (1_s \circ -))} \mathcal{C}_\sigma(\Gamma^\mu).$$

18–10

Semantics of multimodal adjoint type theory

But $$((\varpi \circ \mu) \downarrow (1_s \circ -))$$ has an initial object $$(\varpi \circ \mu, 1_{\varpi \circ \mu})$$, so this limit is isomorphic to $$\mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$. A similar argument applies to the apices of the cospans, so $$\widehat{\mathcal{C}}_{\varpi}(\mathbf{\Gamma})^{1_s}$$ is the limit of the diagram consisting of the objects $$\mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$, for all $$\mu : p \to r$$, and the cospans $$\mathcal{C}_{\varpi \circ \nu}(\mathbf{\Gamma}^\nu) \to \mathcal{C}_{\varpi \circ \nu \circ \varrho}(\mathbf{\Gamma}^\mu) \leftarrow \mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$ for all $$\alpha : \mu \Rightarrow \nu \circ \varrho$$. However, there is a canonical such object where $$\mu = 1_r$$, and for any other $$\mu$$ the 2-cell $$1_\mu : \mu \Rightarrow 1_r \circ \mu$$ determines a canonical cospan $$\mathcal{C}_{\varpi}(\mathbf{\Gamma}^{1_s}) \to \mathcal{C}_{\varpi \circ 1_r \circ \mu}(\mathbf{\Gamma}^\mu) \xleftarrow{\approx} \mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$ in which the right-hand leg is an identity. Thus, the limit of this diagram is isomorphic to $$\mathcal{C}_{\varpi}(\mathbf{\Gamma}^{1_s})$$.

**Lemma 4.15** *The functors $$\mathbf{R}_r : \mathcal{C}_r \to \widehat{\mathcal{C}}_r$$ are lax natural, by doctrinal adjunction [20].*

## 5 MATT in the co-dextrification

We now show that for suitable $$\mathcal{C}$$, the co-dextrification $$\widehat{\mathcal{C}}$$ models MATT over $$\mathcal{L}[\mathcal{S}^\dagger]$$ (recall Assumption 2.4). In fact, we use only its abstract properties; this makes our arguments cleaner and more general.

### 5.1 Adjoint modal pre-models

Recall that a **natural pseudo-model** [39, Appendix A] is a strict natural transformation $$\tau : \mathrm{Tm} \to \mathrm{Ty}$$ between groupoid-valued pseudofunctors $$\mathrm{Tm}, \mathrm{Ty} : \mathcal{D}^{\mathrm{op}} \to \mathcal{G}pd$$ that has discrete fibers and is representable.

**Definition 5.1** Let $$\mathcal{L}$$ be a 2-category with a class $$\mathcal{S}$$ of morphisms. An **adjoint modal pre-model** is:

- (i) A modal context structure $$\widehat{\mathcal{C}} : \mathcal{L}[\mathcal{L}^\dagger]^{\mathrm{coop}} \to \mathcal{C}at$$, such that each $$\widehat{\mathcal{C}}_p$$ is locally cartesian closed. As before, we write its action on morphisms as $$\widehat{\mathcal{C}}^\mu$$, and we write $$\widehat{\mathcal{C}}_\mu = \widehat{\mathcal{C}}^{\mu^\dagger}$$.
- (ii) A pseudofunctor $$\mathcal{C} : \mathcal{L}[\mathcal{S}^\dagger] \to \mathcal{C}at$$, with action on morphisms $$\mathcal{C}_\mu$$.
- (iii) A pseudonatural transformation $$\mathsf{L} : \widehat{\mathcal{C}} \to \mathcal{C}$$ between pseudofunctors $$\mathcal{L} \to \mathcal{C}at$$. To be covariant on $$\mathcal{L}$$, we take the right adjoints in $$\widehat{\mathcal{C}}$$ but the left adjoints in $$\mathcal{C}$$; thus $$\mathcal{C}_\mu(\mathsf{L}^p(\Gamma)) \cong \mathsf{L}^q(\widehat{\mathcal{C}}_\mu(\Gamma))$$.
- (iv) Each functor $$\mathsf{L}^p : \widehat{\mathcal{C}}_p \to \mathcal{C}_p$$ preserves finite limits and has a fully faithful right adjoint $$\mathsf{R}_p$$.
- (v) Each category $$\mathcal{C}_p$$ is a natural pseudo-model $$(\mathcal{C}_p, \tau_p)$$.

**Example 5.2** If $$\mathcal{C} : \mathcal{L} \to \mathcal{C}at$$ is a pseudofunctor such that each $$\mathcal{C}_p$$ is locally cartesian closed with $$\kappa$$-small limits, each functor $$\mathcal{C}_\mu$$ preserves $$\kappa$$-small limits, and $$\mathcal{C}_\mu$$ has a right adjoint if $$\mu \in \mathcal{S}$$, then the co-dextrification $$\widehat{\mathcal{C}}$$ extends it to an adjoint modal pre-model.

**Remark 5.3** If each $$\mathsf{L}^p$$ is an identity, then Definition 5.1 is just a modal context structure $$\widehat{\mathcal{C}} : \mathcal{L}[\mathcal{L}^\dagger]^{\mathrm{coop}} \to \mathcal{C}at$$ consisting of locally cartesian closed natural pseudo-models such that $$\widehat{\mathcal{C}}_\mu$$ has a right adjoint when $$\mu \in \mathcal{S}$$. In this case, the results we will prove in this section specialize to a more ordinary version of [29] for the modal case, when the lock functors already exist but we need to strictly the type formers.

**Lemma 5.4** *In an adjoint modal pre-model, if $$A \xrightarrow{f} B \xrightarrow{g} C$$ are morphisms such that $$f$$ is a pullback of a map in the image of $$\mathsf{R}_p$$, then the pushforward $$g_*(f)$$ is also a pullback of a map in the image of $$\mathsf{R}_p$$.*

**Proof.** The pullbacks of maps in the image of $$\mathsf{R}_p$$ are a left-exact-reflective subcategory of $$\widehat{\mathcal{C}}_p/C$$; the reflection $$\mathsf{L}^{f/C}$$ applies $$\mathsf{L}^p$$ and pulls back to $$C$$. For any $$h : D \to C$$, morphisms $$h \to g_*(f)$$ in $$\widehat{\mathcal{C}}_p/C$$ are equivalent to morphisms $$g^*(h) \to f$$ in $$\widehat{\mathcal{C}}_p/B$$. By assumption on $$f$$, any such morphism factors through $$\mathsf{L}^{f/B}(g^*(h))$$, which is $$g^*(\mathsf{L}^{f/C}(h))$$ by left-exactness of $$\mathsf{L}^p$$. Thus, it also corresponds to a map $$\mathsf{L}^{f/C}(h) \to g_*(f)$$. Taking $$h = g_*(f)$$ we conclude that $$g_*(f) \cong \mathsf{L}^{f/C}(g_*(f))$$ and hence lies in the subcategory. $$\square$$

### 5.2 The left adjoint splitting

The **left adjoint splitting** [29] of a natural pseudo-model $$(\mathcal{D}, \tau)$$ is $$\tau^! : \mathrm{Tm}^! \to \mathrm{Ty}^!$$ where:

- An element $$A \in \mathrm{Ty}^!(\Gamma)$$ consists of an object $$\mathsf{V}_A \in \mathcal{D}$$, a type $$\mathsf{E}_A \in \mathrm{Ty}(\mathsf{V}_A)$$, and a morphism $${}^r A^! : \Gamma \to \mathsf{V}_A$$. We call $$\mathsf{V}_A$$ the *local universe*.

Shulman

18–11

- An element \((A, a) \in \mathrm{Tm}^!(\Gamma)\) consists of \(\mathsf{V}_A \in \mathcal{D}\), a type \(\mathsf{E}_A \in \mathrm{Ty}(\mathsf{V}_A)\), and \(a: \Gamma \to \mathsf{V}_A \triangleright \mathsf{E}_A\).
- The map \(\tau^{!}\) sends \(a\) to \({}^{r}A^{!} = \mathfrak{p}_{A} \circ a\).

Since \(\tau^!\) is the pullback of \(\tau\) along the map \(\mathrm{Ty}^! \to \mathrm{Ty}\) sending \(A\) to \(\mathsf{E}_A[\mathsf{A}']\), it is a natural model.

Given an adjoint modal pre-model, we define \(\widehat{\tau}_p^! = (\mathsf{L}^p)^*\tau_p^!\). Thus, an element \(A \in \widehat{\mathrm{Ty}}_p^!(\Gamma)\) consists of an object \(\mathsf{V}_A \in \mathcal{C}_p\), a type \(\mathsf{E}_A \in \mathrm{Ty}_p(\mathsf{V}_A)\), and a morphism \(^r A^! : \mathsf{L}^p\Gamma \to \mathsf{V}_A\), or equivalently \(^r A^! : \Gamma \to \mathsf{R}_p\mathsf{V}_A\).

Lemma 5.5 If \((\widehat{\mathcal{C}},\mathcal{C})\) is an adjoint modal pre-model over \((\mathcal{L},\mathcal{S})\), then \((\widehat{\mathcal{C}},\widehat{\tau}')\) is an adjoint modal natural model over \(\mathcal{L}[\mathcal{S}^{\dagger}]\).

Proof. The tangible morphisms in \(\mathcal{L}[\mathcal{S}^{\dagger}]\) are \(\mu \circ \nu^{\dagger}\), for \(\mu : q \to r\) in \(\mathcal{L}\) and \(\nu : q \to p\) in \(\mathcal{S}\). Thus, we must show that in this case \((\widehat{\mathcal{C}}_{\nu} \circ \widehat{\mathcal{C}}^{\mu})^{*}\widehat{\tau}_{p}^{!} = (\mathsf{L}^{p} \circ \widehat{\mathcal{C}}_{\nu} \circ \widehat{\mathcal{C}}^{\mu})^{*}\tau_{p}^{!}\) is representable. But by pseudonaturality of \(\mathsf{L}\), we have \(\mathsf{L}^{p} \circ \widehat{\mathcal{C}}_{\nu} \circ \widehat{\mathcal{C}}^{\mu} \cong \mathcal{C}_{\nu} \circ \mathsf{L}^{q} \circ \widehat{\mathcal{C}}^{\mu}\), and this has a right adjoint \(\widehat{\mathcal{C}}_{\mu} \circ \mathsf{R}_{q} \circ \mathcal{C}_{\nu^{\dagger}}\). Finally, restriction along any functor with a right adjoint preserves representability.

Explicitly, the comprehension \(\Gamma \triangleright^{\mu \circ \nu^{\dagger}}A\) is the pullback

\[
\begin{array}{c} \Gamma \triangleright^ {\mu \circ \nu^ {\dagger}} A \xrightarrow {} \widehat {\mathcal {C}} _ {\mu} R _ {q} \mathcal {C} _ {\nu^ {\dagger}} (V _ {A} \triangleright E _ {A}) \\ \widehat {\mathfrak {p}} _ {A} \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \\ \Gamma \xrightarrow {} \widehat {\mathcal {C}} _ {\mu} R _ {q} \mathcal {C} _ {\nu^ {\dagger}} \mathcal {C} _ {\nu} L ^ {q} \widehat {\mathcal {C}} ^ {\mu} (\Gamma) \xrightarrow [ r _ {A} ]{} \widehat {\mathcal {C}} _ {\mu} R _ {q} \mathcal {C} _ {\nu^ {\dagger}} V _ {A}. \end{array} \tag {5.6}
\]

Theorem-Schema 5.7 If \((\widehat{\mathcal{C}},\mathcal{C})\) is an adjoint modal pre-model, then for any of the type constructors considered in [29], if \((\mathcal{C},\tau)\) has weakly stable structure, then \((\widehat{\mathcal{C}},\widehat{\tau}')\) has strictly stable structure.

Proof. Since  \( L^{p} \)  preserves finite limits, any weakly stable or pseudo-stable structure on  \( \tau_{p} \)  lifts to  \( (\mathsf{L}^{p})^{*}\tau_{p} \) . Therefore, by [29],  \( ((\mathsf{L}^{p})^{*}\tau_{p})^{!} \)  has strictly stable structure. If we identify  \( C_{p} \)  with the image of  \( R_{p} \) , then  \( \widehat{\mathrm{Ty}}^{!}\subseteq((\mathsf{L}^{p})^{*}\mathrm{Ty}_{p})^{!} \)  consists of the types whose local universes lie in  \( C_{p} \) . By Lemma 5.4,  \( C_{p} \)  is closed under all the local universe manipulations of [29]; hence  \( \widehat{\tau}^{!} \)  is closed under the strictly stable structure. □

For the modal type formers, the “weakly stable” structure exists on C alone; thus we name its structure.

Definition 5.8 A modal pre-model over an adjoint mode theory \(\mathcal{M}\) is a pseudofunctor \(\mathcal{C}:\mathcal{M}\to \mathcal{C}at\) such that each \(\mathcal{C}_p\) is a natural pseudo-model.

### 5.3 \(\Pi\)-structure

Definition 5.9 A morphism \(\delta : \Gamma \to \Delta\) in a natural pseudo-model is type-exponentiable if for any \(B \in \mathrm{Ty}(\Gamma)\), the pushforward of \(\Gamma \triangleright B\) along \(\delta\) is isomorphic to a type projection \(\Delta \triangleright \Pi(f, B) \to \Delta\).

Definition 5.10 A modal pre-model \(\mathcal{C}\) has pre-\(\Pi\)-structure if for any sharp \(\mu : p \to q\) in \(\mathcal{M}\) and any \(\Gamma \in \mathcal{C}_p\) and \(A \in \mathrm{Ty}_p(\Gamma)\), any pullback of \(\mathcal{C}_{\mu} \mathfrak{p}_A : \mathcal{C}_{\mu}(\Gamma \triangleright A) \to \mathcal{C}_{\mu} \Gamma\) is type-exponentiable.

Lemma 5.11 Let \(\mathsf{L}:\mathcal{A}\rightleftarrows\mathcal{B}:\mathsf{R}\) be an adjunction where \(\mathsf{L}\) preserves pullbacks. Let \(f:A\to B\) be in \(\mathcal{A}\), \(g:C\to \mathsf{L}A\) in \(\mathcal{B}\), and suppose that the pushforward \((\mathsf{L}f)_{*}g:(\mathsf{L}f)_{*}C\to \mathsf{L}B\) of \(g\) along \(\mathsf{L}f\) exists in \(\mathcal{B}\). Then the pullback of \(\mathsf{R}((\mathsf{L}f)_{*}C)\) to \(B\) is a pushforward along \(f\) of the pullback of \(\mathsf{R}g\) to \(B\).

Proof. This is a fairly straightforward diagram chase.

□

Theorem 5.12 If \((\widehat{\mathcal{C}},\mathcal{C})\) is an adjoint modal pre-model over \((\mathcal{L},\mathcal{S})\) such that \(\mathcal{C}\) has pre-\(\Pi\)-structure over \(\mathcal{L}[\mathcal{S}^{\dagger}]\), then \((\widehat{\mathcal{C}},\widehat{\tau}^{\dagger})\) has \(\Pi\)-structure over \(\mathcal{L}[\mathcal{S}^{\dagger}]\).

18–12

Semantics of multimodal adjoint type theory

Proof. Suppose we have \(\mu : q \to r\) in \(\mathcal{L}\) and \(\nu : q \to p\) in \(\mathcal{S}\), and also \(\Gamma \in \widehat{\mathcal{C}}_r\) and \(A \in \widehat{\mathrm{Ty}}_p^! (\widehat{\mathcal{C}}_\nu \widehat{\mathcal{C}}^\mu \Gamma) = \mathrm{Ty}_p(\mathsf{L}^p \widehat{\mathcal{C}}_\nu \widehat{\mathcal{C}}^\mu \Gamma)\) with \(B \in \widehat{\mathrm{Ty}}_r^! (\Gamma \triangleright^{\mu \circ \nu^\dagger} A) = \mathrm{Ty}_r(\mathsf{L}^r (\Gamma \triangleright^{\mu \circ \nu^\dagger} A))\). Applying \(\mathsf{L}^r\) to the defining pullback (5.6) of \(\Gamma \triangleright^{\mu \circ \nu^\dagger} A\), and using pseudonaturality and the fact that \(\mathsf{L}^q \mathsf{R}_q \cong 1\), we have a pullback

\[
\begin{array}{c} \mathsf {L} ^ {r} (\Gamma \triangleright^ {\mu \circ \nu^ {\dagger}} A) \longrightarrow \mathscr {C} _ {\mu} \mathscr {C} _ {\nu^ {\dagger}} (\mathsf {V} _ {A} \triangleright \mathsf {E} _ {A}) \\ \mathsf {L} ^ {r} (\widehat {\mathfrak {p}} _ {A}) \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \end{array} \tag {5.13}
\]

Thus, Definition 5.10 says \(\mathsf{L}^r (\widehat{\mathfrak{p}}_A)\) is type-exponentiable, hence the pushforward of \(B\) along it is a type projection; it remains to construct a local universe making it strictly stable. Let \(\mathsf{V}_{\Pi (A,B)}\) be the universal object with maps \(\pi_A:\mathsf{V}_{\Pi (A,B)}\to \mathcal{C}_\omega (\mathsf{V}_A)\) and \(\pi_B:\pi_A^* (\mathcal{C}_\omega (\mathsf{V}_A\triangleright \mathsf{E}_A))\to \mathsf{V}_B\). By Definition 5.10, \(\pi_A^* (\mathcal{C}_\omega (\mathsf{p}_{\mathsf{E}_A}))\) is type-exponentiable, so the pushforward of \(\mathsf{E}_B[\pi_B]\in \mathrm{Ty}_q(\pi_A^* (\mathcal{C}_\omega (\mathsf{V}_A\triangleright \mathsf{E}_A)))\) along it is represented by a type \(\mathsf{E}_{\Pi (A,B)}\in \mathrm{Ty}_q(\mathsf{V}_{\Pi (A,B)})\). Now the bottom map in (5.13) and \(B':\mathsf{L}^q (\Gamma \triangleright^\omega A)\to \mathsf{V}_B\) induce a map \(\Pi (A,B):\mathsf{L}^q\Gamma \to \mathsf{V}_{\Pi (A,B)}\). Together, these data define \(\Pi (A,B)\in \widehat{\mathrm{Ty}}_p^!\) (\(\Gamma\)), such that \(\mathsf{L}^p\Gamma \triangleright \mathsf{E}_{\Pi (A,B)}[\Pi (A,B)]\) is a pushforward of \(\mathsf{L}^q (\Gamma \triangleright^\omega A)\triangleright \mathsf{E}_B[\Pi ']\) along \(\mathsf{L}^q (\Gamma \triangleright^\omega A)\to \mathsf{L}^q\Gamma\). The comprehension \(\Gamma \triangleright \Pi (A,B)\) in \(\widehat{\mathcal{C}}_q\) is defined by applying \(\mathsf{R}_q\) to this and pulling back along the unit \(\Gamma \to \mathsf{R}_q\mathsf{L}^q\Gamma\). Thus, Lemma 5.11 implies the desired universal property of \(\Pi (A,B)\).

### 5.4 Positive modalities

Definition 5.14 In a natural pseudo-model, a map \( f: \Gamma \to \Delta \) is anodyne if for any \( B \in \mathrm{Ty}(\Delta) \) and any \( g: \Gamma \to \Delta \triangleright B \) lifting \( f \), there exists a diagonal filler:

\[
\begin{array}{c} \Gamma \xrightarrow {g} \Delta \triangleright B \\ f \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \end{array}
\]

A map is stably anodyne if any pullback of it is anodyne.

Definition 5.15 A modal pre-model \(\mathcal{C}\) has positive pre-modalities if for any sharp \(\mu : p \to q\) and \(\Gamma \in \mathcal{C}_p\) with \(A \in \mathrm{Ty}_p(\Gamma)\), there exists \(\mu \square A \in \mathrm{Ty}_q(\mathcal{C}_\mu \Gamma)\) and a map \(i_{\Gamma, A}^\mu : \mathcal{C}_\mu (\Gamma \triangleright A) \to \mathcal{C}_\mu \Gamma \triangleright (\mu \square A)\) over \(\mathcal{C}_\mu \Gamma\). such that for any transparent \(\varrho : q \to r\), the map \(\mathcal{C}_{\varrho}(i_{\Delta, A}^\mu)\) is stably anodyne.

Lemma 5.16 In an adjoint modal pre-model, let \(\theta : \Gamma \to \Delta\) be a map in \(\widehat{\mathcal{C}}_p\). If \(\mathsf{L}^p\theta\) is anodyne in \(\mathcal{C}_p\), then \(\theta\) is anodyne in \(\widehat{\mathcal{C}}_p\).

Proof. Suppose given \( B \in \widehat{\mathrm{Ty}}_p^!(\Delta) = \mathrm{Ty}_p^!(\mathsf{L}^p\Delta) \), and a commutative square as at left below.

\[
\begin{array}{c} \Gamma \longrightarrow \Delta \triangleright B \longrightarrow R _ {p} (V _ {B} \triangleright E _ {B}) \\ \theta \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \Delta \xlongequal {} \Delta \xrightarrow {r _ {B ^ {\prime}}} R _ {p} V _ {B} \end{array}
\]

\[
\begin{array}{c} \mathsf {L} ^ {p} \Gamma \longrightarrow \mathsf {V} _ {B} \triangleright \mathsf {E} _ {B} \\ \mathsf {L} ^ {p} \theta \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \mathsf {L} ^ {p} \Delta \xrightarrow {r _ {B ^ {\prime}}} \mathsf {V} _ {B} \end{array}
\]

It suffices to find a filler for the outer rectangle at left above; and by adjunction, this is equivalent to finding a filler in the square at right above. But such a filler exists precisely because  \( L^{p}\theta \)  is anodyne. ☐

Shulman

18–13

**Theorem 5.17** If $(\widehat{\mathcal{C}}, \mathcal{C})$ is an adjoint modal pre-model over $(\mathcal{L}, \mathcal{S})$ such that $\mathcal{C}$ has positive pre-modalities over $\mathcal{L}[\mathcal{S}^{\dagger}]$, then $(\widehat{\mathcal{C}}, \widehat{\tau}^{\dagger})$ has positive modalities over $\mathcal{L}[\mathcal{S}^{\dagger}]$.

**Proof.** The sharp morphisms in $\mathcal{L}[\mathcal{S}^{\dagger}]$ are $\mu \circ \nu^{\dagger}$, where $\mu : q \to r$ is in $\mathcal{L}$ and $\nu : q \to p$ is in $\mathcal{S}$. Suppose given these and also $\Gamma \in \widehat{\mathcal{C}}_r$ and $A \in \widehat{\mathrm{Ty}}_p!(\widehat{\mathcal{C}}^{\mu \circ \nu^{\dagger}}\Gamma) = \mathrm{Ty}_p!(\mathrm{L}^p(\widehat{\mathcal{C}}^{\mu \circ \nu^{\dagger}}\Gamma))$, hence $\mathsf{E}_A \in \mathrm{Ty}_p(\mathsf{V}_A)$ with $^\prime A' : \mathrm{L}^p\widehat{\mathcal{C}}^{\mu \circ \nu^{\dagger}}(\Gamma) \to \mathsf{V}_A$. By Definition 5.15, we have $(\mu \circ \nu^{\dagger})\square\mathsf{E}_E \in \mathrm{Ty}_q(\mathcal{C}_\mu\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A)$ and $i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}} : \mathcal{C}_\mu\mathcal{C}_{\nu^{\dagger}}(\mathsf{V}_A \triangleright \mathsf{E}_A) \to \mathcal{C}_\mu\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A \triangleright ((\mu \circ \nu^{\dagger})\square\mathsf{E}_A)$ over $\mathcal{C}_\mu\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A$, such that $\mathcal{C}_\varrho(i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}})$ is stably anodyne for any transparent $\varrho$. We define $\mathsf{V}_{(\mu \circ \nu^{\dagger})\square A} = \mathcal{C}_\mu\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A$ and $\mathsf{E}_{(\mu \circ \nu^{\dagger})\square A} = (\mu \circ \nu^{\dagger})\square\mathsf{E}_E$.

Now $^\prime A' : \mathrm{L}^p\widehat{\mathcal{C}}^{\mu \circ \nu^{\dagger}}(\Gamma) \cong \mathrm{L}^p\widehat{\mathcal{C}}_\nu\widehat{\mathcal{C}}^\mu(\Gamma) \cong \mathcal{C}_\nu\mathrm{L}^q\widehat{\mathcal{C}}^\mu\Gamma \to \mathsf{V}_A$ has an adjunct $\Gamma \to \widehat{\mathcal{C}}_\mu\mathsf{R}_q\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A$ (which we will sometimes denote also by $^\prime A'$). Composing this with the lax naturality constraint of $\mathsf{R}$, we get

$$\Gamma \xrightarrow{^\prime A'} \widehat{\mathcal{C}}_\mu\mathsf{R}_q\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A \xrightarrow{\mathsf{R}_\mu} \mathsf{R}_r\mathcal{C}_\mu\mathcal{C}_{\nu^{\dagger}}\mathsf{V}_A = \mathsf{R}_r\mathsf{V}_{(\mu \circ \nu^{\dagger})\square A},$$

whose adjunct $\mathrm{L}^r\Gamma \to \mathsf{V}_{(\mu \circ \nu^{\dagger})\square A}$ we take as $^\prime(\mu \circ \nu^{\dagger})\square A'$. Finally, we define $j_{\Gamma,A}^{\mu \circ \nu^{\dagger}}$ to make the diagram in Figure 7a commute. This uses the universal property of the front rectangle as a pullback. Since $i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}}$ is fixed along with the local universe, this definition of $j$ is strictly stable. This completes Definition 3.4(i).

Note that the left-hand square in back above is also a pullback (defining $\Gamma \triangleright^{\mu \circ \nu^{\dagger}} A$), but the right-hand one is not: it is naturality of the lax constraint for $\mathsf{R}$. However, since $\mathrm{L}^r$ inverts this constraint, that square also becomes a pullback upon application of $\mathrm{L}^r$. Thus, $\mathrm{L}^r(j_{\Gamma,A}^{\mu \circ \nu^{\dagger}})$ is a pullback of $i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}}$.

For (ii) of Definition 3.4, let $\varrho : r \to s$ be in $\mathcal{L}$ (hence transparent in $\mathcal{L}[\mathcal{S}^{\dagger}]$), and suppose we have $A \in \mathrm{Ty}_p(\widehat{\mathcal{C}}^{\varrho \circ \mu \circ \nu^{\dagger}}(\Gamma))$. (Thus, the $\Gamma$ in the preceding proof of part (i) is now $\widehat{\mathcal{C}}^{\varrho}(\Gamma)$.) We first observe that in an adjoint modal pre-model, the construction of $\ell$ in Definition 3.4 is equivalent to the diagram in Figure 7b, in which the map $k$ and the square $(*)$ are defined by the diagram in Figure 7c. Then $(*)$ is a pullback, so $\ell$ is a pullback of $\widehat{\mathcal{C}}_\varrho(j_{\widehat{\mathcal{C}}^{\varrho}(\Gamma),A}^{\mu \circ \nu^{\dagger}})$. Hence $\mathrm{L}^s(\ell)$ is a pullback of $\mathrm{L}^s\widehat{\mathcal{C}}_\varrho(j_{\widehat{\mathcal{C}}^{\varrho}(\Gamma),A}^{\mu \circ \nu^{\dagger}})$, which is isomorphic to $\mathcal{C}_\varrho\mathrm{L}^r(j_{\widehat{\mathcal{C}}^{\varrho}(\Gamma),A}^{\mu \circ \nu^{\dagger}})$. But we observed that $\mathrm{L}^r(j_{\widehat{\mathcal{C}}^{\varrho}(\Gamma),A}^{\mu \circ \nu^{\dagger}})$ is a pullback of $i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}}$; thus $\mathrm{L}^s(\ell)$ is also a pullback of $\mathcal{C}_\varrho(i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}})$. By Definition 5.15, $\mathcal{C}_\varrho(i_{\mathsf{V}_A,\mathsf{E}_A}^{\mu \circ \nu^{\dagger}})$ is stably anodyne; hence $\mathrm{L}^s(\ell)$ is anodyne. Thus the fillers required by (ii) exist; we make them strictly stable as in [29, Lemmas 3.4.1.4 and 3.4.3.2]. $\square$

### 5.5 Negative modalities

**Definition 5.18** A modal pre-model $\mathcal{C}$ has **negative pre-modalities** if for any *sinister* $\mu : p \to q$, and $\Gamma \in \mathcal{C}_q$ with $A \in \mathrm{Ty}_q(\Gamma)$, we have $\mu \diamond \to A \in \mathrm{Ty}_p(\mathcal{C}_{\mu^{\dagger}}\Gamma)$ such that $\mathcal{C}_{\mu^{\dagger}}\Gamma \triangleright (\mu \diamond \to A) \cong \mathcal{C}_{\mu^{\dagger}}(\Gamma \triangleright A)$ over $\mathcal{C}_{\mu^{\dagger}}\Gamma$.

**Theorem 5.19** If $(\widehat{\mathcal{C}}, \mathcal{C})$ is an adjoint modal pre-model over $(\mathcal{L}, \mathcal{S})$ such that $\mathcal{C}$ has negative pre-modalities over $\mathcal{L}[\mathcal{S}^{\dagger}]$, then $(\widehat{\mathcal{C}}, \widehat{\tau}^{\dagger})$ has negative modalities over $\mathcal{L}[\mathcal{S}^{\dagger}]$.

**Proof.** Let $\mu : p \to q$ be in $\mathcal{S}$, and $\Gamma \in \widehat{\mathcal{C}}_p$ with $A \in \widehat{\mathrm{Ty}}_q!(\widehat{\mathcal{C}}_\mu\Gamma) = \mathrm{Ty}_q!(\mathrm{L}^q\widehat{\mathcal{C}}_\mu\Gamma)$. Thus, we have $\mathsf{E}_A \in \mathrm{Ty}_q(\mathsf{V}_A)$ and $^\prime A' : \mathcal{C}_\mu\mathrm{L}^p\Gamma \cong \mathrm{L}^q\widehat{\mathcal{C}}_\mu\Gamma \to \mathsf{V}_A$. By assumption, we have $\mu \diamond \to \mathsf{E}_A \in \mathrm{Ty}_p(\mathcal{C}_{\mu^{\dagger}}\mathsf{V}_A)$ and $\mathcal{C}_{\mu^{\dagger}}\mathsf{V}_A \triangleright (\mu \diamond \to \mathsf{E}_A) \cong \mathcal{C}_{\mu^{\dagger}}(\mathsf{V}_A \triangleright \mathsf{E}_A)$ over $\mathcal{C}_{\mu^{\dagger}}\mathsf{V}_A$. We define $\mathsf{V}_{\mu \diamond \to A} = \mathcal{C}_{\mu^{\dagger}}\mathsf{V}_A$ and $\mathsf{E}_{\mu \diamond \to A} = \mu \diamond \to \mathsf{E}_A$, and let $^\prime \mu \diamond \to A' : \mathrm{L}^p\Gamma \to \mathcal{C}_{\mu^{\dagger}}\mathsf{V}_A$ be the adjunct of $^\prime A'$ under $\mathcal{C}_\mu \dashv \mathcal{C}_{\mu^{\dagger}}$. This defines $\mu \diamond \to A \in \widehat{\mathrm{Ty}}_p!(\Gamma)$; we must

18–14

Semantics of multimodal adjoint type theory

![img-0.jpeg](img-0.jpeg)

(a) Introduction rule

![img-1.jpeg](img-1.jpeg)

(b) Elimination rule, part 1

![img-2.jpeg](img-2.jpeg)

(c) Elimination rule, part 2

Fig. 7. Positive modalities in an adjoint modal pre-model

show \(\Gamma \triangleright (\mu \diamondsuit \rightarrow A) \cong \Gamma \triangleright^{\mu_*} A\). Now \(\Gamma \triangleright (\mu \diamondsuit \rightarrow A)\) is defined by the pullback square at left below:

![img-3.jpeg](img-3.jpeg)

Composing with the isomorphism on the right, we obtain the defining pullback of \(\Gamma \triangleright^{\mu_*} A\) as in (5.6).

## 6 Diagrams of 1-topoi

Combining Theorems 5.12, 5.17 and 5.19, we have the following. (Recall Assumption 2.4.)

Shulman

18–15

**Theorem 6.1** Let $\mathcal{L}$ be a 2-category with a class of morphisms $\mathcal{S}$. If an adjoint modal pre-model $(\widehat{\mathcal{C}}, \mathcal{C})$ over $(\mathcal{L}, \mathcal{S})$ is such that $\mathcal{C}$ has pre-$\Pi$-structure, positive pre-modalities, and negative pre-modalities over $\mathcal{L}[\mathcal{S}^{\dagger}]$, then $(\widehat{\mathcal{C}}, \widehat{\tau}^{\dagger})$ models MATT over $\mathcal{L}[\mathcal{S}^{\dagger}]$. $\square$

Any category with pullbacks has a canonical natural pseudo-model where all maps are type projections.

**Lemma 6.2** Let $\mathcal{M}$ be an adjoint mode theory, and $\mathcal{C}: \mathcal{M} \to \mathcal{C}$ at be a pseudofunctor such that each $\mathcal{C}_p$ is locally cartesian closed. If we make $\mathcal{C}$ a modal pre-model in the canonical way, as above, then it has pre-$\Pi$-structure, positive pre-modalities, and negative pre-modalities.

**Proof.** Since $\mathcal{C}_p$ is locally cartesian closed and everything is a type projection, we have pre-$\Pi$-structure. For positive pre-modalities we take $i_{\Gamma,A}^{\mu}$ to be an identity, and similarly for negative pre-modalities. $\square$

**Theorem 6.3** Let $\kappa$ be an infinite regular cardinal, $\mathcal{L}$ a $\kappa$-small 2-category with a class of morphisms $\mathcal{S}$, and $\mathcal{C}: \mathcal{L} \to \mathcal{C}$ at a pseudofunctor such that each $\mathcal{C}_p$ is locally cartesian closed with $\kappa$-small limits, each $\mathcal{C}_{\mu}$ preserves $\kappa$-small limits, and has a right adjoint if $\mu \in \mathcal{S}$. Then $\widehat{\mathcal{C}}$ models extensional MATT over $\mathcal{L}[\mathcal{S}^{\dagger}]$.

**Proof.** By Lemma 4.5, local cartesian closure lifts from $\mathcal{C}$ to $\widehat{\mathcal{C}}$. Thus, $(\widehat{\mathcal{C}}, \mathcal{C})$ is an adjoint modal pre-model, so Theorem 6.1 and Lemma 6.2 yield a model of MATT. Composition and diagonals yield weakly stable $\Sigma$-types and extensional identity types in each $\mathcal{C}_p$, hence mode-locally by Theorem-Schema 5.7. $\square$

**Remark 6.4** In addition, the following should follow from Lemma 4.5 and Theorem-Schema 5.7.

- If each $\mathcal{C}_p$ has finite coproducts, then $\widehat{\mathcal{C}}$ models sum types at each mode.
- If each $\mathcal{C}_p$ is locally presentable and each $\mathcal{C}_{\mu}$ is accessible, then each $\widehat{\mathcal{C}}_p$ is again locally presentable. Thus, by the methods of [28], $\widehat{\mathcal{C}}$ models inductive types and quotient-inductive types at each mode.
- If $\mathcal{C}$ is a diagram of Grothendieck topoi and geometric morphisms, then each $\widehat{\mathcal{C}}_p$ is also a topos. Thus, if there are enough inaccessible cardinals, $\widehat{\mathcal{C}}$ models universes at each mode (see [16,41,13,39]).

Let $\mathcal{T}$opos denote the 2-category of Grothendieck topoi, geometric morphisms, and transformations.

**Theorem 6.5** Let $\mathcal{L}$ be a finite 2-category and $\mathcal{E}: \mathcal{L}^{\mathrm{coop}} \to \mathcal{T}$opos a pseudofunctor. Then the co-dextrification $\widehat{\mathcal{E}}$ models extensional MATT over $\mathcal{L}[\mathcal{L}^{\dagger}]$, with positive and negative modalities representing inverse image and direct image functors respectively, and extensional MLTT at each mode. $\square$

**Remark 6.6** Theorem 6.5 does not state explicitly how to extract conclusions about $\mathcal{E}$ from the interpretation of MATT in $\widehat{\mathcal{E}}$. We will not try to make this precise here, but the idea is that $\widehat{\mathcal{E}}_p$ can be viewed as a “presentation” of $\mathcal{E}_p$ via the reflector $\mathsf{L}^p: \widehat{\mathcal{E}}_p \to \mathcal{E}_p$, and that the interpretation of MATT respects this “quotient”. For instance, the anodyne context morphisms (Definition 5.14) in $\widehat{\mathcal{E}}_p$ are precisely those that are inverted by $\mathsf{L}^p$; thus MATT is “unable to distinguish” contexts that present the same object of $\mathcal{E}_p$. One way to make this more precise is using Quillen model categories.

We end by discussing some examples of simple classes of diagrams in $\mathcal{T}$opos, to explore the flexibility and the limits of Theorems 6.3 and 6.5. As we will see, in some cases extra left adjoints already exist, so that co-dextrification is not necessary; but even in this case, some coherence results like those of section 5 are often still needed (see Remark 5.3). Table 1 summarizes some of the following examples, along with whether left adjoints already exist, and pointers to related theories in the literature.

**Example 6.7** If $\mathcal{L}$ consists of two objects $p, q$ and one nonidentity morphism $\mu: p \to q$, then a functor $\mathcal{L}^{\mathrm{coop}} \to \mathcal{T}$opos is a single geometric morphism. The resulting instance of MATT has two modes related by an adjoint pair of modalities $\mu \boxminus_{\blacksquare}$ and $\mu \diamondsuit_{\blacksquare}$. It is related to the split-context theory AdjTT of [43], and can be interpreted in any geometric morphism.

In particular, there is a unique geometric morphism from any topos $\mathcal{E}$ to **Set**. The resulting instance of MATT combines the usual internal language of $\mathcal{E}$ at one mode with the classical world of **Set** at another

$^3$ This is an $\infty$-topos without any 1-categorical analogue, so it is not covered by the semantic results in this paper.

18–16

Semantics of multimodal adjoint type theory

|  2-category $\mathcal{L}$ | Semantics | $\dashv ?$ | MATT related to  |
| --- | --- | --- | --- |
|  Single morphism | Geometric morphism • Cartesian comonad coalgebras | no no | AdjTT [43] CoTT [43]  |
|  Idempotent monad | Totally connected topos | no | Parametric TT [32]  |
|  Idempotent comonad | Local topos (Example 6.10) • Johnstone's topos [18] • $\kappa$-condensed sets [35,3] • Cohesive topos [23,36] | no no no yes | Spatial TT [37], Crisp TT [25]  |
|  Idem. monad w/ $\triangleright$ | Topos of trees | yes | Guarded TT [12, §9] and [11, §VI]  |
|  Meet-semilattice | Commuting foci • Simplicial spaces (Example 6.10) • Differential cohesive topos | no no yes | [31] [14]  |
|  Idempotent bimonad | Parametrized spectra^{3} | yes | [34]  |
|  Example 6.15 | Geometric realization | no |   |

Table 1
Instantiations of MATT and their semantics

mode, with a “discrete objects” modality $\mu \boxdot_-$ taking any set to an object of $\mathcal{E}$, having a right adjoint “global sections” modality $\mu \diamond \to_-$. This allows us to use the internal logic of $\mathcal{E}$ but also make “external” statements when needed, e.g. to study the cohomology of $\mathcal{E}$, or “global” structures that do not lift to arbitrary slices. In the language of Lawvere [22], terms at mode $q$ would be called “variable quantities”, while those at at mode $p$ would be “constant quantities”. Since the functor $\mathbf{Set} \to \mathcal{E}$ does not in general have a left adjoint, such an interpretation for a general topos is impossible without co-dextrification. (When this functor does have a left adjoint, one says that $\mathcal{E}$ is locally connected.)

The composite sending $A$ to $\mu \boxdot(\mu \diamond \to A)$ is then a comonad on one mode, while the one sending $B$ to $\mu \diamond \to (\mu \boxdot A)$ is a monad on the other. The 2-categories freely generated by a monad or a comonad are infinite, but if a monad or comonad decomposes through a geometric morphism in this way we can internalize it in MATT without needing infinite limits. Such a comonad decomposes if and only if it preserves finite limits; indeed the category of coalgebras for a finitely continuous comonad on a topos is again a topos. (If we also identify an object with its coffee coalgebra, so we only need one mode of syntactic types, we obtain something like the CoTT of [43].) The category of algebras for a finitely continuous monad on a topos need not be a topos; but if the topos is Boolean, then it can be induced by some geometric morphism [17]. And for a general finitely continuous monad on a topos, the category of algebras is at least locally cartesian closed by [21] on slice categories, so Theorem 6.3 can still be applied.

Example 6.8 Let $\mathcal{L}$ be the 2-category freely generated by an adjunction $\mu \dashv \nu$. Then in $\mathcal{L}[\mathcal{L}^{\dagger}]$ we have $\mu^{\dagger} \cong \nu$ by uniqueness of adjoints, so $\mathcal{L}[\mathcal{L}^{\dagger}]$ is generated (up to equivalence) by an adjoint triple $\mu \dashv \nu \dashv \nu^{\dagger}$. Since $\mathcal{L}$ is countably infinite, we can interpret MATT over this $\mathcal{L}[\mathcal{L}^{\dagger}]$ in any adjoint triple of functors between toposes (or more general categories) whose left adjoint preserves countable limits (the right adjoints do automatically, of course). We would generally prefer to represent the adjoint triple with the modalities $\mu \boxdot_-, \mu \diamond \to_-$ and $\nu \diamond \to_-$, since $\mu \diamond \to_-$ has stronger rules than the equivalent $\nu \boxdot_-$.

Example 6.9 By contrast, the 2-category $\mathcal{L}$ freely generated by a strictly reflective adjunction (i.e. whose counit is an identity) is finite. It has two modes $p$ and $q$, morphisms $\mu : p \to q$ and $\nu : q \to p$ such that $\mu \circ \nu = 1_q$, and a 2-cell $\eta : 1_p \Rightarrow \nu \circ \mu$ such that $\eta \triangleright \nu = 1_\nu$ and $\mu \triangleleft \eta = 1_\mu$. This determines all the composites, so no additional data are needed. A pseudofunctor $\mathcal{L} \to \mathcal{C}at$ is a non-strictly reflective adjunction, whose counit is an isomorphism. Thus we can interpret MATT over this $\mathcal{L}$ in an arbitrary reflective adjunction between toposes, giving a modal type theory for a topos equipped with a subtopos.

Shulman

18–17

If the inclusion functor has a further right adjoint, we have a coreflective adjunction in $\mathcal{T}$opos, and we can interpret MATT over $\mathcal{L}[\mathcal{L}^{\dagger}]$ with $\nu$ sinister. The induced geometric morphism from the larger topos to the smaller one is then called totally connected. For instance, the “topos of trees” used in guarded recursion theory (presheaves on $(\mathbb{N}, \leq)$) is totally connected over Set; the modal type theories that it models are discussed in [12, §9] and [11, §VI]. (In this topos, the left adjoint happens to already have a further left adjoint, so co-dextrification is not required to interpret modal type theory.)

Example 6.10 Taking $\mathcal{L}$ to be the opposite of the one from Example 6.9, we can interpret MATT in an arbitrary coreflective adjunction between toposes. This is the same as a connected geometric morphism, such as that from sheaves on some connected space to Set.

If the right adjoint has a further right adjoint, so that we can interpret MATT over $\mathcal{L}[\mathcal{L}^{\dagger}]$, the geometric morphism is called local. This property rarely holds for the topos of sheaves on a space (a “little topos”), but it often does for toposes whose objects can be interpreted as some kind of space (“big toposes”). Big toposes are a natural home for synthetic topology. One is Johnstone’s topological topos [18], whose objects are a sort of sequential convergence space; the internal language of this topos is used for instance in [8]. A related topos is $\kappa$-condensed sets [35], which has been advocated for the study of algebraic objects equipped with topology. (When $\kappa$ is inaccessible, these are also called pyknotic sets [3]. The category of all “condensed sets” is locally cartesian closed but not a topos.)

Many local toposes are also cohesive, meaning that the leftmost adjoint of their adjoint triple has a further left adjoint. This left adjoint is not usually finitely continuous, so it cannot be represented internally as a judgmental modality with co-dextrification, although it can be introduced axiomatically as in [37,31]. When it exists, co-dextrification is not needed to interpret the other modalities. But Johnstone’s topological topos and $\kappa$-condensed sets are not cohesive, so co-dextrification is necessary in those cases.

Non-cohesive local toposes turn out to have many advantages. One clear advantage is that they can include non-locally-connected spaces, which arise naturally in many parts of mathematics. In addition, they often do a better job of faithfully encoding topological notions such as unions of closed sets, constructions of cell complexes (including geometric realization of simplicial sets), and cohomology. In [9] such a topos was used to represent the Kleene–Kreisel functionals and model principles of intuitionism.

Example 6.11 We can simplify the mode theory of Example 6.10 by removing the mode corresponding to the base topos. Then $\mathcal{L}$ has one mode $p$ and a single idempotent comonad $\mu : p \rightarrow p$, and is again finite. Thus, MATT over this $\mathcal{L}$ can be interpreted in any topos that is connected over some base, with the base topos visible as the modal types for the comonad $\mu \square$. This instantiation of MATT is similar to the split-context “crisp type theory” used in [25] to construct universes in cubical sets.

If the topos is additionally local, the comonad has a right adjoint monad, and we can interpret MATT over $\mathcal{L}[\mathcal{L}^{\dagger}]$. This is similar to the split-context “spatial type theory” of [37], which was conjectured to be interpretable in any local topos; we have thus established this for a related lock-based theory. Note that although examples like Johnstone’s topological topos and pyknotic sets require co-dextrification, the intended model of [37] is cohesive and hence does not.

Example 6.12 Applying the same simplification to Example 6.9, we obtain a 2-category $\mathcal{L}$ with one mode and an idempotent monad, for which $\mathcal{L}[\mathcal{L}^{\dagger}]$ can be interpreted in any topos that is totally connected over some base. This is related to the left-lifting theory of [32], which is interpreted in a topos of “bridge/path cubical sets” that is totally connected over ordinary cubical sets. (The left adjoint in this case also has a further pair of left adjoints.)

Example 6.13 If $\mathcal{L}$ is a meet-semilattice, regarded as a monoidal poset and thereby a one-object 2-category, we obtain an instance of MATT that is similar to the left-lifting theory of [31]. In many of their examples each “focus” is cohesive, hence the further left adjoints needed for locks already exist. This includes the situation of “differential cohesion” studied in [14], as well as other related situations. But there are related examples in which not all foci are cohesive, such as simplicial objects in the topological topos, or simplicial pyknotic sets, and for these we require co-dextrification.

Example 6.14 The left-lifting theory of [34] is similar to MATT over the 2-category generated by an idempotent endomorphism that is both a monad and a comonad and adjoint to itself. This means we can

18–18

Semantics of multimodal adjoint type theory

represent its modality negatively, and use it as its own lock functor in semantics, thereby interpreting this instance of MATT in any topos equipped with such an endofunctor. Unfortunately, the intended model of [34] is an $(\infty, 1)$-topos without an evident 1-categorical analogue, so it is not covered by this paper.

Example 6.15 By [18, Theorem 8.1], there is a geometric morphism $S : \mathcal{E} \to \mathbf{sSet}$ from Johnstone's topological topos $\mathcal{E}$ to the topos $\mathbf{sSet}$ of simplicial sets, whose direct image $S_*$ is the total singular complex (suitably generalized) and whose inverse image $S^*$ is geometric realization. Since both $\mathcal{E}$ and $\mathbf{sSet}$ are local over $\mathbf{Set}$, this allows us to reason formally about geometric realization using an instance of MATT with three modes — say $t$ for the topological topos, $s$ for simplicial sets, and $d$ for discrete sets — with sinister coreflective adjunctions relating $d$ to both $t$ and $s$, and a sinister morphism $\sigma : s \to t$ for the geometric realization adjunction. As $\mathcal{E}$ is not cohesive (though $\mathbf{sSet}$ is), and geometric realization is not a right adjoint, this would be impossible without co-dextrification. Using [18, Theorem 8.2], we can do something similar for geometric realization of "simplicial spaces", i.e. simplicial objects of $\mathcal{E}$.

## 7 Conclusion and future work

We have shown that, contrary to appearances, general modal type theories formulated with "context locks" following [12,11] can be interpreted in diagrams of categories without requiring additional left adjoints to interpret the locks. This significantly expands the potential semantics of such theories, strengthening the argument that they are a good general approach to modal dependent type theories. In addition, we have formulated MATT, a general context-lock modal type theory that unifies the positive modalities of [12] with the negative ones of [11], and shown that it is the natural type theory to interpret in our semantics.

We have, however, left many open questions for future research, such as the following.

- (i) Can the assumption of $\kappa$-small limits be weakened, specifically when $\kappa > \omega$?
- (ii) It is known [39] that intensional dependent type theory can be interpreted in any $(\infty, 1)$-topos. Can intensional MATT be interpreted in any diagram of $(\infty, 1)$-topoi?
- (iii) Is there a full "internal language correspondence" relating MATT to suitable diagrams of categories? E.g. do adjoint modal natural models have a homotopy theory that presents diagrams of categories?
- (iv) Does MATT satisfy normalization, and which $(\mathcal{L}, \mathcal{S})$ are decidable? (See Remark 2.6.)
- (v) Is there a general modal dependent type theory using left multi-liftings, and can it be interpreted in the co-dextrification? Can it be generalized to cases where left multi-liftings do not exist?
- (vi) In [27], simple modal type theories were unified with substructural ones. Is there a context-lock approach to substructurality? Can it be unified with modal dependent type theory?

## References

[1] Annenkov, D., P. Capriotti, N. Kraus and C. Sattler, Two-level type theory and applications, Mathematical Structures in Computer Science (2023), p. 1–56. arXiv:1705.03307. URL https://doi.org/10.1017/S0960129523000130

[2] Awodey, S., Natural models of homotopy type theory, Math. Structures Comput. Sci. 28 (2018), pp. 241–286. arXiv:1406.3219. URL https://doi.org/10.1017/S0960129516000268

[3] Barwick, C. and P. Haine, Pyknotic objects, I. Basic notions (2019). Available online at https://doi.org/10.48550/arXiv.1904.09966

[4] Birkedal, L., R. Clouston, B. Manna, R. Ejlers Mogelberg, A. M. Pitts and B. Spitters, Modal dependent type theory and dependent right adjoints, Mathematical Structures in Computer Science 30 (2020), p. 118–138. arXiv:1804.05236. URL https://doi.org/10.1017/S0960129519000197

[5] Cavallo, E., "Higher Inductive Types and Internal Parametricity for Cubical Type Theory," Ph.D. thesis, Carnegie Mellon University (2021). Available online at https://www.cs.cmu.edu/~rwh/students/cavallo.pdf

[6] Dawson, R., R. Paré and D. Pronk, Adjoining adjoints, Adv. Math. 178 (2003), pp. 99–140. URL https://doi.org/10.1016/S0001-8708(02)00068-3

Shulman

18–19

[7] Dawson, R., R. Paré and D. Pronk, Undecidability of the free adjoint construction, Applied Categorical Structures 11 (2003), pp. 403–419.
URL https://doi.org/10.1023/A:1025712521140

[8] Escardó, M., Topology via higher-order intuitionistic logic (2004), unfinished draft. Available online at http://www.cs.bham.ac.uk/~mhe/papers/index.html.

[9] Escardó, M. and C. Xu, A constructive manifestation of the Kleene–Kreisel continuous functionals, Annals of Pure and Applied Logic 167 (2016), pp. 770–793, fourth Workshop on Formal Topology (4WFTop).
URL https://doi.org/10.1016/j.apal.2016.04.011

[10] Gratzer, D., Normalization for multimodal type theory, in: Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science, LICS '22 (2022), pp. 1–13, arXiv:2106.01414.
URL https://doi.org/10.1145/3531130.3532398

[11] Gratzer, D., E. Cavallo, G. A. Kavvos, A. Guatto and L. Birkedal, Modalities and parametric adjoints, ACM Trans. Comput. Logic 23 (2022).
URL https://doi.org/10.1145/3514241

[12] Gratzer, D., G. A. Kavvos, A. Nuyts and L. Birkedal, Multimodal dependent type theory, Logical Methods in Computer Science 17 (2021).
URL https://doi.org/10.46298/LMCS-17(3:11)2021

[13] Gratzer, D., M. Shulman and J. Sterling, Strict universes for Grothendieck topoi (2022), Available online at https://doi.org/10.48550/arXiv.2202.12012

[14] Gross, J. A., D. R. Licata, M. S. New, J. Paykin, M. Riley, M. Shulman and F. Wellen, Differential cohesive type theory (extended abstract), Workshop on Homotopy Type Theory and Univalent Foundations (2017). Available online at https://hott-uf.github.io/2017/abstracts/cohesivett.pdf

[15] Hofmann, M., On the interpretation of type theory in locally cartesian closed categories, in: Proceedings of Computer Science Logic, Lecture Notes in Computer Science (1994), pp. 427–441.
URL https://doi.org/10.1007/BFb0022273

[16] Hofmann, M. and T. Streicher, Lifting Grothendieck universes (1997). Available online at http://www.mathematik.tu-darmstadt.de/~streicher/NOTES/lift.pdf.

[17] Johnstone, P., Cartesian monads on toposes, Journal of Pure and Applied Algebra 116 (1997), pp. 199–220.
URL https://doi.org/10.1016/S0022-4049(96)00165-X

[18] Johnstone, P. T., On a topological topos, Proc. London Math. Soc. (3) 38 (1979), pp. 237–271.
URL https://doi.org/10.1112/plms/s3-38.2.237

[19] Johnstone, P. T., “Sketches of an Elephant: A Topos Theory Compendium: Volumes 1 and 2,” Number 43 in Oxford Logic Guides, Oxford Science Publications, 2002. ISBN: 978-0198534259 and ISBN: 978-0198515982

[20] Kelly, G. M., Doctrinal adjunction, in: Category Seminar (Proc. Sem., Sydney, 1972/1973), Springer, Berlin, 1974 pp. 257–280. Lecture Notes in Math., Vol. 420.
URL https://doi.org/10.1007/BFb0063105

[21] Kock, A., Bilinearity and Cartesian closed monads, Math. Scand. 29 (1971), pp. 161–174 (1972). URL http://www.jstor.org/stable/24491025
URL https://doi.org/10.7146/math.scand.a-11042

[22] Lawvere, F. W., Variable quantities and variable structures in topoi, in: A. Heller and M. Tierney, editors, Algebra, Topology, and Category Theory, Academic Press, 1976 pp. 101–131.
URL https://doi.org/10.1016/B978-0-12-339050-9.50014-6

[23] Lawvere, F. W., Axiomatic cohesion, Theory and Applications of Categories 19 (2007), pp. 41–49. Available online at http://www.tac.mta.ca/tac/volumes/19/3/19-03.pdf

[24] Licata, D., A fibrational framework for substructural and modal dependent type theories, Talk at Homotopy Type Theory Electronic Seminar (2019). Video and slides available online at http://uwo.ca/math/faculty/kapulkin/seminars/hottest.html.

[25] Licata, D. R., I. Orton, A. M. Pitts and B. Spitters, Internal universes in models of homotopy type theory, Leibniz International Proceedings in Informatics (LIPIcs) 108 (2018), pp. 1–17. arXiv:1801.07664.
URL https://doi.org/10.4230/LIPIcs.FSCD.2018.22

18–20

Semantics of multimodal adjoint type theory

[26] Licata, D. R. and M. Shulman, Adjoint logic with a 2-category of modes, in: S. Artemov and A. Nerode, editors, Logical Foundations of Computer Science (2016), pp. 219–235. Available online at http://dlicata.web.wesleyan.edu/pubs/ls15adjoint/ls15adjoint.pdf. URL https://doi.org/10.1007/978-3-319-27683-0_16
[27] Licata, D. R., M. Shulman and M. Riley, A fibrational framework for substructural and modal logics, Formal Structures for Computation and Deduction (2017). URL https://doi.org/10.4230/LIPIcs.FSCD.2017.25
[28] Lumsdaine, P. L. and M. Shulman, Semantics of higher inductive types, Mathematical Proceedings of the Cambridge Philosophical Society 169 (2020), pp. 159–208, arXiv:1705.07088. URL https://doi.org/10.1017/S030500411900015X
[29] Lumsdaine, P. L. and M. A. Warren, The local universes model: An overlooked coherence construction for dependent type theories, ACM Trans. Comput. Logic 16 (2015), pp. 23:1–23:31, arXiv:1411.1736.
[30] Makkai, M. and R. Paré, “Accessible categories: the foundations of categorical model theory,” Contemporary Mathematics 104, American Mathematical Society, Providence, RI, 1989, viii+176 pp. eBook ISBN: 978-0-8218-7692-3.
[31] Myers, D. J. and M. Riley, Commuting cohesions (2023), arXiv:2301.13780. URL https://doi.org/10.48550/arXiv.2301.13780
[32] Nuyts, A., A. Vezzosi and D. Devriese, Parametric quantifiers for dependent type theory, Proc. ACM Program. Lang. 1 (2017). URL https://doi.org/10.1145/3110276
[33] Pfenning, F. and R. Davies, A judgmental reconstruction of modal logic, Mathematical Structures in Comp. Sci. 11 (2001), pp. 511–540. URL https://doi.org/10.1017/S0960129501003322
[34] Riley, M., E. Finster and D. R. Licata, Synthetic spectra via a monadic and comonadic modality (2021), arXiv:2102.04099. URL https://doi.org/10.48550/arXiv.2102.04099
[35] Scholze, P., Lectures on condensed mathematics (2019), (joint with Dustin Clausen). Available online at https://www.math.uni-bonn.de/people/scholze/Condensed.pdf.
[36] Schreiber, U., Differential cohomology in a cohesive ∞-topos (2013), http://ncatlab.org/schreiber/show/differential+cohomology+in+a+cohesive+topos; URL https://doi.org/10.48550/arXiv.1310.7930
[37] Shulman, M., Brouwer’s fixed-point theorem in real-cohesive homotopy type theory, Mathematical Structures in Computer Science 28 (2018), pp. 856–941, arXiv:1509.07584. URL https://doi.org/10.1017/S0960129517000147
[38] Shulman, M., Type 2-theories, Talk at Homotopy Type Theory Electronic Seminar (2018). Video and slides available online at http://uwo.ca/math/faculty/kapulkin/seminars/hottest.html.
[39] Shulman, M., All (∞, 1)-toposes have strict univalent universes (2019). arXiv:1904.07004. URL https://doi.org/10.48550/arXiv.1904.07004
[40] Stassen, P., D. Gratzer and L. Birkedal, mitten: a flexible multimodal proof assistant (2022), https://jozefg.github.io/papers/mitten-a-flexible-multimodal-proof-assistant.pdf.
[41] Streicher, T., Universes in toposes, in: From sets and types to topology and analysis, Oxford Logic Guides 48, Oxford Univ. Press, Oxford, 2005 pp. 78–90. Available online at https://www2.mathematik.tu-darmstadt.de/~streicher/NOTES/UniTop.pdf
[42] Wraith, G., Artin glueing, Journal of Pure and Applied Algebra 4 (1974), pp. 345–348. URL https://doi.org/10.1016/0022-4049(74)90014-0
[43] Zwanziger, C., Natural model semantics for comonadic and adjoint type theory: Extended abstract, in: Preproceedings of Applied Category Theory Conference 2019, 2019. Available online at https://www.cs.ox.ac.uk/ACT2019/preproceedings/Colin%20Zwanziger%20Natural%20Model%20Semantics%20for%20Comonadic%20