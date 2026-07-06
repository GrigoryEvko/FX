Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:23

Example 5.4. If $\mathbb{U}$ is cartesian, i.e. $[\mathbb{X}, u : \mathbb{U}] = [\mathbb{X}] \times [\mathbb{U}]$, then there is a diagonal substitution $(w : \mathbb{U}, u := w, v := w) : [\mathbb{X}, w : \mathbb{U}] \to [\mathbb{X}, u : \mathbb{U}, v : \mathbb{U}]$. Writing

$$\begin{array}{l} \alpha = 1_{\Pi u} * 1_{\Pi v} * \operatorname{const}_{(w, u := w, v := w)} : \Pi u \circ \Pi v \Rightarrow \\ \quad \Pi u \circ \Pi v \circ \Pi(w, u := w, v := w) \circ \Omega[w, u := w, v := w] \\ \quad = \Pi((u : \mathbb{U}) \circ (v : \mathbb{U}) \circ (w, u := w, v := w)) \circ \Omega[w, u := w, v := w] \\ \quad = \Pi((u : \mathbb{U}) \circ (w, u := w)) \circ \Omega[w, u := w, v := w] \\ \quad = \Pi w \circ \Omega[w, u := w, v := w], \end{array}$$

where the equations use strict functoriality of $\Pi \sqcup$ and ordinary calculation of composition of substitutions, this allows us to type the naively typed function $\lambda f.\lambda w.f w w : (\Pi u.\Pi v.A) \to \Pi w.A[w/u, w/v]$ as

$$\langle \Pi(u : \mathbb{U}) \mid \langle \Pi(v : \mathbb{U}) \mid A \rangle \rangle \to \langle \Pi(w : \mathbb{U}) \mid \langle \Omega[w : \mathbb{U}, u := w, v := w] \mid A[\mathbf{Q}_{\alpha}] \rangle \rangle.$$

Remark 5.5. The reframing of shape substitutions as a modality, has the annoying consequence that substitution no longer reduces. However, both $\langle \Omega[\sigma] \mid \sqcup \rangle$ and $\operatorname{mod}_{\Omega[\sigma]}$ are semantically an ordinary substitution (along an isomorphism, see Remark 5.2). Thus, we could add computation rules such as:

$$\begin{array}{rcl} \langle \Omega[\sigma] \mid A \times B \rangle & = & \langle \Omega[\sigma] \mid A \rangle \times \langle \Omega[\sigma] \mid B \rangle, \quad \langle \Omega[\sigma] \mid \mathsf{U} \rangle = \mathsf{U}, \\ \operatorname{mod}_{\Omega[\sigma]}(a, b) & = & (\operatorname{mod}_{\Omega[\sigma]} a, \operatorname{mod}_{\Omega[\sigma]} b), \quad \operatorname{mod}_{\Omega[\sigma]} \lceil A \rceil = \lceil \langle \Omega[\sigma] \mid A \rangle \rceil. \end{array}$$

This is fine in an extensional type system, but would not play well with the $\beta$-rule for modal types in an intensional system. Indeed, $\beta$-reduction for $\langle \Omega[\sigma] \mid A \rangle$ requires a solution to the following problem: when $\hat{a} = \operatorname{mod}_{\Omega[\sigma]} a$ definitionally, then we need to be able to infer $a$ up to definitional equality from $\hat{a}$. Alternatively, the eliminator for $\langle \Omega[\sigma] \mid A \rangle$ should somehow proceed by induction on $A$, e.g. an element of $\langle \Omega[\sigma] \mid A \times B \rangle$ could be eliminated as an element of $\langle \Omega[\sigma] \mid A \rangle \times \langle \Omega[\sigma] \mid B \rangle$. A third possibility would be to abolish elimination of $\langle \Omega[\sigma] \mid \sqcup \rangle$ altogether, except when applied to type formers for which there is no definitional substitution-commutation law.

Remark 5.6. In type theory, we generally expect admissibility of substitution: given a derivable judgement $\Gamma \vdash J$ and a substitution $\sigma : \Delta \to \Gamma$, we expect derivability of $\Delta \vdash J[\sigma]$, where the operation $\sqcup[\sigma]$ can be applied to any term, type or other object in context and traverses its structure, leaving everything untouched except variables. A good way to guarantee admissibility of substitution is by making sure that every inference rule has a conclusion in a general context $\Gamma$ and that the context of any premise is obtained by applying a functorial operation to $\Gamma$.

There is no such result for shape substitutions. The conclusion of modal inference rules often has a non-general shape context, and the transpension type is in general not even respected by shape substitution [Nuy20b]. However, until we extend MTraS with additional rules in Sections 8 to 10,¹³ we do have a form of the usual result: given a derivable judgement $\mathbb{X} \mid \Gamma \vdash J$ and a substitution $\mathbb{X} \mid \sigma : \Delta \to \Gamma$, we can derive $\mathbb{X} \mid \Delta \vdash J[\sigma]$.

¹³And possibly even after, see Remark 9.4.