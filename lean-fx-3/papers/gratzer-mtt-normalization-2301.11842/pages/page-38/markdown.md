27:38

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

**Lemma 7.3.** $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ *supports crisp identity induction.*

*Proof.* This argument is similar to Lemma 5.7, as the induction principle for modal types is always 'crisp' in MTT. We must implement the following constant.

$$\begin{array}{l} \mathsf{J}_{\mu}^{*}:(\mu \mid A:\mathsf{Ty}_{n}^{*})(B:(\mu \mid a_{0},a_{1}:\mathsf{Tm}_{n}^{*}(A))(\mu \mid p:\mathsf{Tm}_{n}^{*}(\mathsf{Id}^{*}(A,a_{0},a_{1})))\to\mathsf{Ty}_{m}^{*}) \\ \quad\rightarrow(b:(\mu \mid a:\mathsf{Tm}_{n}^{*}(A))\rightarrow\mathsf{Tm}_{m}^{*}(B(a,a,\mathsf{refl}^{*}(a)))) \\ \quad\rightarrow(\mu \mid a_{0},a_{1}:\mathsf{Tm}_{n}^{*}(A))(\mu \mid p:\mathsf{Tm}_{n}^{*}(\mathsf{Id}(A,a_{0},a_{1})))\rightarrow \\ \quad\rightarrow\{\mathsf{Tm}_{m}^{*}(B(a_{0},a_{1},p))\mid z:\mathbf{syn}\mapsto\mathsf{J}_{\mu}(A,B,b,p)\} \end{array}$$

Let us fix $A$, $B$, $b$, $a_0$, $a_1$, and $p$ with the types described above. Recalling the definition of $\mathsf{Id}^*(A, a_0, a_1).\mathsf{pred}$ from Lemma 5.10, we can commute $\langle\mu \mid -\rangle$ past the dependent sum, closed modalities, equality types, and coproducts to decompose $p$ into a pair of the following:

$$\begin{array}{l} (\mu \mid \mathsf{tm}:\mathsf{Nf}_{n}(\mathsf{Id}(A,a_{0},a_{1}))) \\ \mathsf{prf}:\bullet\left[\begin{array}{l} (\sum_{e:\langle\mu|\mathsf{Ne}_{n}(\mathsf{Id}(A,a_{0},a_{1}))\rangle}\mathbf{up}\circledast e=\mathsf{mod}_{\mu}(\mathsf{tm})) \\ +(\mathsf{mod}_{\mu}(a_{0})=\mathsf{mod}_{\mu}(a_{1})\times\mathsf{mod}_{\mu}(\mathsf{tm})=\mathsf{mod}_{\mu}(\mathsf{refl}(a_{0}))) \end{array}\right] \end{array}$$

We then define $\mathsf{J}_{\mu}^{*}(B,b,a_{0},a_{1},p)$ by analyzing prf:

$$\left\{\begin{array}{ll} \mathsf{J}(z,B,b,a_{0},a_{1},p) & \mathsf{prf}=\iota_{1}(z) \\ \downarrow\mathbf{J}(\lambda a_{0},a_{1},p.B(\uparrow a_{0},\uparrow a_{1},\uparrow p).\mathsf{code},\lambda a.\downarrow b(\uparrow a),e) & q=\iota_{2}(\iota_{1}(e,-)) \\ b(a_{0}) & q=\iota_{2}(\iota_{2}(.,-)) \end{array}\right. \quad \square$$

Having made this alteration, the remainder of Sections 5 and 6 are unchanged. In particular, all the results of Section 6 continue to hold in the presence of crisp induction.

### 8. RELATED WORK

We have built on top of a long line of research systematically structuring logical relations as gluing models [MS93, AHS95, Str98, Fio02, Shu15, AK17, KHS19, Coq19, SA21, Ste21]. In particular, Altenkirch et al. [AHS95] and Fiore [Fio02] recast NbE into the construction of a gluing model in which types are triples $(A,\downarrow,\uparrow)$. Generalizing from this work to dependent type theory has proven a considerable challenge [AK16]. The final ingredient for Martin-Löf type theory was provided by Coquand [Coq19]: a construction of a universe in this gluing model similar to that of Shulman [Shu15].

**Gluing for modal type theory.** Gratzer et al. [GSB19a] gave a classical normalization-by-evaluation proof for a Fitch-style type theory. The complexity of this proof, however, makes it intractable to extend to a general modal type theory like MTT. Unfortunately, extending gluing techniques to modal type theories has proven challenging. In particular, Gratzer et al. [GKNB20a] used gluing to prove canonicity for MTT, but they were forced to add an additional equality to MTT $(\mathbf{1}.\{\mu\}=\mathbf{1})$ to tame the construction of the gluing model. The challenge lies in fitting the glued category of contexts into a CwF-style model of type theory; the natural definition of glued types and terms fails to admit modalities. While there have been some attempts to systematize the construction of glued CwFs [KHS19], they do not apply to MTT.

Recently, Hu and Pientka [HP22] gave a proof of normalization for a simply-typed Fitch-style type theory (Kripke-style in their parlance) with one modality. They give