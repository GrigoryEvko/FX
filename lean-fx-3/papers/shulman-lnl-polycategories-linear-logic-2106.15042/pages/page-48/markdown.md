1:48

M. SHULMAN

Vol. 19:2

be redundant, corresponding to hom-sets that are always canonically isomorphic to some other hom-sets, and can be omitted from the syntax.

For example, a Kleisli sorted doctrine with $|\mathbb{D}| = \text{LNLMULTI}$ yields split-context calculi for intuitionistic linear logic like those of [Bar96, Wad94], with only one class of types that can appear in both parts of the context. Types in the nonlinear part have an implicit application of $\mathsf{U}$, so it makes sense to change notation and write $\mathsf{FA}$ as $!A$. Moreover, since $\mathcal{P}(\Theta; \mathsf{UA}) \cong \mathcal{P}(\Theta \mid ; A)$, the nonlinear morphisms are determined by the linear ones; thus we can dispense with the nonlinear sequents entirely, essentially defining them by the invertible rule for $\mathsf{U}$. The remaining logical rules for the exponentials then become:

$$\frac{\Theta \mid \cdot \vdash A}{\Theta \mid \cdot \vdash !A} \qquad \frac{\Theta, A \mid \Gamma \vdash \Delta}{\Theta \mid \Gamma, !A \vdash \Delta} \qquad \frac{\Theta \mid \Gamma, A \vdash \Delta}{\Theta, A \mid \Gamma \vdash \Delta}$$

The first two appear verbatim in [Bar96, Wad94], while the third is admissible [Bar96, Lemma 2.5]. The cut rule that mixes linear and nonlinear sequents also has to be restated in this notation, alongside the one for purely linear sequents:

$$\frac{\Theta' \mid \Gamma' \vdash \Delta', A \quad \Theta \mid \Gamma, A \vdash \Delta}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta, \Delta'} \qquad \frac{\Upsilon \mid \cdot \vdash A \quad \Theta, A \mid \Gamma \vdash \Delta}{\Theta, \Upsilon \mid \Gamma \vdash \Delta}.$$

These cut rules both appear in [Bar96, Lemma 3.1] (“Linear Cut” and “Intuitionistic Cut”) and in [Wad94] (“Cut” and the derivable “Cut-Int”).

Something similar happens in [EMS12] with $|\mathbb{D}| = \text{CBPV}$, although in this case the computation types are merely *included* in the value types by an implicit $\mathsf{U}$, rather than identified with them. This includes the above rules for $!A$ (meaning $\mathsf{FA}$) with $\Gamma = \emptyset$, and the (arity-restricted, cut-including) rules for $\to\circ$ (their “$\to$”):

$$\frac{\Theta \vdash X \quad \Theta' \mid \Gamma \vdash X \to\circ B}{\Theta, \Theta' \mid \Gamma \vdash B} \qquad \frac{\Theta, X \mid \Gamma \vdash B}{\Theta \mid \Gamma \vdash X \to\circ B}.$$

Likewise, for Example 6.9 with $|\mathbb{D}| = \text{SYMSKEW}$, the rules for restricted $\otimes$ and $\to\circ$ (with one tight input — the “stoup” — and the other loose) specialize to those of [UVZ18, UVZ20, Vel21, UVW22].

As a final example, in the double-Kleisli sorted doctrine of Example 6.7, we can write the sequents as $\Theta \mid \Gamma \vdash \Delta \mid \Upsilon$, where $\Theta$ and $\Upsilon$ consist of types lying over the “left-hand” and “right-hand” derived sorts respectively. Types in $\Theta$ have an implicit $\mathsf{U}$ and types in $\Upsilon$ have an implicit $\Pi$, so we write $\mathsf{F}$ and $\mathsf{J}$ as $!$ and $?$ respectively. Again we can define the nonlinear sequents by the invertible rules for $\mathsf{U}$ and $\Pi$ — although when translating a nonlinear sequent $\Theta, \Upsilon \vdash A$ in this way, we have to pay attention to whether $A$ is being regarded as a left-hand type or a right-hand type: in the former case the sequent becomes $\Theta \mid \cdot \vdash A \mid \Upsilon$, while in the latter case it becomes $\Theta \mid A \vdash \cdot \mid \Upsilon$ (due to the different universal properties of $\mathsf{U}$ and $\Pi$). The remaining logical rules then become:

$$\frac{\Theta \mid \cdot \vdash A \mid \Upsilon}{\Theta \mid \cdot \vdash !A \mid \Upsilon} \qquad \frac{\Theta, A \mid \Gamma \vdash \Delta \mid \Upsilon}{\Theta \mid \Gamma, !A \vdash \Delta \mid \Upsilon} \qquad \frac{\Theta \mid \Gamma, A \vdash \Delta \mid \Upsilon}{\Theta, A \mid \Gamma \vdash \Delta \mid \Upsilon}$$
$$\frac{\Theta \mid A \vdash \cdot \mid \Upsilon}{\Theta \mid ?A \vdash \cdot \mid \Upsilon} \qquad \frac{\Theta \mid \Gamma \vdash \Delta \mid \Upsilon, A}{\Theta \mid \Gamma \vdash \Delta, ?A \mid \Upsilon} \qquad \frac{\Theta \mid \Gamma \vdash \Delta, A \mid \Upsilon}{\Theta \mid \Gamma \vdash \Delta \mid \Upsilon, A}$$