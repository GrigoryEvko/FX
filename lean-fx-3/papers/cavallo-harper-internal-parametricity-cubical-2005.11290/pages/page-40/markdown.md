5:40

E. CAVALLO AND R. HARPER

Vol. 17:4

**4.5. Building up inference rules.** With a value type system in hand, it remains to verify that the judgments are closed under the inference rules introduced in Sections 1 and 2. We go through the typing rules for Gel-types in detail. The rules for Bridge-types are simpler to verify, as the reduction rules are all “cubically stable”: they do not depend on the status of any interval term. (In comparison, $\text{gel}_r(M_0, M_1, P)$ may be a value or step depending on whether $r$ is a variable or constant.) The rules for extent do involve unstable transitions, but require no ideas that are not present in the proofs for Gel-types; in particular, the hcom reduction for Gel involves extent-like variable capture. The reader may see [CH19b] for complete proofs of these results.

We rely on the following five lemmas to work with the candidate judgments. These are rephrasings of Lemmas A.2, A.3, and A.5 from [CH18]; each follows straightforwardly by unfolding definitions.

**Lemma 4.16** (Coherent type value). *Suppose $A, A'$ are terms. If for every $\Psi' \Vdash \Psi \in \Psi$, either $\tau(\Psi', A\psi, A'\psi, \alpha_\psi)$ or $\Psi' \Vdash A\psi \sim A'\psi \downarrow \alpha\psi \in \tau$, then $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$.*

**Lemma 4.17** (Coherent term value). *Suppose $\Psi \Vdash A \downarrow \alpha \in \tau$ and $M, M'$ are terms. If for every $\Psi' \Vdash \Psi \in \Psi$, either $\alpha_\psi(M\psi, M'\psi)$ or $\Psi' \Vdash M\psi \sim M'\psi \in \alpha\psi$, then $\Psi \Vdash M \sim M' \in \alpha$.*

**Lemma 4.18** (Coherent type expansion). *Suppose $A$ is a term and $(A_\psi)_{\Psi' \Vdash \psi \in \Psi}$ is a family of terms such that $A\psi \longmapsto^* A_\psi$ and $\Psi' \Vdash A_\psi \sim A_{\text{id}}\psi \downarrow \alpha\psi \in \tau$ for all $\Psi' \Vdash \psi \in \Psi$. Then $\Psi \Vdash A \sim A_{\text{id}} \downarrow \alpha \in \tau$.*

**Lemma 4.19** (Coherent term expansion). *Suppose $\Psi \Vdash A \downarrow \alpha \in \tau$, $M$ is a term, and $(M_\psi)_{\Psi' \Vdash \psi \in \Psi}$ is a family of terms such that $M\psi \longmapsto^* M_\psi$ and $\Psi' \Vdash M_\psi \sim M_{\text{id}}\psi \in \alpha\psi$ for all $\Psi' \Vdash \psi \in \Psi$. Then $\Psi' \Vdash M \sim M_{\text{id}} \in \alpha$.*

**Lemma 4.20** (Evaluation). *Suppose $\Psi \Vdash M = M' \in A$. Then $M \Downarrow V$ and $M' \Downarrow V'$ with $\Psi \Vdash M = V = V' = M' \in A$.*

We now check the rules for Gel-types as presented in Figure 6. We prove that each rule holds when the ambient context is an arbitrary interval context $\Psi$. The open rules—for an arbitrary context $\Gamma$—then follow mechanically, as the open type and term judgments are defined by their closed instantiations.

It is convenient to prove the boundary reduction equations for a type or term former *before* the general introduction rule; for example, we show first $\text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R) = A_\varepsilon$ pretype and then $\text{Gel}_r(A_0, A_1, a_0.a_1.R)$ pretype.

**Rule 4.21** (GEL-FORM-$\partial$). *For any $\varepsilon \in \{0, 1\}$, $\Psi \Vdash A_\varepsilon$ pretype, and terms $A_{1-\varepsilon}$, $R$, we have $\Psi \Vdash \text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R) = A_\varepsilon$ pretype.*

*Proof.* By Lemma 4.18, taking $A_\psi := A_\varepsilon\psi$: we have $\text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R)\psi \longmapsto A_\psi$ and $\Psi' \Vdash A_\varepsilon\psi \sim A_\varepsilon\psi \downarrow [A_\varepsilon]\psi \in \tau$ for all $\psi$. $\square$

As described above, this “closed” principle implies the open rule. Given $\Gamma$ ctx and $\Gamma \gg A_\varepsilon$ pretype, we have by definition that $\Psi \Vdash A_\varepsilon\gamma = A_\varepsilon\gamma'$ pretype for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$. Thus $\Psi \Vdash \text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R)\gamma = A_\varepsilon\gamma'$ pretype for all such instantiations by the rule just proven, which means that $\Gamma \gg \text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R) = A_\varepsilon$ pretype.

The following lemma gets us part of the way to the formation rule. We also need that the relation for Gel-types is value-coherent and supports the Kan operations; we will return to these later.