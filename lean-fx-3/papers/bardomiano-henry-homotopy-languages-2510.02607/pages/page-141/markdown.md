Each object comes with a fibration $A_\mu \to \Gamma$. This is given by the transfinite composition axiom of $\mathcal{C}$.

- **Morphisms:** For ordinals $\mu \leq \lambda < \kappa$ and objects $B_\lambda \in Ob_\lambda(\mathcal{C}(\Gamma))$, $A_\mu \in Ob_\mu(\mathcal{C}(\Gamma))$, we set

$$\operatorname{Hom}_{\mathcal{C}(\Gamma)}(B_\lambda, A_\mu) := \operatorname{Hom}_{\mathcal{C}/\Gamma}(B_\lambda, A_\mu).$$

- The rest of the structure of $\mathcal{C}(\Gamma)$ is induced by $\mathcal{C}/\Gamma$, in particular, the transfinite composition is that of $\mathcal{C}/\Gamma$.

Before proving that this gives us a $\kappa$-contextual category, let us explain the objects of this category. Recall that for $A \in \mathsf{Ty}(\Gamma)$ means we have a diagram of the form

$$\begin{array}{c} E_A \\ \downarrow \\ \Gamma \xrightarrow{f_A} V_A. \end{array}$$

When we identify this object with $[A]$, then $\mathsf{Ty}([A])$ is the set of objects of the form

$$\begin{array}{c} E_B \\ \downarrow \\ [A] \xrightarrow{(E_A)_{f_A}} E_A. \end{array}$$

Each of such objects gives $(V_A, f_A, E_B) \in \mathsf{Ty}(\Gamma)$, where $E_B \to V_A$ is the composition $E_B \to E_A \to V_A$. Equivalently, this is the composition $[B] \to [A] \to \Gamma$. Furthermore, if we write $\Gamma.A := [A]$, then we can rewrite this in a more familiar fashion $\Gamma.A.B \to \Gamma.A \to \Gamma$. This illustrates the general procedure for successor ordinals. A related construction appears in [KL18, Definition 4.3].

**Lemma B.60.** *For any $\kappa$-clan $\mathcal{C}$ and any $\Gamma \in \mathcal{C}$, the category $\mathcal{C}(\Gamma)$ is a $\kappa$-contextual category.*

Each axiom can be verified more or less immediately. We start with the category with attributes in theorem B.58 and the construction from theorem B.59.

*Proof.* 1. The objects of $\mathcal{C}(\Gamma)$ have grading $Ob(\mathcal{C}(\Gamma)) = \prod_{\mu < \kappa} Ob_\mu(\mathcal{C}(\Gamma))$ as in theorem B.59. This grading determines the height of each object.

141