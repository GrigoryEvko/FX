Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:7

a variable $x : \langle \mu \mid A \rangle$ only when our context is structured in a way that does not obstruct the use of $x$, and the final arbiter of that is the modal elimination rule.

MTT turns this idea on its head: rather than handing control over to the modal elimination rule, we delegate this decision to the variable rule itself. In order to ascertain whether we can use a variable in our calculus, the variable rule examines the locks to the right of the variable. The rule of thumb is this: we should always be able to access $\langle \mu \mid A \rangle$ behind $\widehat{\bullet}_{\mu}$. Carrying the illustrative analogy of an adjunction $-, \widehat{\bullet}_{\mu} \dashv \langle \mu \mid - \rangle$ further, we see that the simplest judgment that fits this, namely $\Gamma, x : \langle \mu \mid A \rangle, \widehat{\bullet}_{\mu} \vdash x : A \circledast n$, corresponds to the counit of the adjunction.

To correctly formulate the variable rule, we will require one more idea: following modal type theories based on left division [Pfe01, Abe06, Abe08, NVD17, ND18], every variable in the context will be annotated with a modality, $x : (\mu \mid A)$. Intuitively a variable $x : (\mu \mid A)$ is the same as a variable $x : \langle \mu \mid A \rangle$, but the annotations are part of the structure of a context while $\langle \mu \mid A \rangle$ is a type. This small circumlocution will ensure that the variable rule respects substitution.

The most general form of the variable rule will be able to handle the interaction of modalities, so we present it in stages. A first counit-like approximation is then

$$\frac{\widehat{\bullet} \not\in \Gamma_1 \quad \Gamma_0, \widehat{\bullet}_{\mu} \vdash A \text{ type}_1 \circledast n}{\Gamma_0, x : (\mu \mid A), \widehat{\bullet}_{\mu}, \Gamma_1 \vdash x : A \circledast n}$$

The first premise requires that no further locks occur in $\Gamma_1$, so that the conclusion remains in the same mode $n$. The second premise is just enough to derive $\Gamma_0 \vdash \langle \mu \mid A \rangle \text{ type}_1 \circledast m$.

Context extension. The switch to modality-annotated declarations $x : (\mu \mid A)$ also requires us to revise the context extension rule. The revised version, CX/EXTEND, appears in Figure 2 and closely follows the formation rule for $\langle \mu \mid - \rangle$: if $\Gamma, \widehat{\bullet}_{\mu} \vdash A \text{ type}_1 \circledast n$ is a type in the locked context $\Gamma$, then we may extend the context $\Gamma$ to include a declaration $x : (\mu \mid A)$, so that $x$ stands for a term of type $A$ under the modality $\mu$.

The elimination rule. The difference between a modal type $\langle \mu \mid A \rangle$ and an annotated declaration $x : (\mu \mid A)$ in the context is navigated by the modal elimination rule. In brief, its role is to enable the substitution of a term of the former type for a variable with the latter declaration. The full rule is complex, so we first discuss the case of a single modality $\mu : n \to m$. The corresponding rule is

$$\frac{\begin{array}{c} \text{TM/MODAL-ELIM/SINGLE-MODALITY} \\ \Gamma \vdash M_0 : \langle \mu \mid A \rangle \circledast m \\ \Gamma, x : (1 \mid \langle \mu \mid A \rangle) \vdash B \text{ type}_1 \circledast m \quad \Gamma, y : (\mu \mid A) \vdash M_1 : B[\text{mod}_{\mu}(y)/x] \circledast m \\ \hline \Gamma \vdash \text{let mod}_{\mu}(y) \leftarrow M_0 \text{ in } M_1 : B[M_0/x] \circledast m \end{array}}{}$$

Forgetting dependence for a moment, we see that this rule is close to the dual-context style [PD01, Kav20]: if we think of annotations as separating the context into multiple zones, then $y : (\mu \mid A)$ clearly belongs to the 'modal' part.

In the dependent case we also need a motive $\Gamma, x : (1 \mid \langle \mu \mid A \rangle) \vdash B \text{ type}_1 \circledast m$, which depends on a variable of modal type, but under the identity modality 1. This premise is then fulfilled by $M_0$ in the conclusion. In a sense, this rule permits a form of modal induction: every variable $x : (1 \mid \langle \mu \mid A \rangle)$ can be assumed to be of the form $\text{mod}_{\mu}(y)$ for some $y : (\mu \mid A)$. This kind of rule has appeared before in the spatial and cohesive type theories of [Shu18].