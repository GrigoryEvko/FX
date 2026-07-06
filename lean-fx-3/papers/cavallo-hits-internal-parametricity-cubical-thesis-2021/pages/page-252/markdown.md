240

Cohesive parametric type theory

### 14.2.2 Context operators: modalities and restriction

To state the rules for closing substitutions, we must first define the modal operators on contexts, as these appear in the defining rule for substitutions into modal hypotheses. The intent is that we have $\Gamma.\mu \text{ ctx } @ m$ whenever $\Gamma \text{ ctx } @ n$ and $\mu : m \to n$.

Definition 14.2.5. Given a context $\Gamma$, we define the context $\Gamma.\mu$ for the three basic modalities (cc, dsc, and glo) in Figure 14.1. Application of a compound modality is defined by sequential application of basic modalities: $\Gamma.(cc, \mu) := \Gamma.cc.\mu$ and so on.

The salient aspects of these definitions are their behavior on bridge interval hypotheses and term hypotheses, reproduced below.

$$(x : \mathbf{I}).\text{cc} := \cdot \quad (\mu \mid a : A).\text{cc} := \begin{cases} (\mu' \mid a : A), & \text{if } \mu = \text{cc}, \mu' \\ \cdot, & \text{otherwise} \end{cases}$$

$$(\mu \mid a : A).\text{dsc} := (\text{cc}, \mu \mid a : A)$$

$$(x : \mathbf{I}).\text{glo} := x : 2 \quad (\mu \mid a : A).\text{glo} := (\text{dsc}, \mu \mid a : A)$$

The connected components operator squashes interval hypotheses, while the global sections operator replaces them with endpoint hypotheses. The two right adjoints evaluate on term hypotheses by adding their left adjoints to the hypothesis modality, while the connected components operator removes all term hypotheses not beneath cc. The evaluation of cc on constraints is also somewhat tricky: it leaves constraints on endpoints alone and squashes consistent equations on variables while preserving inconsistent equations. Each modality also induces a functorial action on substitutions following the same pattern. Here we intend to have $\Gamma'.\mu \gg (\gamma : \Gamma) \otimes \mu \in \Gamma.\mu @ m$ whenever $\mu : m \to n$ and $\Gamma' \gg \gamma \in \Gamma @ n$.

Definition 14.2.6. Given a context $\Gamma$ and substitution $\gamma$ into $\Gamma$, we define the substitution $(\gamma : \Gamma) \otimes \mu$ for the basic modalities in Figure 14.2. The action of compound modalities is defined as with contexts.

Remark 14.2.7. The effect of a substitution $(\gamma : \Gamma) \otimes \mu$ on syntax is the same as that of $\gamma$. That is, if $M$ is a term depending only on the variables in $\Gamma.\mu$, then $M[(\gamma : \Gamma) \otimes \mu] = M\gamma$.

Finally, we update the definition of interval restriction (Definition 9.1.9) to handle the new forms of hypothesis. We also specify that restriction by an endpoint variable, like that by an endpoint constant, is the identity.

Definition 14.2.8 (Interval restriction). Given a context $\Gamma$ and term $\Gamma \gg r \in \mathbf{I}$, we define $\Gamma \setminus r$ in Figure 14.3. The action $(\gamma : \Gamma) \setminus r$ is defined analogously.