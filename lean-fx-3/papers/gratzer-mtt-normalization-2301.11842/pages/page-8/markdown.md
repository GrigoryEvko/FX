27:8

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

$$\frac{\mu : n \longrightarrow m \quad \Gamma \mathsf{cx} @ m}{\Gamma . \{\mu\} \mathsf{cx} @ n} \quad \frac{\mu : n \longrightarrow m \quad \Gamma \vdash \delta : \Delta @ m}{\Gamma . \{\mu\} \vdash \delta . \{\mu\} : \Delta . \{\mu\} @ n}$$

$$\frac{\mu : n \longrightarrow m \quad \Gamma \vdash \delta_0 : \Delta_0 @ m \quad \Delta_0 \vdash \delta_1 : \Delta_1 @ m}{\Gamma . \{\mu\} \vdash (\delta_1 \circ \delta_0) . \{\mu\} = \delta_1 . \{\mu\} \circ \delta_0 . \{\mu\} : \Delta_1 . \{\mu\} @ n} \quad \frac{\mu : n \longrightarrow m \quad \Gamma \mathsf{cx} @ m}{\Gamma . \{\mu\} \vdash \mathsf{id} . \{\mu\} = \mathsf{id} : \Gamma . \{\mu\} @ n}$$

$$\frac{\nu : o \longrightarrow n \quad \mu : n \longrightarrow m \quad \Gamma \mathsf{cx} @ m}{\Gamma . \{\mu \circ \nu\} = \Gamma . \{\mu\} . \{\nu\} \mathsf{cx} @ o}$$

$$\frac{\nu : o \longrightarrow n \quad \mu : n \longrightarrow m \quad \Gamma \vdash \delta : \Delta @ m}{\Gamma . \{\mu \circ \nu\} \vdash \delta . \{\mu\} . \{\nu\} = \delta . \{\mu \circ \nu\} : \Delta . \{\mu \circ \nu\} @ o}$$

$$\frac{\mu, \nu : n \longrightarrow m \quad \alpha : \nu \longrightarrow \mu \quad \Gamma \vdash \delta : \Delta @ m}{\Gamma . \{\mu\} \vdash \{\alpha\}_\Gamma : \Gamma . \{\nu\} @ n} \quad \frac{\mu : n \longrightarrow m \quad \Gamma \mathsf{cx} @ m}{\Gamma . \{\mu\} \vdash \mathsf{id} = \{\mathsf{id}\}_\Gamma : \Gamma . \{\mu\} @ n}$$

$$\frac{\Gamma, \Delta \mathsf{cx} @ m \quad \mu, \nu : n \longrightarrow m \quad \Gamma \vdash \delta : \Delta @ m \quad \alpha : \nu \longrightarrow \mu}{\Gamma . \{\mu\} \vdash \{\alpha\}_\Gamma \circ (\delta . \{\mu\}) = (\delta . \{\nu\}) \circ \{\alpha\}_\Delta : \Delta . \{\nu\} @ n}$$

$$\frac{\Gamma \mathsf{cx} @ m \quad \mu_0, \mu_1, \mu_2 : n \longrightarrow m \quad \alpha_0 : \mu_0 \longrightarrow \mu_1 \quad \alpha_1 : \mu_1 \longrightarrow \mu_2}{\Gamma . \{\mu_2\} \vdash \{\alpha_1 \circ \alpha_0\}_\Gamma = \{\alpha_0\}_\Gamma \circ \{\alpha_1\}_\Gamma : \Gamma . \{\mu_0\} @ n}$$

$$\frac{\Gamma \mathsf{cx} @ m \quad \nu_0, \nu_1 : o \longrightarrow n \quad \mu_0, \mu_1 : n \longrightarrow m \quad \beta : \nu_0 \longrightarrow \nu_1 \quad \alpha : \mu_0 \longrightarrow \mu_1}{\Gamma . \{\mu_1 \circ \nu_1\} \vdash \{\alpha \bullet \beta\}_\Gamma = \{\alpha\}_\Gamma . \{\nu_0\} \circ \{\beta\}_{\Gamma . \{\mu_1\}} : \Gamma . \{\mu_0 \circ \nu_0\} @ o}$$

Figure 1: Key rules for contexts and substitutions in MTT

Intuitively, $\Gamma . (\mu \mid A)$ plays the same role as $\Gamma . \langle \mu \mid A \rangle$ and comes equipped with a similar universal property: a substitution $\Delta \vdash \gamma : \Gamma . (\mu \mid A) @ m$ is precisely determined by a substitution $\Delta \vdash \gamma' : \Gamma @ m$ and a term $\Delta . \{\mu\} \vdash M : A [\gamma' . \{\mu\}] @ n$. The ordinary context extension $\Gamma . A$ is recovered by taking $\mu = \mathsf{id}$; the equation $\Gamma . \{\mathsf{id}\} = \Gamma$ ensures that the universal properties of $\Gamma . A$ and $\Gamma . (\mathsf{id} \mid A)$ match.

Despite the similarities between $\Gamma . (\mu \mid A)$ and $\Gamma . (\mathsf{id} \mid \langle \mu \mid A \rangle)$, they occupy different positions in the theory. The variable rule of MTT is adjusted to take into account modal annotations and require that the modalities in the context must cancel a variable's annotation:

$$\frac{\Gamma \mathsf{cx} @ m \quad \Gamma . \{\mu\} \vdash A @ n}{\Gamma . (\mu \mid A) . \{\mu\} \vdash \mathbf{v}_0 : A [\uparrow . \{\mu\}] @ n}$$

As in Martin-Löf type theory, it is necessary to apply a weakening substitution $\uparrow$ to $A$ when describing the type of $\mathbf{v}_0$. The normal variable rule arises again as a special case after setting $\mu = \mathsf{id}$. Note that attempting to state such a variable rule for $\Gamma . (\mathsf{id} \mid \langle \mu \mid A \rangle)$ would quickly introduce issues around substitution within the theory, so these two contexts behave quite differently in practice.

Remark 2.1. From the view of Fitch-style type theories where $- . \{\mu\}$ is left adjoint to the modal type, this rule plays the role of the counit; it allows us to pass from $L(R(A))$ to $A$.