254

Cohesive parametric type theory

Proposition 14.3.21 (Components-discrete adjunction).

$$\frac{\Gamma'.cc \gg \gamma = \gamma' \in \Gamma @ pt}{\Gamma' \gg \gamma = \gamma' \in \Gamma.dsc @ par}$$

$$\frac{\Gamma' \gg \gamma = \gamma' \in \Gamma.dsc @ par}{\Gamma'.cc \gg \gamma = \gamma' \in \Gamma @ pt}$$

Proof. Following the proof of Lemma 14.3.8.

Proposition 14.3.22 (Discrete-global adjunction).

$$\frac{\Gamma'.dsc \gg \gamma = \gamma' \in \Gamma @ par}{\Gamma' \gg \gamma = \gamma' \in \Gamma.glo @ pt}$$

$$\frac{\Gamma' \gg \gamma = \gamma' \in \Gamma.glo @ pt}{\Gamma'.dsc \gg \gamma = \gamma' \in \Gamma @ par}$$

Proof. Following the proof of Lemma 14.3.9.

Proposition 14.3.23 (Stability/composition of substitutions). If $\Gamma'' \gg \gamma'' = \gamma''' \in \Gamma' @ m$ and $\Gamma' \gg \gamma = \gamma' \in \Gamma @ m$, then $\Gamma'' \gg \gamma''\gamma = \gamma'''\gamma' \in \Gamma @ m$.

Proof. Following the proof of Proposition 14.3.18, using the action of modalities on substitutions and stability of open typing judgments in the modal hypothesis case.

## 14.4 Modal types

With the judgmental apparatus sorted, we now construct a specific type system with types corresponding to the discrete, global, and codiscrete cohesion functors.

To avoid repetition, we introduce a uniform notation for modal types: we write $\langle \mu | A \rangle$ for the type corresponding to the right adjoint of each $\mu \in \{cc, dsc, glo\}$. Thus we have the following encodings.

$$Disc(A) := \langle cc | A \rangle$$

$$Glo(A) := \langle dsc | A \rangle$$

$$Codisc(A) := \langle glo | A \rangle$$

This notation reflects the role of the left adjoint in the intended introduction rule for each modal type.

$$\frac{\Gamma.\mu \gg M \in A}{\Gamma \gg mod(M) \in \langle \mu | A \rangle}$$

Note also the parallel with the modal hypothesis notation ($\mu \mid a : A$). We display the operational semantics rules for modal types in Figures 14.4 and 14.5.

It will be useful to first give names to the relations that will interpret these types.