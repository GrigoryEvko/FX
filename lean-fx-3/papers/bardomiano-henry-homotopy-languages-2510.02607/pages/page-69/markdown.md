### 4.3.1 Weak model for objects with weak cylinders

We start by fixing a weak model category $\mathcal{M}$ and let $J$ be the category

$$a \xrightarrow[j]{i} b \xrightarrow{k} c$$

such that $ki = kj$. Consider the degree function making $J$ into a direct category, $\deg(a) = 0$, $\deg(b) = 1$, $\deg(c) = 2$. Our first goal is to prove:

**Theorem 4.19.** *The category of diagrams $\mathcal{M}^J$ has a weak model structure where:*

1. *A map between diagrams $X \rightarrow Y$ is a cofibration if*

(a) *It is a Reedy cofibration,*
(b) $Y_a \sqcup_{X_a} X_c \xrightarrow{\sim} Y_c$ and $Y_b \sqcup_{X_b} X_c \xrightarrow{\sim} Y_c$ are trivial cofibrations in $\mathcal{M}$.

2. *Fibrations are level-wise fibrations.*

*Remark 4.20.* The theorem above make reference to Reedy cofibrations, therefore we must justify first that $\mathcal{M}^J$ carries the Reedy weak model structure. Fortunately, this has been addressed in theorem C.11.

*Notation 4.21.* For the sake of clarity, we denote by $\mathcal{M}^J_{Reedy}$ when referring to the Reedy weak model structure and $\mathcal{M}^J_{Loc}$ for the weak model structure of theorem 4.19. Of course, *a priori*, we have yet to prove that the latter is indeed a weak model structure. Therefore, whenever we say, for example, that a map $f : X \rightarrow Y$ is a cofibration we just mean that $f$ satisfies the corresponding condition of theorem 4.19.

We will justify that the following construction, which is simply the conditions of the theorem, is the correct one.

*Observation 4.22.* One can verify that in this new model structure, the core fibrations and core trivial cofibrations coincide with the ones in the Reedy weak model structure (see theorem 4.25).

The reader might suspect that this is not a fortuitous coincidence, these suspicions are well justified. As we mentioned, what we have done is a right Bousfield localization of a Reedy weak model structure on $\mathcal{M}^J$. Such localizations are studied in [Hen23] in the case when $\mathcal{M}$ is a combinatorial (accessible) weak model category. Due to the lack of a general theorem that justifies the existence of these localizations producing a weak model category, we verify all required conditions by hand.

69