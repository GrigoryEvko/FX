**Theorem 4.36.** *There is a weak model structure $\mathcal{N}_{Loc}^{I}$ on the category of diagrams $\mathcal{N}^{I}$ obtained from the Reedy weak model structure $\mathcal{N}_{Reedy}^{I}$, where:*

1. *A map between diagrams $X \to Y$ is a cofibration if*

(a) *It is a Reedy cofibration,*
(b) $X_2 \sqcup_{X_1} Y_1 \xrightarrow{\sim} Y_2$ and $X_2 \sqcup_{X_0} Y_0 \xrightarrow{\sim} Y_2$ are trivial cofibrations in $\mathcal{N}$.

2. *Fibrations are level-wise fibrations.*

It will be useful to have in mind that for an object $X \in \mathcal{N}^{I}$ we have $L_0 X = 0$ and $L_1 X = X_0 \sqcup X_1$. So a map $X \to Y$ is a Reedy cofibration if the maps $X_0 \hookrightarrow Y_0$, $X_1 \hookrightarrow Y_1$ and $(Y_0 \sqcup Y_1) \sqcup_{(X_0 \sqcup X_1)} X_2 \hookrightarrow Y_2$ are cofibrations.
*Observation 4.37.* Unwinding the definitions, a diagram $X \in \mathcal{N}_{Loc}^{I}$ is cofibrant if both maps $X_0 \xrightarrow{\sim} X_2$ and $X_1 \xrightarrow{\sim} X_2$ are trivial cofibrations.

The proof of the theorem is completely analogous to theorem 4.19. We state the lemmas necessary for this and only comment on the proofs when adequate.

**Lemma 4.38.** *Let $X, Y \in \mathcal{N}_{Loc}^{I}$ cofibrant. Then, a map $X \to Y$ is a cofibration in $\mathcal{N}_{Loc}^{I}$ if and only if it is a cofibration in $\mathcal{N}_{Reedy}^{I}$.*

*Proof.* Just as in theorem 4.24 we only prove the interesting direction; assume that $X, Y$ are cofibrant in $\mathcal{N}_{Loc}^{I}$ and that $X \to Y \in \mathcal{N}_{Reedy}^{I}$ is a Reedy cofibration. Remains to show that

$$X_2 \sqcup_{X_0} Y_0 \to Y_2 \text{ and } X_2 \sqcup_{X_1} Y_1 \to Y_2$$

are trivial cofibrations. Again, the fact that the maps are weak equivalences follow from $X, Y$ being cofibrant and the 2-out-of-3 property. To see that they are cofibrations we can use the Reedy condition just as in theorem 4.24.

□

**Lemma 4.39.** *Let $X \in \mathcal{N}_{Loc}^{I}$ cofibrant and $X \to Z \in \mathcal{N}_{Reedy}^{I}$ a Reedy trivial cofibration. Then $Z$ is cofibrant in $\mathcal{N}_{Loc}^{I}$. Furthermore, $X \to Z$ is a trivial cofibration in $\mathcal{N}_{Loc}^{I}$.*

*Proof.* The difficult part is to show that $Z$ is cofibrant. Since $X \to Z$ is a Reedy trivial cofibration, then by theorem C.16 we have it is a levelwise trivial cofibration. Then $Z$ is cofibrant by the 2-out-of-3 property. □

82