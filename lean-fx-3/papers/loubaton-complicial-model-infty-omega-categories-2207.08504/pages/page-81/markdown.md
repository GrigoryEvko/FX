2.3. SUSPENSION AND GRAY OPERATIONS

- $D_2 = D_1 \cup [20, 30, 31]$ ;
- $D_3 = D_2 \cup [20, 21, 31]$ ;
- $D_4 = D_3 \cup [00, 01, 21, 31]$ ;
- $D_5 = D_4 \cup [00, 20, 30, 31]$ ;
- $D_6 = D_5 \cup [00, 20, 21, 31]$ ;

and

- $(D_0, M_0) \to (D_1, M_1)$ is a pushout of $\Lambda^2[2] \to [2]^2$ ;
- $(D_1, M_1) \to (D_2, M_2)$ is a pushout of $\Lambda^1[2] \to [2]^1$ ;
- $(D_2, M_2) \to (D_3, M_3)$ is a pushout of $\Lambda^2[2] \to [2]^2$ ;
- $(D_3, M_3) \to (D_4, M_4)$ is a pushout of $\Lambda^3[3] \to [3]^3$ ;
- $(D_4, M_4) \to (D_5, M_5)$ is a pushout of $\Lambda^2[3] \to [3]^2$ ;
- $(D_5, M_5) \to (D_6, M_6)$ is a pushout of $\Lambda^3[3] \to [3]^3$ .

Lemma 2.3.1.5. The maps $A_0 \cup A_1 \cup A_2 \to B$ and $A_4 \to B$ are acyclic cofibrations.

Proof. This is a direct consequence of the last two lemmas.

Construction 2.3.1.6. The marked simplicial set $\overline{X \otimes B}$ is the pushout:

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes B}. \end{array}$$

Let $\overline{X \otimes A_i}$ and $\overline{X \otimes B_i}$ be the sub-objects of $\overline{X \otimes B}$ corresponding to image of $X \otimes A_i$ and $X \otimes B_i$.

Lemma 2.3.1.7. The inclusion $\overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \to \overline{X \otimes B}$ and $\overline{X \otimes A_4} \to \overline{X \otimes B}$ are acyclic cofibrations.

Proof. Remark that we have cocartesian squares

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes A_0 \cup X \otimes A_1 \cup X \otimes A_2 \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \longrightarrow \overline{X \otimes B} \end{array}$$

and

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes A_4 \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes A_4} \longrightarrow \overline{X \otimes B} \end{array}$$

The result then follows from lemma 2.3.1.5.

Lemma 2.3.1.8. The morphisms $\overline{X \otimes A_0} \to [1] \vee \Sigma X$ and $\overline{X \otimes A_2} \to \Sigma X \vee [1]$, induced by the morphism $A_0 \to [00, 01, 11]_t$ and $A_2 \to [20, 30, 31]_t$, are acyclic cofibrations.

81