CHAPTER 2. STUDY OF COMPLICIAL SETS

Proof. We have cocartesian squares

$$\begin{array}{c} X \otimes ([00, 01] \coprod \{11\}) \longrightarrow X \otimes [00, 01] \coprod_{X \otimes [01]} X \otimes [01, 11] \xrightarrow{\sim} X \otimes A_0 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod \{11\} \xrightarrow{\quad} [1] \coprod_{[0]} \Sigma X \xrightarrow{\sim} \overline{X \otimes A_0} \end{array}$$

That shows that $[1] \coprod_{[0]} \Sigma X \to \overline{X \otimes A_0}$ is an acyclic cofibration. We then have a commutative diagram:

$$[1] \coprod_{[0]} \Sigma X \xrightarrow{\sim} \overline{X \otimes A_0} \longrightarrow [1] \vee \Sigma X$$

and by two out of three, this shows that $\overline{X \otimes A_0} \to [1] \vee \Sigma X$ is an acyclic cofibration. We proceed similarly for the second morphism.

Lemma 2.3.1.9. Marked simplicial sets $\overline{X \otimes A_1}$ and $\overline{X \otimes A_4}$ are respectively equal to $\Sigma(X \otimes [1])$ and $(\Sigma X) \otimes [1]$.

Proof. This is true by the definition of these objects.

Proof of theorem 2.3.1.1. According to lemma 2.3.1.9 we have a cocartesian square

$$\begin{array}{c} \overline{X \otimes A_0} \coprod \overline{X \otimes A_2} \longrightarrow \overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \vee \Sigma X \coprod \Sigma X \vee [1] \longrightarrow [1] \vee \Sigma X \coprod_{\Sigma(X \otimes \{0\})} \Sigma(X \otimes [1]) \coprod_{\Sigma(X \otimes \{1\})} \Sigma X \vee [1] \end{array}$$

The left vertical morphism is a weak equivalence according to lemma 2.3.1.8, and the horizontal morphisms are cofibrations. By left properness, the right vertical morphism is a weak equivalence. Combined with lemmas 2.3.1.7 and 2.3.1.9, this provides a zigzag of weak equivalences between $[1] \vee \Sigma X \coprod_{\Sigma(X \otimes \{0\})} \Sigma(X \otimes [1]) \coprod_{\Sigma(X \otimes \{1\})} \Sigma X \vee [1]$ and $(\Sigma X) \otimes [1]$.

### 2.3.2 Formulas for the Gray cone and the Gray o-cone

The aim of this subsection is to demonstrate the following theorem, which is the analogue in stratified simplicial sets of the theorem 1.2.4.14.

Theorem 2.3.2.1. There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram

$$\Sigma X \vee [1] \leftarrow \Sigma X \rightarrow \Sigma([0] \stackrel{co}{\star} X)$$

and $\Sigma X \star [0]$.

There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram

$$\Sigma(X \star [0]) \leftarrow \Sigma X \rightarrow [1] \vee \Sigma X$$

and $[0] \stackrel{co}{\star} \Sigma X$.

82