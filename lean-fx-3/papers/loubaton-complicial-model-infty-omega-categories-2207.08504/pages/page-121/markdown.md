3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

As the proposition 3.2.1.6 implies that the colimit of the the diagram 3.2.3.9 is equivalent to the one of the diagram given in the statement, this concludes the proof. □

**Lemma 3.2.3.10.** *The morphism*

$$[e, 1] \vee (e \star [a, 1]) \cup e \star [e \star a, 1] \rightarrow [e, 1] \vee (e \star [e \star a, 1])$$

*is a weak equivalence.*

*Proof.* We have a cocartesian square

$$\begin{array}{c} [e, 1] \cup e \star [a, 1] \xrightarrow{[e, 1] \cup e \star [d^0 \star a, 1]} [e, 1] \cup e \star [e \star a, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \vee (e \star [a, 1]) \longrightarrow [e, 1] \vee (e \star [a, 1]) \cup e \star [e \star a, 1] \end{array} \tag{3.2.3.11}$$

Remark that the left vertical morphism is the vertical colimit and homotopy colimit of the diagram

$$\begin{array}{c} [e, 1] \cup [e \star a, 1] \longleftarrow [e, 1] \cup [a, 1] \longrightarrow [e, 1] \cup [e, 1] \vee [a, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \vee [e \star a, 1] \longleftarrow [e, 1] \vee [a, 1] \longrightarrow [e, 2] \vee [a, 1] \end{array}$$

and is then a weak equivalence. This implies that the right vertical morphism of (3.2.3.11) is a weak equivalence. Similarly, $[e, 1] \cup e \star [e \star a, 1] \rightarrow [e, 1] \vee (e \star [e \star a, 1])$ is a weak equivalence. By two out of three this concludes the proof. □

**Lemma 3.2.3.12.** *The morphism $\{1\} \star [0] \rightarrow [1]_t \star [0]$ is an acyclic cofibration.*

*Proof.* Using proposition 3.2.1.6 we deduce that $[1]_t \star [0]$ is the colimit of the diagram

$$[[1]_t, 1] \longleftarrow [e, 1] \longrightarrow [e, 1]_t \vee [e, 1]$$

The inclusion $\{1\} \star [0] \rightarrow [1]_t \star [0]$ is then the composite of the following sequence

$$\begin{array}{c} [e, 1] \xrightarrow{[d^0, 1]} [[1]_t, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \xrightarrow{[e, d^0]} [e, 1]_t \vee [e, 1] \longrightarrow [1]_t \star [0] \end{array}$$

As the morphism $[e, d^0]$ and $[d^0, 1]$ are acyclic cofibrations, this concludes the proof. □

**Lemma 3.2.3.13.** *The morphism $\{1\} \star [a, 1] \rightarrow [1]_t \star [a, 1]$ is an acyclic cofibration.*

*Proof.* The Segal $A$-precategory $[1]_t \star [a, 1]$ is the colimit and the homotopy colimit of the diagram

$$\begin{array}{c} [1] \star \emptyset \\ \downarrow \\ [1]_t \star \emptyset \end{array} \xrightarrow{\quad} \begin{array}{c} [[1] \star a, 1] \\ \downarrow \\ [1] \star [a, 1] \end{array} \xleftarrow{\quad} \begin{array}{c} [[1]_t \star a, 1] \\ \downarrow \\ [[1]_t \star a, 1] \end{array}$$

The lemma 3.2.3.3 then implies that we have a weak equivalence from $[1]_t \star [a, 1]$ to the colimit, denoted by $K$, of the diagram

$$[[1]_t \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1]_t \vee (e \star [a, 1])$$

121