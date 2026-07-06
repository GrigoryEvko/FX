2.3. SUSPENSION AND GRAY OPERATIONS

By two out of three, $i_{str}(K) \to i_{str}(L)$ is then an acyclic cofibration. The functor $i_{srt}$ is then left Quillen. $\square$

## 2.3 Suspension and Gray operations

### 2.3.1 Formula for the Gray cylinder

The aim of this subsection is to demonstrate the following theorem:

**Theorem 2.3.1.1.** *There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram*

$$[1] \vee \Sigma X \stackrel{\vee}{\leftarrow} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \stackrel{\vee}{\rightarrow} \Sigma X \vee [1]$$

and $(\Sigma X) \otimes [1]$.

**Construction 2.3.1.2.** Let $C$ be the following colimit:

$$\begin{array}{c} [3] \times \{0\} \coprod [3] \times \{1\} \longrightarrow [3] \times [1] \\ s^0 s^0 \coprod s^2 s^3 \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \coprod [1] \longrightarrow C. \end{array}$$

We define several marked simplicial sets whose underlying simplicial sets are sub objects of C:

$$\begin{array}{c c c} A_0 := & \begin{array}{c} 00 \longrightarrow 01 \\ \parallel \searrow \searrow \searrow \downarrow \\ 10 \longrightarrow 11 \end{array} & A_3 := & \begin{array}{c} 00 \longrightarrow 01 \\ \parallel \searrow \searrow \searrow \downarrow \\ 20 \longrightarrow 21 \end{array} \\ A_1 := & \begin{array}{c} \parallel \searrow \searrow \searrow \parallel \\ 20 \longrightarrow 21 \end{array} & \\ A_2 := & \begin{array}{c} 20 \longrightarrow 21 \\ \downarrow \searrow \searrow \parallel \\ 30 \longrightarrow 31 \end{array} & A_4 := & \begin{array}{c} 00 \longrightarrow 01 \\ \downarrow \searrow \searrow \searrow \downarrow \\ 30 \longrightarrow 31 \end{array} \end{array} \end{array}$$

where arrows labeled by $=$ are degenerate and simplices labeled by $\sim$ are thin.

Let $B_0$ be the sub object corresponding to the image of $[0, 1, 2] \times [0, 1]$ where the marking includes all cells of dimension $\le 2$, except $[10, 20, 21]$ and $[00, 20, 21]$.

Let $B_1$ be the sub object corresponding to the image of $[0, 2, 3] \times [0, 1]$ where the marking includes all cells of dimension $\le 2$, except $[00, 20, 21]$, $[00, 30, 31]$ and $[00, 20, 31]$.

Let $B$ be the reunion of $[0, 1, 2] \times [0, 1]$ and $[0, 2, 3] \times [0, 1]$ where the marking is the reunion of $B_0$ and $B_1$.

**Lemma 2.3.1.3.** *Morphisms $A_0 \cup A_1 \to B_0$ and $A_3 \to B_0$ are acyclic cofibrations.*

87