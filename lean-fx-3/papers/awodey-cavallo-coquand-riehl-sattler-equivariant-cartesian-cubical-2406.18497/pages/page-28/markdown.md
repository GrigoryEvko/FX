3.2. **Brown factorizations.** The structure of a cylindrical premodel structure is designed to provide fibred mapping cylinder and mapping path space factorizations that are stable under coslicing and slicing, respectively. In this section, we focus on the mapping path space construction, which we call the “Brown factorization” after [Bro73], which will be used in the next section to establish the equivalence extension property.

**Construction 3.2.1.** Given a map $f: Z \rightarrow Y$ in a cylindrical premodel category, its **Brown factorization** $f = p_f \cdot s_f$ is constructed by factoring the graph of $f$ as follows:

$$\begin{array}{c} Z \xrightarrow{f} Y \\ (1,f) \left( \begin{array}{c} \downarrow s_f \\ \downarrow \\ Bf \xrightarrow{f \times Y} PY \\ \downarrow (q_f, p_f) \end{array} \right) \\ Z \times Y \xrightarrow{f \times Y} Y \times Y. \end{array}$$

By construction $f = p_f \cdot s_f$ and $1 = q_f \cdot s_f$.

**Lemma 3.2.2.** *For the Brown factorization of a map $f: Z \rightarrow Y$ in a cylindrical premodel category,*

$$\begin{array}{c} q_f \xrightarrow{f} Bf \\ \downarrow \xrightarrow{s_f} y \\ Z \xrightarrow{f} Y, \end{array}$$

- (i) If $Y$ is fibrant, then $(q_f, p_f): Bf \rightarrow Z \times Y$ is a fibration.
- (ii) If $Y$ is fibrant, then $q_f: Bf \rightarrow Z$ is a trivial fibration.
- (iii) If $Y$ and $Z$ are both fibrant, then $p_f: B_f \rightarrow Y$ is a fibration.

*Proof.* These maps arise as

$$\begin{array}{c} Bf \longrightarrow PY \\ q_f \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \\ Z \xrightarrow{f} Y, \end{array}$$

If $Y$ is fibrant, then by Definition 3.1.8, $\partial: PY \rightarrow Y \times Y$ is a fibration and $\partial_0: PY \xrightarrow{\sim} Y$ is a trivial fibration, proving the first two statements. If $Z$ is fibrant, then the projection $\pi: Z \times Y \rightarrow Y$ is a fibration as well, proving the third statement. $\square$

*Remark 3.2.3.* By Lemma 3.1.9, Construction 3.2.1 can be implemented in slice categories. Given a map $f: Z \rightarrow Y$ lying over $X$ via $g: Y \rightarrow X$, the **fibred Brown factorization** is defined by implementing the Brown factorization construction in the slice over $X$. This factors the graph of $f$, regarded as a morphism with codomain $Z \times_X Y$, through a pullback of the fibred path object as

28