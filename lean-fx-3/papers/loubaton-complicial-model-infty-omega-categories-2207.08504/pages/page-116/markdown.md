CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

**Proposition 3.2.1.4.** *The functor $e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ is a left Quillen functor.*

*Proof.* The proposition 3.2.1.3 implies that $e \star \_$ is pointwise weakly equivalent to the functor $\{0\} \coprod_{\{0\} \otimes \_} [1] \otimes \_$. As this last functor is a homotopy colimit of functors preserving weak equivalence, the functor $e \star \_$ also preserves them. As $e \star \_$ also preserves cofibrations, this concludes the proof. $\square$

**Construction 3.2.1.5.** Let $a$ be an object of $A$ and $l, m$ two integers. By construction, $e \star e[a, m]$ is a quotient of

$$P_{a,l,m} := \underset{[k_0,k_1] \to 1 \star [m]}{\operatorname{colim}} \underset{[k_2,k_3] \to [l] \otimes [k_1]}{\operatorname{colim}} [[k_2] \otimes [k_0] \otimes a, k_3]$$

while $e \star [a, m]$ is a quotient of

$$Q_{a,l,m} := \underset{[k_4,k_3] \to 1 \star [m]}{\operatorname{colim}} [[k_4] \otimes a, k_3].$$

Lemma 1.2.5.20 and the Gray module structure on $A$ then induce a morphism

$$P_{a,l,m} \to Q_{a,l,m}.$$

We can check that this morphism passes to the quotient and then induces a natural morphism

$$s^0 \star [a, n] : e \star e \star [a, n] \to e \star [a, n].$$

By extension by colimit, this induces, for any Segal $A$-category $C$, a morphism

$$s^0 \star C : e \star e \star C \to e \star C.$$

We can moreover check that this natural transformation between $e \star e \star \_$ and $e \star \_$ extends to stratified Segal $A$-categories. Finally, by construction and using the equality (1.2.5.21), we get a commutative square

$$\begin{array}{c} e \star e \star e \star C \xrightarrow{s^0 \star e \star C} e \star e \star C \\ e \star s^0 \star C \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star e \star C \xrightarrow{s^0 \star C} e \star C \end{array}$$

for any stratified Segal $A$-category $C$.

**Proposition 3.2.1.6.** *The stratified Segal $A$-precategory $e \star [a, 1]$ is the colimit of the diagram*

$$[e \star a, 1] \xleftarrow{[d^0 \star a, 1]} [a, 1] \xrightarrow{[a, d^1]} [e, 1] \vee [a, 1]$$

*and the stratified Segal $A$-precategory $e \star [e, 1]_t$ is the colimit of the diagram*

$$[[1]_t, 1] \xleftarrow{[d^0 \star e, 1]} [e, 1] \xrightarrow{[e, d^1]} [e, 1] \vee [e, 1]_t$$

*Proof.* We recall that $e \star a$ is the object of $A$ fitting in the following cocartesian square

$$\begin{array}{c} \{0\} \otimes a \longrightarrow [1] \otimes a \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow e \star a \end{array}$$

The results then directly follow from the construction of the functor $e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ and from proposition 1.2.5.17. $\square$

116