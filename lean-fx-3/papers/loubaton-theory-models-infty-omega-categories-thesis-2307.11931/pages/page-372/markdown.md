CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**Corollary 6.2.4.6.** Let $A, B$ and $C$ be three $\mathbf{U}$-small $(\infty, \omega)$-categories with $B$ lax $\mathbf{U}$-cocomplete, and $i : A \to C$ and $f : A \to B$ two functors. The left Kan extension of $i$ along $f$ is given by the composite functor.

$$B \xrightarrow{N_f} \widehat{A} \xrightarrow{i_!} \widehat{C} \xrightarrow{\text{laxcolim}} C$$

*Proof.* We have a sequence of equivalences

$$\begin{array}{l} \operatorname{hom}_{\underline{\operatorname{Hom}}(C, B)}(\text{laxcolim } \circ i_! \circ N_f, h) \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(C, \widehat{A})}(N_f, i^* \circ y^B \circ h) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{A})}(y^A, i^* \circ y^B \circ h \circ f) \quad (6.2.4.3) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(i_! \circ y^A, y^B \circ h \circ f) \quad (6.2.2.7) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(y^B \circ i, y^B \circ h \circ f) \quad (6.2.3.3) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, B)}(i, h \circ f) \quad (6.2.1.16) \end{array}$$

natural in $h : \underline{\operatorname{Hom}}(C, B)$.

362