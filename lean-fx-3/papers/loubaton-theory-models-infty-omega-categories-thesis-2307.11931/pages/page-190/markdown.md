CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

By hypothesis, this square admits a lift $l : c \to b$, that we factorize in a morphism $r' \in L$ followed by a morphism $p' \in R$. The commutativity of the lower triangle implies equivalences $pl' \sim pp'r' \sim id$, and by unicity, $r' \sim id$ and $pp' \sim id$. The lift $l$ is equivalent to $p'$ and is then in $R$. The commutativity of the upper triangle implies $lf \sim lpi \sim i$ and by unicity again, $p'p \sim id$. The morphism $p$ is then an isomorphism, this implies that $f \sim i$, and $f$ is then in $L$. We proceed similarly for the dual assertion. □

**Proposition 4.1.2.10.** *A morphism is in $L$ (resp. in $R$) if and only if it has the unique left lifting property against morphisms of $R$ (resp. the unique right lifting property against the morphisms of $R$).*

*Proof.* This is the content of lemma 4.1.2.8 and 4.1.2.9.

**Proposition 4.1.2.11.** *The forgetful functor from the $(\infty,1)$-category of squares with lifts, and whose left (resp. right) vertical morphism is in $L$ (resp. in $R$), to the $(\infty,1)$-category of squares whose left (resp. right) vertical morphism is in $L$ (resp. in $R$), is an equivalence.*

*Roughly speaking, the formation of the lift in squares whose left (resp. right) vertical morphism is in $L$ (resp. in $R$) is functorial.*

*Proof.* The $(\infty,1)$-category of squares with lifts, and whose left (resp. right) vertical morphism is in $L$ (resp. in $R$), is the $(\infty,1)$-category

$$
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C)
$$

and the $(\infty,1)$-category whose left (resp. right) vertical morphism is in $L$ (resp. in $R$) of squares is the limit of the diagram

$$
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) \xrightarrow{\nabla} \operatorname{Arr}(C) \xleftarrow{\nabla} \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C)
$$

The forgetful functor is induced by the commutative diagram

$$
\begin{array}{ccc}
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C) & \xrightarrow{\nabla \times_C \operatorname{Arr}_R(C)} & \operatorname{Arr}(C) \times_C \operatorname{Arr}_R(C) \\
\operatorname{Arr}_L(C) \times_C \nabla \downarrow & & \downarrow \nabla \\
\operatorname{Arr}_L(C) \times_C \operatorname{Arr}(C) & \xrightarrow{\nabla} & \operatorname{Arr}(C)
\end{array}
$$

and we then have to show that it is cartesian.

By definition of factorization system, the morphism

$$
\nabla : \operatorname{Arr}_L(C) \times_C \operatorname{Arr}_R(C) \to \operatorname{Arr}(C)
$$

180