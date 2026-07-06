CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

Now, remark that for any element \( e \in (A \star 1)_{n+1}^* \), there exists \( x \in (A \star 1)_n^* \) such that \( x \star 1 \leq e \) if and only if there exists \( y \in (A \star 1)_{n-1}^* \) such that \( y \star 1 \leq \partial^{+}(e) \). By a direct induction, this implies that there exists \( x \in (A \star 1)_n^* \) such that \( x \star 1 \leq e \) if and only if \( \partial_0^+(e) \in \mathbb{Z}[\emptyset \star 1] \).

Combined with the previous observation, this implies that for any element x of the basis of  \( A_{n+1} \) ,  \( \phi(x \star \emptyset) \)  is of shape  \( x' \star \emptyset \) . The automorphism  \( \phi \)  then induces by restriction an automorphism  \( \phi_{|A \star \emptyset}: A \to A \) , and the hypothesis implies that it is the identity.

We now show by induction on n that  \( \phi_{n}:(A\star1)_{n}\to(A\star1)_{n} \)  is the identity. Suppose the result true at the stage n. For any element x of the basis of  \( A_{n} \) , we then have

\[
\partial \phi (x \star 1) = \phi (\partial (x \star 1)) = \partial (x \star 1).
\]

By the definition of the derivative of  \( A \star 1 \) , and as  \( \phi \)  preserves the basis, this forces the equality  \( \phi(x \star 1) = x \star 1 \) . As we already know that for any element x of the basis of  \( A_{n+1} \)  we have  \( \phi(x \star \emptyset) = x \star \emptyset \) , this concludes the induction.

We then have \(\phi = id\) and \(A\star 1\) has no non trivial automorphisms. The case \(1^{\text{co}}\star A\) follows directly by using the fact that dualities preserve augmented directed complexes admitting no non-trivial automorphisms.

□

##### 1.2.2.9. We define the suspension as the functor

\[
[ \_, 1 ]: \mathrm{ADC} \to \mathrm{ADC}
\]

where \([K,1]\) is defined as the following pushout:

\[
\begin{array}{c} K \otimes \{0, 1 \} \longrightarrow K \otimes [ 1 ] \\ \Big \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text { (1.2.2.10) } \\ 1 \coprod 1 \longrightarrow [ K, 1 ] \end{array}
\]

We leave to the reader to check that \([K,1]\) admits a loop free and unitary basis when this is the case for \(K\). This functor then induces a functor:

\[
[ \_, 1 ]: \mathrm{ADC} _ {\mathrm{B}} \to \mathrm{ADC} _ {\mathrm{B}}
\]

##### 1.2.2.11. Unfolding the definition, we have

\[
[ (K, K ^ {\prime}, e), 1 ] := ([ K, 1 ], ([ K, 1 ]) ^ {*}, e)
\]

where

50