5.1. MARKED \((\infty, \omega)\)-CATEGORIES

5.1.1.14. A marked  \( (\infty,\omega) \) -category is a tW-local stratified  \( \infty \) -presheaves on  \( \Theta \) . We denote by  \( (\infty,\omega) \) -cat \( _{m} \)  the  \( (\infty,1) \) -category of marked  \( (\infty,\omega) \) -categories. Unfolding the definition, a marked  \( (\infty,\omega) \) -category is a pair  \( (C,tC) \)  where C is an  \( (\infty,\omega) \) -category and  \( tC := (tC_{n})_{n>0} \)  is a sequence of full sub  \( \infty \) -groupoids of  \( C_{n} \) , containing identities, stable by composition and by whiskering with cells of lower dimension. A n-cell  \( a : D_{n} \to (C,tC) \)  is marked if it belongs to the image of  \( tC_{n} \) .

There are two obvious ways to mark a  \( (\infty,\omega) \) -category. For  \( C\in(\infty,\omega) \) -cat, we define  \( C^{\sharp}:=(C,(C_{n})_{n>0}) \)  and  \( C^{\flat}:=(C,(\mathbb{I}(C_{n-1})_{n>0})) \) . The first one corresponds to the case where all cells are marked, and the second one where only the identities are marked. These two functors fit in the following adjoint triple:

\[
(\_) ^ {\flat}: (\infty , \omega) \text {-cat} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat} _ {\mathrm{m}}: (\_) ^ {\natural} \qquad (\_) ^ {\natural}: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \xrightarrow [ \leftarrow ]{\perp} (\infty , \omega) \text {-cat}: (\_) ^ {\sharp}
\]

where  \( (\_)^{\sharp} \)  is the obvious forgetful functor. To simplify notations, for a marked  \( (\infty,\omega) \) -category C, the marked  \( (\infty,\omega) \) -categories  \( (C^{\sharp})^{\flat} \)  and  \( (C^{\sharp})^{\sharp} \)  will be simply denoted by  \( C^{\flat} \)  and  \( C^{\sharp} \) .

5.1.1.15. Following paragraph 4.2.1.54, for any subset \(S\) of \(\mathbb{N}^*\), we define the duality

\[
(\_) ^ {S}: (\infty , \omega) \text {-cat} _ {\mathrm{m}} \to (\infty , \omega) \text {-cat} _ {\mathrm{m}}
\]

whose value on  \( (C,tC) \)  is  \( (C^{S},tC) \) . In particular, we have the odd duality  \( (\_)^{op} \) , corresponding to the set of odd integer, the even duality  \( (\_)^{co} \) , corresponding to the subset of non negative even integer, the full duality  \( (\_)^{\circ} \) , corresponding to  \( N^{*} \)  and the transposition  \( (\_)^{t} \) , corresponding to the singleton  \( \{1\} \) . Eventually, we have equivalences

\[
((\_) ^ {c o}) ^ {o p} \sim (\_) ^ {\circ} \sim ((\_) ^ {o p}) ^ {c o}.
\]

5.1.1.16. Given a functor \( F: I \to (\infty, \omega) \)-cat\(_m\), the colimit of \( F \) is given by the marked \( (\infty, \omega) \)-category \( (C, tC) \) with

\[
C := \underset {I} {\operatorname{colim}} F ^ {\natural}
\]

and for any \(n\), \((tC)_n\) is the image of the morphism

\[
\underset {I} {\operatorname{colim}} t F _ {n} \to (\underset {I} {\operatorname{colim}} F) _ {n} ^ {\natural}.
\]

The case of the limit is easier as we have

\[
\lim _ {I} F := (\lim _ {I} F ^ {\natural}, (\lim _ {I} (t F _ {n}) _ {n > 0}).
\]

In particular, if  \( (C,tC) \)  and  \( (D,tD) \)  are two marked  \( (\infty,\omega) \) -categories, we have

\[
(C, t C) \times (D, t D) := (C \times D, (t C _ {n} \times t D _ {n}) _ {n > 0}).
\]

237