CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

The following are equivalent.

(1) The functor \( u \) admits a right adjoint.
(2) For any element \( b \) of \( D \), the marked \( (\infty, \omega) \)-category \( (C^t)_{b/}^{\sharp} \) admits an initial element.

Similarly, the following are equivalent.

(1)' The functor \( u \) admits a left adjoint.
(2)' For any element \( b \) of \( D \), \( C_{b/}^{\sharp} \) admits an initial element.

Proof. Suppose first that (1) is fulfilled, and let  \( v : D \to C \)  be a functor and  \( \phi : \hom(u(a), b) \sim \hom(a, v(b)) \)  be an invertible natural transformation. In particular, this implies that we have an equivalence

\[
\int_ {C ^ {t} \times D} \hom_ {D} (u (a), b) \sim \int_ {C ^ {t} \times D} \hom_ {C} (a, v (b))
\]

Pulling back along \( C^t \times \{b\} \) where \( b \) is any object of \( D \), we get an equivalence between \( (C^t)_{b/}^{\sharp} \) and \( (C^t)_{v(b)/}^{\sharp} \). As this last marked \( (\infty, \omega) \)-category admits an initial element, given by the image \( id_{v(b)} \), this shows the implication \( (1) \Rightarrow (2) \).

For the converse, suppose that \( u \) fulfills condition (2). The functor \( \mathrm{hom}_D(u(\_), \_) : C^t \times D \to \underline{\omega} \) corresponds by adjonction to a functor \( v' : D \to \widehat{C} \). By assumption, for any \( b \in B \), \( v'(b) \) is a representable \( (\infty, \omega) \)-presheaf. The Yoneda lemma then implies that \( v \) factors through a functor \( v : D \to C \). Using once again Yoneda lemma, we have a sequence of equivalences

\[
\hom_ {D} (u (a), b) \sim v ^ {\prime} (b) (a) \sim \hom_ {C} (b, v (a)).
\]

The equivalence between  \( (1)' \)  and  \( (2)' \)  is proved similarly.

□

6.2.2.3. Let  \( (u,v,\phi) \)  be an adjoint structure. There is a transformation

\[
\hom_ {C} (a, a ^ {\prime}) \to \hom_ {D} (u (a), u (a ^ {\prime})) \to \hom_ {C} (a, v u (a ^ {\prime}))
\]

natural in  \( a : C^{t} \) ,  \( a' : C \) . According to the Yoneda lemma, this corresponds to a natural transformation  \( \mu : id_{C} \to vu \) , called the unit of the adjunction. Similarly, the natural transformation:

\[
\hom_ {D} (b, b ^ {\prime}) \to \hom_ {C} (v (b), v (b ^ {\prime})) \to \hom_ {C} (u v (b), b ^ {\prime})
\]

induces a natural transformation \(\epsilon : uv \to id_D\), called the counit of the adjunction.

344