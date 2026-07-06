CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

5.1.1.10. For a stratified  \( \infty \) -presheaf X on  \( \Delta[\Theta] \) , we denote by  \( tX_{1} \)  the  \( \infty \) -groupoid  \( X([1]^{\sharp}) \) , and for any n > 1, we denote by  \( tX_{n} \)  the  \( \infty \) -groupoid  \( X((\mathbf{D}_{n})_{t}) \) .

A stratified  \( \infty \) -presheaf on  \( \Delta[\Theta] \)  is then the data of a pair  \( (X,tX) \)  such that  \( X\in\mathrm{Psh}^{\infty}(\Delta[\Theta]) \)  and  \( tX:=(tX_{n})_{n>0} \)  is a sequence of  \( \infty \) -groupoid such that for any n>0,  \( tX_{n} \)  is a full sub  \( \infty \) -groupoid of  \( X_{n} \)  including all units.

For  \( X \in \mathrm{Psh}^{\infty}(\Delta[\Theta]) \) , we define once again  \( X^{\sharp} := (X, (X_{n})_{n>0}) \)  and  \( X^{\flat} := (X, (\mathbb{I}(X_{n-1}))_{n>0}) \)  and we still have an adjoint triple

\[
(\_) ^ {\sharp} \mathrm{Psh} ^ {\infty} (\Delta [ \Theta ]) \underset {\leftarrow} {\longrightarrow} \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]): (\_) ^ {\sharp} \qquad (\_) ^ {\sharp}: \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]) \underset {\leftarrow} {\longrightarrow} \mathrm{Psh} ^ {\infty} (\Delta [ \Theta ]): (\_) ^ {\sharp}
\]

where  \( (\_)^{\sharp} \)  is the obvious forgetfull functor.

5.1.1.11. We once again have an adjunction:

\[
i _ {!}: \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]) \xrightarrow [ \longleftarrow ]{} \mathrm{tPsh} ^ {\infty} (\Theta): i ^ {*}
\]

induced by the canonical inclusion  \( t\Delta[t\Theta]\to t\Theta \) . For an integer n, we define the functor  \( (\_)^{\sharp_{n}}:\mathrm{Psh}^{\infty}(\Theta)\to\mathrm{tPsh}^{\infty}(\Theta) \)  and  \( (\_)^{\sharp_{n}}:\mathrm{Psh}^{\infty}(\Delta[\Theta])\to\mathrm{tPsh}^{\infty}(\Delta[\Theta]) \)  sending a  \( \infty \) -presheaf X onto  \( (X,(X_{k}^{n})_{k>0}) \)  where  \( X_{k}^{n}:=\mathbb{I}(X_{k-1}) \)  if k<n, and  \( X_{k}^{n}:=X_{k} \)  if not. We eventually set

\[
\mathrm{tW} := \coprod_ {n} (\mathrm{W} _ {\mathrm{Seg}}) ^ {\sharp_ {n}} \coprod (\mathrm{W} _ {\mathrm{Sat}}) ^ {\flat} \qquad \mathrm{tM} := \coprod_ {n} (\mathrm{M} _ {\mathrm{Seg}}) ^ {\sharp_ {n}} \coprod (\mathrm{M} _ {\mathrm{Sat}}) ^ {\flat}
\]

As  \( i_{!}(tM) \)  is contained in tW, the previous adjunction induces a derived one:

\[
\mathbf {L} i _ {!}: \mathrm{tPsh} ^ {\infty} (\Delta [ \Theta ]) _ {\mathrm{tM}} \xrightarrow [ \leftarrow ]{\longrightarrow} \mathrm{tPsh} ^ {\infty} (\Theta) _ {\mathrm{tW}}: i ^ {*} \mathbf {R} \tag {5.1.1.12}
\]

Proposition 5.1.1.13. The derived adjunction (5.1.1.12) is an adjoint equivalence.

Proof. It is enough to show that for any element \( a: t\Delta[t\Theta] \) and any \( b: t\Theta \), \( a \to i^{*}i_{!}a \) and \( i_{!}i^{*}b \to b \) are respectively in \( \widehat{\mathrm{tM}} \) and \( \widehat{\mathrm{tW}} \). If \( a \) is of shape \( [b, n]^{\flat} \), this is a direct consequence of proposition 4.2.1.5, and if \( a \) is \( (\mathbf{D}_n)_t \) the unit is the identity. We proceed similarly for \( i_{!}i^{*}b \to b \).

The inclusion  \( t\Theta \rightarrow (0, \omega) \) -cat \( _{m} \)  induces an adjunction

\[
\mathrm{tPsh} (\Theta) \xrightarrow [ \longleftarrow ]{\longrightarrow} (0, \omega) \text {-cat} _ {\mathrm{m}}
\]

and we can easily check that this induces an equivalence between  \( (0,\omega) \) -cat \( _{m} \)  and the sub-category of tPsh( \( \Theta \) ) of tW-local objects. Together with proposition 5.1.1.13, this induces equivalences

\[
\mathrm{tPsh} (\Theta) _ {\mathrm{tM}} \cong \mathrm{tPsh} (\Delta [ \Theta ]) _ {\mathrm{tW}} \cong (0, \omega) \mathrm{-cat} _ {\mathrm{m}}
\]

236