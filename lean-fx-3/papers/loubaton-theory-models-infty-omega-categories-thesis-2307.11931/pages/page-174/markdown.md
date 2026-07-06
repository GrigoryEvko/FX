CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

For an element \( f:[n_0] \star [n_1] \to [n] \) of \( \Delta_{/[n]}^2 \), we consider the morphism \( \phi_f:[K,n_1] \vee [K \otimes \lambda[n_0],1] \to [K,n] \star 1 \) as the unique morphism fulfilling

\[
\phi_ {f} ([ x, v _ {i, i + 1} ]) := [ x, v _ {f _ {0} (i), f _ {0} (i) + 1} ] \star \emptyset + \dots + [ x, v _ {f _ {0} (i) - 1, f _ {0} (i + 1)} ] \star \emptyset
\]

\[
\phi_ {f} ([ x \otimes v _ {i}, 1 ]) := 0
\]

\[
\phi_ {f} ([ x \otimes v _ {i, i + 1}, 1 ]) := [ x, v _ {f _ {1} (i), f _ {1} (i) + 1} ] \star 1 + \dots + [ x, v _ {f _ {1} (i) - 1, f _ {1} (i + 1)} ] \star 1
\]

for \( x \) an element of \( K \) and where we denote by \( f_0 \) and \( f_1 \) the induced morphisms \( [n_0] \to [n_0] \star [n_1] \to [n] \) and \( [n_1] \to [n_0] \star [n_1] \to [n] \).

Peforming this for any such \( f:[n_0] \star [n_1] \to [n] \) of \( \Delta_{/[n]}^2 \), this induces a morphism

\[
\psi : \underset {\Delta_ {/ [ n ]} ^ {2}} {\operatorname{colim}} [ [ n _ {0} ] \otimes a, 1 ] \vee [ a, n _ {1} ] \to 1 \star [ a, n ]
\]

whose restriction to \(\coprod_{k\leq n}\mathrm{colim}_{\Delta_{/ (k)}^2}[[n_0]\otimes a,1]\vee [a,n_1]\) factors through \(\coprod_{k\leq n}\mathrm{colim}_{\Delta_{/ (k)}^2}[[n_0],1]\vee [1,n_1]\) and this concludes the proof.

Lemma 3.4.1.3. There is an invertible natural transformation \(\mathrm{R}(e\star_{-})\to 1\star \mathrm{R}(\_)\) that firs in a commutative square

\[
\begin{array}{c} \operatorname{R} (\emptyset \star_ {-}) \longrightarrow \operatorname{R} (e \star_ {-}) \\ \stackrel {{i d}} {{\downarrow}} \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \emptyset \star \operatorname{R} (_ {-}) \longrightarrow 1 \star \operatorname{R} (_ {-}) \end{array}
\]

Proof. The lemma 3.4.1.2 provides such natural transformation. As R sends weak equivalences to isomorphisms, it is sufficient to show that  \( \mathrm{R}(e \star [K,1]) \to 1 \star [\mathrm{R}(K),1] \)  is an equivalence, which directly follows from the explicit description of these two objects provided by proposition 3.2.2.6 and by the example 3.2.2.4. □

Proposition 3.4.1.4. The following triangle commutes up to an invertible natural transformation

\[
\begin{array}{c} \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n}) \\ \xrightarrow {i ^ {n + 1}} \quad \Big \downarrow_ {\mathrm{R}} \\ \mathrm{tPsh} (\Delta) ^ {n + 1} \xrightarrow [ \mathrm{R} ]{} (0, \omega) \text {-cat} \end{array}
\]

For any integer \( k \leq n + 1 \), the induced morphism \( i^{n+1}(\mathrm{N}\mathbf{D}_k) \to \mathrm{N}(\mathbf{D}_k) \) is a weak equivalence.

Proof. It is sufficient to show the result for  \( n := \omega \) . The lemma 3.4.1.3 provides an invertible transformation  \( \phi : (\mathrm{R} i^{\omega})_{|\Delta} \to \mathrm{R}_{|\Delta} \)  which is natural when restricted to the full

164