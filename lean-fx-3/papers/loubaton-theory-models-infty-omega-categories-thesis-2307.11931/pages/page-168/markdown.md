CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. Suppose first that we are in the first case of the definition 3.3.3.6. We can then suppose without loss of generality that \( C = [a,2] \). We define \( \tilde{x} := \epsilon_a \circ [d^0 \otimes a,1] \). Diagram (6).3.3.3.2 and lemma 3.3.3.11 imply that \( (\tilde{x},\bar{y}) \geq_{n+1} \bar{z} \). Eventually, diagrams (3).3.3.3.2 and (5).3.3.3.2 induce a diagram:

\[
\begin{array}{c} [ e \star a, 1 ] \xrightarrow {[ e \star a , d ^ {2} ]} [ e \star a, 1 ] \vee [ a, 1 ] \xleftarrow {[ [ 1 ] \otimes a , d ^ {1} ]} [ [ 1 ] \otimes a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {2} ] ]{} e \star [ a, 2 ] \xleftarrow [ \epsilon_ {a} ]{} [ [ 2 ] \bar {\otimes} a, 1 ] \end{array}
\]

wich implies that \(\bar{x} \geq_{n+1} \tilde{x}\).

If we are in the second case of the definition, it is a direct consequence of the naturality of  \( \alpha \) , of the definition of n-reliability and of the fact that  \( (e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}} \)  as remarked in paragraph 3.3.2.1.

Lemma 3.3.3.15. For any \(a\) such that \(\tau_{n}^{i}a = a\) and \(x:[a,1]\to C\), if we denote by \(\bar{x} := e\star x\circ d^0\star [a,1]\) and \(\tilde{x} := e\star x\circ \alpha_a\circ [d^0\star a,1]\), then \(\bar{x}\geq_{n + 1}\tilde{x}\).

Proof. Using the diagrams (1).3.3.3.2 and (2).3.3.3.2, we have a diagram:

\[
\begin{array}{c} [ a, 1 ] \xrightarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \\ [ a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \alpha_ {a} \\ [ e, 1 ] \vee [ a, 1 ] \xrightarrow {\beta_ {a}} e \star [ a, 1 ] \xrightarrow {e \star x} C \\ [ a, d ^ {0} ] \Big \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ a, 1 ] \end{array}
\]

which implies the desired inequality.

3.3.3.16. We now use these results to show that the thinness extensions are weak equivalences. We define by induction the morphism  \( \iota_{n}:[[n-1],1]\to[n] \)  where  \( \iota_{2}:=\alpha_{[0]} \)  and  \( \iota_{n+1}:=e\star\iota_{n}\circ\alpha_{[n-1]} \) .

We can easily show by induction that \([n]\) is a colimit of terms which are all invariant under \(\tau_{n - 1}^{i}\) except the one corresponding to \(\iota_{n}\). For any \(n\) we then have a pushout square:

\[
\begin{array}{c} [ [ n - 1 ], 1 ] \xrightarrow {\iota_ {n}} [ n ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ [ n - 1 ] _ {t}, 1 ] \xrightarrow {\iota} [ n ] _ {t} \end{array}
\]

Lemma 3.3.3.17. For any \( n \) and for any \( k < n \), such that \( k \neq n - 2 \), we have inequalities \( d^k \circ \iota_{n-1} \geq_{n-1} \iota_n \circ [d^k, 1] \) and \( (d^n \circ \iota_{n-1}, d^{n-2} \circ \iota_{n-1}) \geq_{n-1} \iota_n \circ [d^{n-2}, 1] \)

158