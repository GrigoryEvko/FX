CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

1.2.2.4. To simplify notion, the augmented directed complex \(\lambda[1]\) will simply be denoted by [1]. The induced functor

\[
\_ \otimes [ 1 ]: \mathrm{ADC} \rightarrow \mathrm{ADC}
\]

is called the Gray cylinder. For  \( (K, K^{*}, e) \)  an augmented directed complex, we then have

\[
(K, K ^ {*}, e) \otimes [ 1 ] := (K \otimes [ 1 ], (K \otimes [ 1 ]) ^ {*}, e)
\]

where

- \(K \otimes [1]\) is the chain complex whose value on \(n\) is:

\[
(K \otimes [ 1 ]) _ {n} := \left\{ \begin{array}{l l} \{x \otimes \{\epsilon \}, x \in K _ {0}, \epsilon = 0, 1 \} & \text {if n = 0} \\ \{x \otimes \{\epsilon \}, x \in K _ {n}, \epsilon = 0, 1 \} \oplus \{x \otimes [ 1 ], x \in K _ {n - 1} \} & \text {if n > 0} \end{array} \right.
\]

and the differential is the unique graded group morphism fulfilling:

\[
\partial (x \otimes [ 1 ]) := \partial x \otimes [ 1 ] + (- 1) ^ {| x |} (x \otimes \{1 \} - x \otimes \{0 \}) \quad \partial (x \otimes \{\epsilon \}) = (\partial x) \otimes \{\epsilon \}
\]

for \(\epsilon \in \{0,1\}\), and where we set the convention \(\partial x := 0\) if \(|x| = 0\).

- \((K\otimes [1])^{*}\) is given on all integer \(n\) by:

\[
(K \otimes [ 1 ]) _ {n} ^ {*} := \left\{ \begin{array}{l l} \{x \otimes \{\epsilon \}, x \in K _ {0} ^ {*}, \epsilon = 0, 1 \} & \text {if n = 0} \\ \{x \otimes \{\epsilon \}, x \in K _ {n} ^ {*}, \epsilon = 0, 1 \} \oplus \{x \otimes [ 1 ], x \in K _ {n - 1} ^ {*} \} & \text {if n > 0} \end{array} \right.
\]

- \(e:(K\otimes [1])_0\to \mathbb{Z}\) is the unique morphism fulfilling

\[
e (x \otimes \{0 \}) = e (x \otimes \{1 \}) = e (x).
\]

1.2.2.5. We define the Gray cone and the Gray o-cone:

\[
\begin{array}{c c c c c c} \text {ADC} & \to & \text {ADC} & \text {ADC} & \to & \text {ADC} \\ K & \mapsto & K \star 1 & K & \mapsto & 1 ^ {c o} \star K \end{array}
\]

where \(K \star 1\) and \(1 \stackrel{co}{\star} K\) are defined as the following pushout:

\[
\begin{array}{c c c} K \otimes \{1 \} \longrightarrow K \otimes [ 1 ] & K \otimes \{0 \} \longrightarrow K \otimes [ 1 ] \\ \Big \downarrow & \Big \downarrow & \Big \downarrow \\ 1 \longrightarrow K \star 1 & 1 \longrightarrow 1 ^ {c o} \star K \end{array} \tag {1.2.2.6}
\]

The equation (1.2.2.3) provides an equivalence

\[
(C \star 1) ^ {\circ} \cong 1 \stackrel {c o} {\star} C ^ {\circ}.
\]

According to [AM20, corollary 6.21] and to the previous equivalence, if \( K \) admits a loop free and unitary basis, this is also the case for \( K \star 1 \) and \( 1 \stackrel{co}{\star} K \). The Gray cone and the Gray o-cone then induce functors:

\[
\begin{array}{c c c c c c} \mathrm{ADC} _ {\mathrm{B}} & \to & \mathrm{ADC} _ {\mathrm{B}} & \mathrm{ADC} _ {\mathrm{B}} & \to & \mathrm{ADC} _ {\mathrm{B}} \\ K & \mapsto & K \star 1 & K & \mapsto & 1 ^ {c o} \star K \end{array}
\]

48