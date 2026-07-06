CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

##### 1.2.2.14. Unfolding the definition, we have

\[
[ (K, K ^ {\prime}, e), 1 ] \vee [ 1 ] := ([ K, 1 ] \vee [ 1 ], ([ K, 1 ] \vee [ 1 ]) ^ {*}, e)
\]

\[
[ 1 ] \vee (K, K ^ {\prime}, e), 1 ] := ([ 1 ] \vee [ K, 1 ], ([ 1 ] \vee [ K, 1 ]) ^ {*}, e)
\]

where

- \([K,1]\vee [1]\) and \([1]\vee [K,1]\) are the chain complexes whose value on \(n\) are:

\[
[ K, 1 ] \vee [ 1 ] := \left\{ \begin{array}{l l} \mathbb {Z} [ \{0 \}, \{1 \}, \{2 \} ] & \text {if n = 0} \\ \{[ x, 1 ], x \in K _ {0} \} \oplus \mathbb {Z} [ e _ {1} ] & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 1} \end{array} \right.
\]

\[
[ 1 ] \vee [ K, 1 ] := \left\{ \begin{array}{l l} \mathbb {Z} [ \{0 \}, \{1 \}, \{2 \} ] & \text {if n = 0} \\ \mathbb {Z} [ e _ {1} ] \oplus \{[ x, 1 ], x \in K _ {0} \} & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 1} \end{array} \right.
\]

and the differentials are the unique graded group morphism fulfilling:

\[
\partial_ {[ K, 1 ] \vee [ 1 ]} (e _ {1}) := \{2 \} - \{1 \} \quad \partial_ {[ K, 1 ] \vee [ 1 ]} ([ x, 1 ]) := \left\{ \begin{array}{l l} \{1 \} - \{0 \} & \text {if} | x | = 0 \\ [ \partial x, 1 ] & \text {if} | x | > 0 \end{array} \right.
\]

\[
\partial_ {[ 1 ] \vee [ K, 1 ]} (e _ {1}) := \{1 \} - \{0 \} \quad \partial_ {[ 1 ] \vee [ K, 1 ]} ([ x, 1 ]) := \left\{ \begin{array}{l l} \{2 \} - \{1 \} & \text {if} | x | = 0 \\ [ \partial x, 1 ] & \text {if} | x | > 0 \end{array} \right.
\]

- \(([K,1]\vee [1])^{*}\) and \(([1]\vee [K,1])^{*}\) are given on all integer \(n\) by:

\[
([ K, 1 ] \vee [ 1 ]) ^ {*} := \left\{ \begin{array}{l l} \{\{0 \}, \{1 \}, \{2 \} \} & \text {if n = 0} \\ \{[ x, 1 ], x \in K _ {0} ^ {*} \} \oplus \mathbb {N} [ e _ {1} ] & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} \} & \text {if n > 1} \end{array} \right.
\]

\[
([ 1 ] \vee [ K, 1 ]) ^ {*} := \left\{ \begin{array}{l l} \{\{0 \}, \{1 \}, \{2 \} \} & \text {if n = 0} \\ \mathbb {N} [ e _ {1} ] \oplus \cup \{[ x, 1 ], x \in K _ {0} ^ {*} \} & \text {if n = 1} \\ \{[ x, 1 ], x \in K _ {n - 1} ^ {*} \} & \text {if n > 1} \end{array} \right.
\]

- The augmentations \( e \) are the unique morphism fulfilling

\[
e (\{0 \}) = e (\{1 \}) = e (\{2 \}) = 1.
\]

Proposition 1.2.2.15. Let A be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexes  \( [A,1]\vee[1] \)  and  \( [1]\vee[A,1] \)  have no non-trivial automorphisms.

Proof. The proof is similar to the one of proposition 1.2.2.12 and we leave it to the reader. \(\square\)

52