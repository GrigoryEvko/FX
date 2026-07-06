CHAPTER 4. THE \((\infty,1)\)-CATEGORY OF \((\infty,\omega)\)-CATEGORIES

We denote by

\[
(\infty , \omega) \text {-cat} \rightarrow (\infty , \omega) \text {-cat}
\]

\[
C \mapsto C ^ {[ 1 ]}
\]

the right adjoint of the Gray cylinder.

Eventually, recall that we have a natural transformation  \( C \otimes [1] \to [C, 1] \)  whose restriction to  \( C \otimes \{0\} \)  (resp. to  \( C \otimes \{1\} \) ) is constant on  \( \{0\} \)  (resp. on  \( \{1\} \) ), and such that the following induced square is cocartesian:

\[
\begin{array}{c} C \otimes \{0, 1 \} \longrightarrow C \otimes [ 1 ] \\ \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \tag {4.3.1.1}
\]

##### 4.3.1.2. We define the Gray cone and the Gray o-cone:

\[
\begin{array}{c c c c c c c c} (\infty , \omega) \text {-cat} & \to & (\infty , \omega) \text {-cat} _ {\bullet} & (\infty , \omega) \text {-cat} & \to & (\infty , \omega) \text {-cat} _ {\bullet} \\ C & \mapsto & C \star 1 & C & \mapsto & 1 \stackrel {c o} {\star} C \end{array}
\]

where \(C\star 1\) and \(1\stackrel {co}{\star}C\) are defined as the following pushout:

\[
\begin{array}{c c} C \otimes \{1 \} \longrightarrow C \otimes [ 1 ] & C \otimes \{0 \} \longrightarrow C \otimes [ 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \qquad \qquad \qquad \qquad \Big \downarrow \\ 1 \longrightarrow C \star 1 & 1 \longrightarrow 1 ^ {c o} \star C \end{array}
\]

The corollary 4.3.3.21 will imply an invertible natural transformation

\[
C \star 1 \sim (1 ^ {c o} \star C ^ {\circ}) ^ {\circ}.
\]

We will denote by

\[
\begin{array}{c c c c c c c c} (\infty , \omega) \text {-cat} _ {\bullet} & \to & (\infty , \omega) \text {-cat} & (\infty , \omega) \text {-cat} _ {\bullet} & \to & (\infty , \omega) \text {-cat} \\ (C, c) & \mapsto & C _ {/ c} & (C, c) & \mapsto & C _ {c /} \end{array}
\]

the right adjoints of the Gray cone and the Gray o-cone, respectively called the slice of C over c and the slice of C under c. The corollary 4.3.3.21 will imply an invertible natural transformation

\[
C _ {/ c} \sim (C _ {c /} ^ {\circ}) ^ {\circ}.
\]

Given an \((\infty, \omega)\)-category \(C\), and two objects \(c, d\), we have by construction two cartesian squares:

\[
\begin{array}{c c} \hom_ {C} (c, d) \longrightarrow C _ {/ d} & \hom_ {C} (c, d) \longrightarrow C _ {c /} \\ \Big \downarrow \qquad \qquad \qquad \Big \downarrow & \Big \downarrow \\ \{c \} \longrightarrow C & \{d \} \longrightarrow C \end{array}
\]

208