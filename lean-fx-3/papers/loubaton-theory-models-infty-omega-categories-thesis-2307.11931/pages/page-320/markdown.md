CHAPTER 6. THE \((\infty, \omega)\)-CATEGORY OF SMALL \((\infty, \omega)\)-CATEGORIES

6.1.1.20. Let \( S \) be a subset of \( \mathbb{N}^* \). We define the subset \( \Sigma S = \{i + 1, i \in S\} \). Remark that for any \( n \), we have

\[
(\mathrm{N} _ {(\omega , 1)} C) _ {n} ^ {S} \sim (\mathrm{N} _ {(\omega , 1)} C ^ {\Sigma S}) _ {n}
\]

We then set the functor

\[
(\_) ^ {S}: \underline {{\omega}} \to (\underline {{\omega}}) ^ {\Sigma S}
\]

sending a U-small left fibration  \( X \to \mathrm{N}_{(\omega,1)} C \)  to the left fibration  \( n \mapsto (X_{n}^{S} \to (\mathrm{N}_{(\omega,1)} C^{\Sigma S})_{n}^{S}) \) . These functors are called dualities. In particular, we have the odd duality  \( (\_)^{op} : \underline{\omega} \to \underline{\omega}^{co} \) , corresponding to the set of odd integer, the even duality  \( (\_)^{co} : \underline{\omega} \to (\underline{\omega}^{t})^{op} \) , corresponding to the subset of non negative even integer, the full duality  \( (\_)^{\circ} : \underline{\omega} \to \underline{\omega}^{t\circ} \) , corresponding to  \( N^{*} \)  and the transposition  \( (\_)^{t} : \underline{\omega} \to \underline{\omega}^{\Sigma t} \) , corresponding to the singleton  \( \{1\} \) . Eventually, we have equivalences

\[
((\_) ^ {c o}) ^ {o p} \sim (\_) ^ {\circ} \sim ((\_) ^ {o p}) ^ {c o}.
\]

#### 6.1.2 Grothendieck construction

Notation. Through this section, we will identify any marked  \( (\infty,\omega) \) -categories C with the canonical induced morphism  \( C\to1 \) . If  \( f:X\to Y \)  is a morphism,  \( f\times C \)  then corresponds to the canonical morphism  \( X\times C\to Y \) .

6.1.2.1. Let A be an  \( (\infty,\omega) \) -category and a an object of A, we denote by  \( h_{a}^{A} \)  the morphism  \( 1 \rightarrow A^{\sharp} \)  induces by a. At the end of section 5.2.1, we have remarked that the left fibrant replacement of  \( h_{a}^{A} \), that we denoted by  \( Fh_{a}^{A} \), is the fibration  \( A_{a/}^{\sharp} \rightarrow A^{\sharp} \). Equation (5.1.3.7) induces, for any object b of  \( A^{\sharp} \), a cartesian square

\[
\begin{array}{c} \hom_ {A} (a, b) ^ {\flat} \longrightarrow A _ {a /} ^ {\sharp} \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Biggl \downarrow \mathbf {F} h _ {a} ^ {A} \\ \{b \} \longrightarrow A ^ {\sharp} \end{array} \tag {6.1.2.2}
\]

which induces a canonical morphism \( h_b^A \times \mathrm{hom}_A(a, b)^b \to \mathbf{F}h_a^A \), and consequently, a morphism \( \mathbf{F}h_b^A \times \mathrm{hom}_A(a, b)^b \to \mathbf{F}h_a^A \).

The case of \( A := [C,1] \) will be of particular interest. The morphism \( \mathbf{F}h_1^{[C,1]} \) is just \( h_1^{[C,1]} \) and theorem 5.2.3.10 implies that \( \mathbf{F}h_0^{[C,1]} \) is the canonical morphism \( 1 \stackrel{\circ}{\star} C^\flat \to [C,1]^{\sharp} \). In this last case, the square (6.1.2.2) corresponds to the square

\[
\begin{array}{c} C ^ {\flat} \longrightarrow 1 \stackrel {{c o}} {{\star}} C ^ {\flat} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \mathbf {F} h _ {0} ^ {[ C, 1 ]} \\ \{1 \} \longrightarrow [ C, 1 ] ^ {\sharp} \end{array}
\]

310