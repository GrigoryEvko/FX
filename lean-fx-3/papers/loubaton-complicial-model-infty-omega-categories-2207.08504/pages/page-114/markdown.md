CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Notation 3.1.5.6. We will denote by \([n_0] \otimes [n_1] \otimes ..[n_k] \otimes a\) the object \([n_0] \otimes ([n_1] \otimes ..([n_k] \otimes a))\).

Example 3.1.5.7. For any \(d \in \mathbb{N} \cup \{\omega\}\), the model category \(\mathrm{tPsh}(\Delta)^d\), corresponding to the model structure for \(d\)-complicial sets on stratified simplicial sets, and where \(K \otimes L := \tau_1^i(K) \boxtimes L\), is an example of complicial Gray module.

Indeed, if \( n \) is any integer, we define \( [n]^{\diamond} := [0] \diamond [0] \diamond \ldots \diamond [0] \) and \( [n]_{l}^{\diamond} := \tau_{n}^{i}([n]^{\diamond}) \). This induces a colimit preserving functor \( K \mapsto K^{\diamond} \). The join coming from \( \tau_{1}^{i}(\_) \boxtimes \_ \) then corresponds to the functor \( (K, L) \mapsto K^{\diamond} \diamond L \). The proposition 2.2.2.13 provides a natural transformation \( K^{\diamond} \diamond L \to K \star L \), which implies that the first functor is left Quillen.

### 3.2 Complicial Gray module structure on  \( \operatorname{tSeg}(A) \)

The purpose of this section is to show that for any complicial Gray module \( A \), the Gray module structure on \( \mathrm{tSeg}(A) \) constructed in 3.1.4.8 is complicial. This is achieved in theorem 3.2.6.2.

We fix a complicial Gray module \(A\) until the end of this section.

#### 3.2.1 o-cone in tSeg(A)

To show that the Gray module  \( \operatorname{tSeg}(A) \)  is complicial, we need to demonstrate that the adjunction with marked simplicial sets constructed in 3.1.5.1 is a Quillen adjunction. This adjunction is constructed using an op-cone  \( e \star_{-} : \operatorname{tSeg}(A) \to \operatorname{tSeg}(A) \)  arising from the Gray module structure of  \( \operatorname{tSeg}(A) \) . However, for technical reasons, it will be useful to work with another op-cone that is constructed in 3.2.1.2. We have chosen to also denote this op-cone on  \( \operatorname{tSeg}(A) \)  by  \( e \star_{-} \) , as it is the only one we will use from now on.

Proposition 3.2.1.3 shows that these two op-cones are weakly equivalent, implying that the two adjunctions with stratified simplicial sets they induce are weakly equivalent.

Construction 3.2.1.1. We consider the colimit-preserving functor

\[
e \star_ {-}: \operatorname{Seg} (A) \to \operatorname{Seg} (A)
\]

whose value on \([a, m]\) fits in the pushout

\[
\begin{array}{c} \coprod_ {l \leq m} \operatorname{colim} _ {[ k _ {0}, k _ {1} ] \to 1 \star \{l \}} [ [ k _ {0} ] \otimes a, k _ {1} ] \longrightarrow \operatorname{colim} _ {[ k _ {0}, k _ {1} ] \to 1 \star [ m ]} [ [ k _ {0} ] \otimes a, k _ {1} ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_ {l \leq m} \operatorname{colim} _ {[ k _ {0}, k _ {1} ] \to 1 \star \{l \}} [ e, k _ {1} ] \xrightarrow {} e \star [ a, m ] \end{array}
\]

This functor is called the Gray o-cylinder, where  \( 1 \star_{-} : (\infty, 1) \) -cat  \( \rightarrow (\infty, 2) \) -cat denotes the Gray o-cone defined in 1.2.4.8. The morphism  \( d^{0} : [m] \to 1 \star [m] \)  induces a morphism

\[
d ^ {0} \star [ a, m ]: [ a, m ] \cong \underset {[ k _ {1} ] \to [ m ]} {\operatorname{colim}} [ a, k _ {1} ] \to e \star [ a, m ].
\]

By left Kan extension, this induces a transformation

\[
d ^ {0} \star C: C \to e \star C
\]

natural in \(C:\operatorname {Seg}(A)\)

114