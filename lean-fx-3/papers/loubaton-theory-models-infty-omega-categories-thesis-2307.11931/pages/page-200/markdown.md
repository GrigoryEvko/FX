CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

has the unique right lifting property against W. We then consider a square

$$\begin{array}{c} a \longrightarrow \operatorname{colim}_{i:I} \iota F(i) \\ \downarrow \quad \downarrow \operatorname{colim}_{i:I} \iota \psi(i) \\ b \longrightarrow \operatorname{colim}_{i:I} \iota G(i) \end{array} \tag{4.2.1.25}$$

where $f \in W$. As the domain of $f$ is representable, there always exists $j : I$, such that the bottom horizontal morphism factors through $G(j)$. As $\psi$ is cartesian, the square (4.2.1.25) factors in two squares, where the right one is cartesian.

$$\begin{array}{c} a \longrightarrow F(i) \longrightarrow \operatorname{colim}_{i:I} \iota F(i) \\ \downarrow \quad \downarrow \psi(i) \quad \downarrow \operatorname{colim}_{i:I} \iota \psi(i) \\ b \longrightarrow G(i) \longrightarrow \operatorname{colim}_{i:I} \iota G(i) \end{array}$$

Lifts in the square (4.2.1.25) are then equivalent to lifts in the left square, which exist and are unique as $F(i) \to G(i)$ has the unique right lifting property against W. $\square$

**Proposition 4.2.1.26.** *For any integer $n$, and globular sums $a$ and $b$, the equalizer diagram*

$$\coprod_{k+l=n-1}[a, k] \vee [a \times b, 1] \vee [a, l] \longrightarrow \coprod_{k+l=n}[a, k] \vee [b, 1] \vee [a, l]$$

*where the top diagram is induced by $[a \times b, 1] \to [a, 1] \vee [b, 1]$ and to bottom one by $[a \times b, 1] \to [b, 1] \vee [a, 1]$, has a special colimit, which is $[a, n] \times [b, 1]$.*

*Proof.* The lemma 4.1.1.6 implies that the colimit of the previous diagram, computed in $\operatorname{Psh}^{\infty}(\Theta)$ is strict. It is then enough to show that this colimit, computed in $\operatorname{Psh}(\Theta)$, is equivalent to $[a, n] \times [b, 1]$. As this last object is W-local, this will conclude the proof. The remaining combinatorial exercise is left to the reader. $\square$

**Proposition 4.2.1.27.** *Any sequence of $(\infty, \omega)$-categories has a special colimit.*

*Proof.* Suppose given such sequence. If the sequence is finite, this is obviously true. Suppose now that the sequence is non finite. As codomains and domains of morphism of W are $\omega$-small, the colimit of the sequence, computed in $\operatorname{Psh}^{\infty}(\Theta)$ is W-local, which concludes the proof. $\square$

**Lemma 4.2.1.28.** *The functor $[\_, 1] : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}_{\bullet,\bullet}$ preserves special colimits.*

*Proof.* This is a direct consequence of proposition 4.2.1.14. $\square$

190