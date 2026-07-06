CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

the right adjoints of Gray cone and of the Gray o-cone, respectively called the *slice of C over c* and the *slice of C under c*. The proposition 5.1.3.3 induces an invertible natural transformation:

$$C_{/c} \sim (C_{c/}^{\circ})^{\circ}.$$

Given an $(\infty, \omega)$-category $C$, and $c, d$ two objects, the cocartesian square (5.1.3.2) induces two cartesian squares:

$$\begin{array}{ccc} \hom_C(c, d)^{\flat} & \longrightarrow & C_{/d}^{\sharp} \\ \downarrow & \downarrow & \downarrow \\ \{c\} & \longrightarrow & C^{\sharp} \end{array} \qquad \begin{array}{ccc} \hom_C(c, d)^{\flat} & \longrightarrow & C_{c/}^{\sharp} \\ \downarrow & \downarrow & \downarrow \\ \{d\} & \longrightarrow & C^{\sharp} \end{array} \quad (5.1.3.7)$$

**5.1.3.8.** The equation given in paragraph 4.3.1.6 induces similar ones for the marked version of these operations. For every marked $(\infty, \omega)$-category $C$, there are a natural identification between $[C, 1] \otimes [1]^{\sharp}$ and the colimit of the following diagram

$$[1]^{\sharp} \vee [C, 1] \longleftarrow [C \otimes \{0\}, 1] \longrightarrow [C \otimes [1]^{\sharp}, 1] \longleftarrow [C \otimes \{1\}, 1] \longrightarrow [C, 1] \vee [1]^{\sharp} \quad (5.1.3.9)$$

There is also a natural identification between $1 \stackrel{\circ\circ}{\star} [C, 1]$ and the colimit of the diagram

$$[1]^{\sharp} \vee [C, 1] \longleftarrow [C, 1] \longrightarrow [C \star 1, 1] \quad (5.1.3.10)$$

and between $[C, 1] \star 1$ and the colimit of the diagram

$$[1 \stackrel{\circ\circ}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1]^{\sharp} \quad (5.1.3.11)$$

**5.1.3.12.** For any $C : (\infty, \omega)$-cat, we denote by $m_{C^{\sharp}}$ the colimit preserving functor $(\infty, \omega)\text{-cat}_m \rightarrow (\infty, \omega)\text{-cat}_m$ whose value on $[a, n]^{\flat}$ is $[a \times C^{\sharp}, n]$, on $[1]^{\sharp}$ is $[C, 1]^{\sharp}$, and on $[(\mathbf{D}_n)_t, 1]$ is $[(\mathbf{D}_n)_t \times C^{\sharp}, 1]$. Remark that the assignation $C \mapsto m_{C^{\sharp}}$ is natural in $C$ and that $m_1$ is the identity. We define the colimit preserving functor:

$$\begin{array}{ccc} (\infty, \omega)\text{-cat}_m \times (\infty, \omega)\text{-cat}_m & \rightarrow & (\infty, \omega)\text{-cat}_m \\ (X, Y) & \mapsto & X \ominus Y^{\sharp} \end{array}$$

where for any marked $(\infty, \omega)$-category $C$ and element $[b, n]$ of $\Delta[\Theta]$, $C \ominus [b, n]^{\sharp}$ is the following pushout:

$$\begin{array}{ccc} \coprod_{k \leq n} m_{b^{\sharp}}(C \otimes \{k\}) & \longrightarrow & m_{b^{\sharp}}(C \otimes [n]^{\sharp}) \\ \downarrow & & \downarrow \\ \coprod_{k \leq n} m_1(C \otimes \{k\}) & \longrightarrow & C \ominus [b, n]^{\sharp} \end{array} \quad (5.1.3.13)$$

250