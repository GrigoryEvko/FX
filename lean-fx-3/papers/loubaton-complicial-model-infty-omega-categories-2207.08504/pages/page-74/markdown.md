CHAPTER 2. STUDY OF COMPLICIAL SETS

The suspension then preserves acyclic cofibration and is then a left Quillen functor.

This functor admits a right adjoint, that sends a pair $(a, b, C)$ to $C(a, b)$ where $a, b$ are two 0-simplices of $C$. If $p : C \to D$ is a morphism between complicial sets, and $a, b$ two 0-simplices of $C$, we denote by

$$p(a, b) : C(a, b) \to D(pa, pb)$$

the induced morphism.

Construction 2.2.2.10. We introduce an other operation, the diamond product, that makes the link between the Gray tensor product and the join. Let $X$ and $Y$ be two marked simplicial sets. We define $X \diamond Y$ as the colimit of the diagram:

$$X \longleftarrow X \otimes \{0\} \otimes Y \longrightarrow X \otimes [1] \otimes Y \longleftarrow X \otimes \{1\} \otimes Y \longrightarrow Y$$

The functors

$$\_ \diamond X : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X} \quad \text{and} \quad X \diamond \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X}$$

are colimit preserving. Furthermore, for every acyclic cofibration $K \to L$, the morphism $K \diamond X \to L \diamond X$ is the horizontal colimit of the diagram:

$$\begin{array}{c} K \amalg X \longleftarrow K \otimes \partial[1] \otimes X \longrightarrow K \otimes [1] \otimes X \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ L \amalg X \longleftarrow L \otimes \partial[1] \otimes X \longrightarrow L \otimes [1] \otimes X \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that $\_ \diamond X$ is a left Quillen functor. We show analogously that $X \diamond \_$ is a left Quillen functor.

Proposition 2.2.2.11. There is a canonical isomorphism

$$(X \diamond Y)^{\mathrm{op}} \cong Y^{\mathrm{op}} \diamond X^{\mathrm{op}}$$

natural in $X$ and $Y$.

Proof. This directly follows from proposition 2.2.2.4.

Lemma 2.2.2.12. There exists a unique natural transformation $\gamma_{X,Y} : X \diamond Y \to X \star Y$ that fits in the following diagram:

$$\begin{array}{c} X \coprod Y \longrightarrow X \star Y \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \diamond Y \longrightarrow [1] \end{array}$$

Proof. We begin by defining this morphism on simplicial sets, and for this we can suppose that both $X$ and $Y$ are representables, ie $X := [n]$, $Y := [m]$. On object, this morphism is induced by the assignation:

$$p(k, 0, l) := k \quad p(k, 1, l) := l.$$

We need to verify that this morphism preserves thin cells. Suppose now that $(x, v, y)$ is a thin $n$-simplex of $X \diamond Y$. There are several cases to consider. Case $v_n = 0$. The simplex $x$ is then thin, and is sent to $x \star \emptyset$ which is also thin. Case $v_0 = 1$. Similar. Case $v_0 = 0$ and $v_n = 1$. Let $p$ be the smaller integer such that $v_p = 1$. Either $\amalg_{p-1, n-p+1}^1(x)$ or $\amalg_{p, n-p}^2(y)$ is thin. This implies that $\phi_{X,Y}(x, v, y) = \amalg_{p-1, n-p+1}^1(x) \star \amalg_{p, n-p}^2(y)$ is thin.

74