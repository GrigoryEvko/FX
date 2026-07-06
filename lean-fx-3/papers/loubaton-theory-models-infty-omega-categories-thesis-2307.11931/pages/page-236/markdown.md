CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**Corollary 4.3.3.21.** *There is a natural diagram*

$$\begin{array}{c} (C \otimes \{1\})^{\circ} \longrightarrow (C \otimes [1])^{\circ} \longleftarrow (C \otimes \{0\})^{\circ} \\ \downarrow \sim \qquad \qquad \qquad \downarrow \sim \qquad \qquad \downarrow \sim \\ C^{\circ} \otimes \{0\} \longrightarrow C^{\circ} \otimes [1] \longleftarrow C^{\circ} \otimes \{1\} \end{array}$$

*where all vertical arrows are equivalences. There is an invertible natural transformation*

$$C \star 1 \sim (1 \stackrel{co}{\star} C^{\circ})^{\circ}.$$

*Proof.* As these functors preserve colimits, we can define this equivalence on representables. As cylinders (resp. cone) (resp. o-cone) of representables are strict according to theorem 4.3.3.19, and as $(\_)^{\circ}$ preserves strict objects, it is enough to show these equivalences in $(0, \omega)$-cat, where it follows from [AM20, proposition A.22].

**Corollary 4.3.3.22.** *Let $A$ and $B$ two $(\infty, \omega)$-categories. There is an equivalence*

$$(A \ominus B)^{\circ} \sim A^{\circ} \ominus B^{\circ}$$

*natural in $A$ and $B$.*

*Proof.* It is sufficient to construct the equivalence when $A$ is a globular sum $a$ and $B$ is of shape $[b, n]$. Remark first that the corollary 4.3.3.20 implies that $(a \otimes [n])^{\circ}$ and $a^{\circ} \otimes [n]^{\circ}$ are strict objects. The proposition A.22 of [AM20] then implies that these two objects are isomorphic. The results then directly follows from the definition of the operation $\ominus$ and from the equivalence $(m_b(\_))^{\circ} \sim m_{b^{\circ}}((\_)^{\circ})$. $\square$

**Corollary 4.3.3.23.** *Let $F$ be an endofunctor of $(\infty, \omega)$-cat such that the induced functor $(\infty, \omega)$-cat $\to (\infty, \omega)$-cat$_{F(\emptyset)/}$ is colimit preserving, and $\psi$ is an invertible natural transformation between $G^{+} \to (\infty, \omega)$-cat $\xrightarrow{F} (\infty, \omega)$-cat and $G^{+} \to (\infty, \omega)$-cat $\xrightarrow{H} (\infty, \omega)$-cat where $G^{+}$ is obtained from $G$ by adding an initial element $\{\emptyset\}$, and $H$ is either the Gray cylinder, the Gray cone, the Gray o-cone or an iterated suspension.*

*Then, the natural transformation $\psi$ can be extended to an invertible natural transformation between $F$ and $H$.*

*Proof.* We denote by $\Theta^{+}$ the category obtained from $\Theta$ by adding an initial element $\emptyset$. Remark first that the theorem 1.2.3.18 implies that we have an invertible natural transformation

$$\pi_{0} \circ F_{|\Theta^{+}} \to \pi_{0} \circ H_{|\Theta^{+}}.$$

The propositions 4.3.3.12, 4.3.3.17 and 4.3.3.2 imply that the canonical morphism

$$H_{|\Theta^{+}} \to \mathrm{N} \circ \pi_{0} \circ H_{|\Theta^{+}}$$

226