CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

is an equivalence. According to theorem 5.2.3.3, the two objects are left cartesian fibrations, and we then have to check that this morphism induce equivalences on fibers. Remark furthermore that the two morphisms $\{0\} \rightarrow [b, 1]^{\sharp}$ and $\{1\} \rightarrow [b, 1]^{\sharp}$ are discrete Conduché functors and then exponentiable according to proposition 5.1.1.29. The fibers on 0 and 1 of the morphism (5.2.3.9) then corresponds to the equivalences

$$1 \coprod_{\emptyset} \emptyset \sim 1 \quad \text{and} \quad b \coprod_b C \sim C.$$

**Theorem 5.2.3.10.** *Let $C$ be a $(\infty, \omega)$-category. The left cartesian fibration $\mathbf{F}h^0_{[C,1]}$ is equivalent to the projection $1 \stackrel{co}{\star} C^{\flat} \rightarrow [C, 1]^{\sharp}$.*

*Proof.* Let $i : [b, 1]^{\sharp} \rightarrow [C, 1]^{\sharp}$ be any morphism. The proposition 5.2.3.8 states that the following square is cartesian:

$$\begin{array}{ccc} 1 \stackrel{co}{\star} b^{\flat} \coprod_{b^{\flat}} C^{\flat} & \longrightarrow & [C, 1]_{0/}^{\sharp} \\ \downarrow & & \downarrow \\ [b, 1]^{\sharp} & \longrightarrow & [C, 1]^{\sharp} \end{array}$$

Eventually, remark that we have an equivalence

$$\underset{b \rightarrow C}{\operatorname{colim}}[b, 1] \sim [C, 1].$$

The theorem 5.2.2.12 then induces equivalences

$$[C, 1]_{0/}^{\sharp} \sim \underset{i:b \rightarrow C}{\operatorname{colim}} 1 \stackrel{co}{\star} b^{\flat} \coprod_{b^{\flat}} C^{\flat} \sim 1 \stackrel{co}{\star} C^{\flat} \coprod_{C^{\flat}} C^{\flat} \sim 1 \stackrel{co}{\star} C^{\flat}$$

over $[C, 1]^{\sharp}$. This concludes the proof.

**Corollary 5.2.3.11.** *Let $b$ be a globular form and $j : b \rightarrow C$ any morphism. The following square is cartesian:*

$$\begin{array}{ccc} 1 \stackrel{co}{\star} b \coprod_b C & \longrightarrow & 1 \stackrel{co}{\star} C \\ \downarrow & & \downarrow \\ [b, 1] & \longrightarrow & [C, 1] \end{array}$$

*Proof.* We apply the functor $(\_)^{\sharp}$ to the cartesian square given in proposition 5.2.3.8 and the equivalence given in theorem 5.2.3.10.

**Corollary 5.2.3.12.** *Let $C$ be an $(\infty, \omega)$-category. We denote by $\gamma : C \star 1 \rightarrow [C, 1]$ and $\gamma' : 1 \stackrel{co}{\star} C \rightarrow [C, 1]$ the two canonical projections. The functors $\gamma^* : (\infty, \omega)\text{-cat}_{/[C,1]} \rightarrow (\infty, \omega)\text{-cat}_{/C \star 1}$ and $\gamma^* : (\infty, \omega)\text{-cat}_{/[C,1]} \rightarrow (\infty, \omega)\text{-cat}_{/1 \stackrel{co}{\star} C}$ preserve colimits.*

282