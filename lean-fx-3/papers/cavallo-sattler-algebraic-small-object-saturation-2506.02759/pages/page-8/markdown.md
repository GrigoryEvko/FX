For each of these problems, we add a point to the two-step factorization. Solutions to the first two problems were already added in the first step, so the new solutions are equated with the existing ones in $f_1$. Moreover, the morphisms of (1.4) identify the point added for the third problem with those added for the first and second problems; likewise for the fourth problem. The two-step factorization is hence a *quotient* of the one-step factorization in which the points added in the first step are equated:

$$\begin{array}{ccc} 0 & \xrightarrow{m_1} 1 \sqcup 1 & \xrightarrow{m_2} 1 \\ f \downarrow & & f_1 \downarrow & f_2 \downarrow \\ 1 & \xrightarrow{!} 1 & \xrightarrow{!} 1. \end{array}$$

Garner's argument converges at this stage. In contrast to Quillen's argument, the transition map between the $n$-step and $(n+1)$-step factorization need not belong to the left class: $m_2: 1 \sqcup 1 \rightarrow 1$ is not a monomorphism.

We thus put aside the step maps $X_\alpha \rightarrow X_{\alpha+1}$ and instead look at the composites $m_{\leq \alpha}: X \rightarrow X_\alpha$, which *do* belong to the left class. We can write the left factor of Garner's factorization as their colimit in $\mathcal{E}^-$:

$$\begin{array}{ccc} X & = & X = \cdots = X \\ \| & & \downarrow m_{\leq 1} \downarrow m_{\leq 2} & \downarrow \text{colim}_{\alpha < \kappa} m_{\leq \alpha} =: Lf \\ X & \xrightarrow{m_1} X_1 & \xrightarrow{m_2} X_2 & \xrightarrow{m_3} \cdots & \longrightarrow X_\kappa \end{array} \quad (1.5)$$

While the *class* of left maps of an AWFS (L, R) is not generally closed under such colimits, the *category* of L-coalgebras is (indeed, it has all small colimits), and in fact (1.5) lifts to a diagram in L-Coalg: thanks to the quotienting, we solve lifts against $m_{\leq \alpha}$ and $m_{\leq \beta}$ in the same way on their overlap. It turns out that the cobase change involved in defining $m_{\leq \alpha+1}$ from $m_\alpha$ can similarly be described as a pushout in L-Coalg. These are the two kinds of colimit we require of a cellular notion of composable structure.

Finally, while the step maps in Garner's argument are not always left maps of the generated AWFS, we can often say *something* about them. In our target examples of Section 4.1, for instance, they are always monomorphisms. In such cases, we can more precisely delimit the colimits we need in Garner's construction. This is the role of the backdrop $\mathcal{M}$. Ultimately, the argument requires colimits chains of L-coalgebras of the form

$$\begin{array}{ccc} A & = & A = \cdots \\ \downarrow & & \downarrow \\ B_0 & \xrightarrow{\in \mathcal{M}} B_1 & \xrightarrow{\in \mathcal{M}} B_2 & \xrightarrow{\in \mathcal{M}} \cdots \end{array}$$

(up to some ordinal bound) and pushouts of spans of the form

$$\begin{array}{ccc} A_0 & \longleftarrow & A = \cdots \\ \downarrow & & \downarrow \\ B_0 & \longleftarrow & B \xrightarrow{\in \mathcal{M}} B_1. \end{array}$$

For these colimits to suffice for some generating diagram $u: \mathcal{J} \rightarrow \mathcal{E}^-$, we require (Definition 3.2.4) that $D_u: \mathcal{E}^- \rightarrow \mathcal{E}^-$ is valued in $\mathcal{M}$ and that given a square $(h, k): f \rightarrow g$ in $\mathcal{E}$ with $h, k \in \mathcal{M}$, the

8