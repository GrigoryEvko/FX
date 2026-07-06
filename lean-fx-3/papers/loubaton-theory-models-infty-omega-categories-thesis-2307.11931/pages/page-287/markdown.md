5.2. CARTESIAN FIBRATIONS

Corollary 5.2.2.13. Let $B$ be the colimit of a diagram $F: I \to (\infty, \omega)$-cat, and $p: X \to \operatorname{colim}_i B_i$ a left cartesian fibration. The canonical morphism

$$\underset{i:B_i \to B}{\operatorname{colim}} i^* p \to p$$

is an equivalence.

Proof. This morphism corresponds to the square

$$\begin{array}{c} \operatorname{colim}_{i:I} p^* B_i \longrightarrow X \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow_p \\ \operatorname{colim}_{i:I} B_i \longrightarrow B^\sharp \end{array}$$

The lower horizontal morphism is an equivalence by hypothesis, and the upper one is an equivalence as $p^*$ preserves colimits.

### 5.2.3 Colimits of cartesian fibrations

Through this section, we will identify any marked $(\infty, \omega)$-category $C$ with the canonical induced morphism $C \to 1$. If $f: X \to Y$ is a morphism, $f \times C$ then corresponds to the canonical morphism $X \times C \to Y$.

Lemma 5.2.3.1. Let $b$ be a globular sum and $F: I \to (\infty, \omega)$-cat$_{\mathrm{m}/b^\sharp}$ be a diagram that is pointwise a left cartesian fibration. The induced morphism $\operatorname{colim}_I F$ is a left cartesian fibration over $b^\sharp$.

Proof. We denote $G: I \to (\infty, \omega)$-cat$_{\mathrm{m}}$ the diagram induced by $F$ by taking the domain. Remark first that proposition 5.2.2.2 implies that $\operatorname{colim}_I F$ is $b$-exponentiable. Let $n$ be an integer. Suppose given cartesian squares

$$\begin{array}{c} Y' \xrightarrow{f} Y \xrightarrow{} \operatorname{colim}_I X \\ \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \operatorname{colim}_I F \\ \mathbf{D}_n^\flat \xrightarrow[i_n^\alpha]{} (\mathbf{D}_{n+1})_t \xrightarrow[j]{} b^\sharp \end{array}$$

where $\alpha$ is $+$ is $n$ is even and $-$ if not and with $j$ globular. According to proposition 5.2.2.6, we have to show that $f$ is a right Gray deformation retract to conclude. As $F$ is pointwise a left cartesian fibration, proposition 5.2.1.13 implies that for any $i: I$, the morphism $f(i)$ appearing in the cartesian squares:

$$\begin{array}{c} Y' \xrightarrow{f(i)} Y \xrightarrow{} X(i) \\ \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow_{F(i)} \\ \mathbf{D}_n^\flat \xrightarrow[i_n^\alpha]{} (\mathbf{D}_{n+1})_t \xrightarrow[j]{} b^\sharp \end{array}$$

277