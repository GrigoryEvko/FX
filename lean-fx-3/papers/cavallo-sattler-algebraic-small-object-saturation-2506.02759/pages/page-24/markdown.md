have these properties. Left-connected and cellular notions of composable structure are the targets for our main theorems.

In Section 3.4, we return to the abstract setting of Section 2 and give conditions under which, for a given notion of composable structure, structure on the unit of a pointed endofunctor yields structure on the unit of its free monad (Theorem 3.4.4). Finally, we prove our main results (Theorems 3.5.6, 3.5.13 and 3.5.16) in Section 3.5 by applying the results of Section 3.4 to the specific case of the free monad construction that produces a cofibrantly generated AWFS.

### 3.1 Preliminaries

#### 3.1.1 Algebraic weak factorization systems

The original definition of AWFS is due to Grandis and Tholen [GT06] under the name *natural weak factorization system*. The definition we use here includes an additional distributivity condition which was introduced by Garner [Gar09]. Recall from Section 1.1 that an AWFS (L, R) on a category $\mathcal{E}$ consists of a pair of a comonad $\mathsf{L} = (L, \Phi, \Sigma)$ and monad $\mathsf{R} = (R, \Lambda, \Pi)$ such that $L, R$ define a functorial factorization, $\Phi \colon L \to \mathrm{Id}$ and $\Lambda \colon \mathrm{Id} \to R$ are of the form

$$
\begin{array}{c c c} X \xlongequal {\quad} X & X \xrightarrow {L f} E f \\ L f \Big \downarrow \quad \Phi_ {f} \quad \Big \downarrow f & f \Big \downarrow \quad \Lambda_ {f} \quad \Big \downarrow R f \\ E f \xrightarrow [ R f ]{} Y & Y \xlongequal {\quad} Y \end{array}
$$

respectively, and we have a distributive law [Bec69] of L over R.

**Remark 3.1.1.** The (co)unit laws imply that the comultiplication $\Sigma$ and multiplication $\Pi$ are of the forms

$$
\begin{array}{c c c} X \xlongequal {\quad} X & & E R f \xrightarrow {\mu_ {f}} E f \\ L f \Big \downarrow \quad \Sigma_ {f} \quad \Big \downarrow L L f & & R R f \Big \downarrow \quad \Pi_ {f} \quad \Big \downarrow R f \\ E f \xrightarrow [ \delta_ {f} ]{} E L f & & Y \xlongequal {\quad} Y \end{array}
$$

for some $\delta \colon E\to EL$ and $\mu \colon ER\to E$.

**Proposition 3.1.2** ([Gar09, Remark 2.17] [Rie11, Remark 2.11]). An AWFS (L, R) has an underlying WFS whose left and right classes may be described either as

(i) the (co)algebras for the (co)pointed endofunctors \(\mathsf{L}_{\mathfrak{p}}\) and \(\mathsf{R}_{\mathfrak{p}}\) respectively; or
(ii) the retracts in \(\mathcal{E}^{\rightarrow}\) of (co)algebras for the (co)monads L and R respectively.

**Notation 3.1.3.** Given an AWFS (L, R) on $\mathcal{E}$, we write $\pmb{L} \colon \mathcal{E}^{\rightarrow} \to \mathsf{L}$-Coalg and $\pmb{R} \colon \mathcal{E}^{\rightarrow} \to \mathsf{R}$-Alg for the functors sending a map to its cofree L-coalgebra and free R-algebra respectively.

**Notation 3.1.4.** Fix an AWFS (L, R). An object of $\mathsf{L}_{\mathfrak{p}}$-Coalg is, by definition, a morphism $f$ in $\mathcal{E}$ equipped with a section of $\Phi_f \colon Lf \to f$. Such a section is determined by a map $s$ in $\mathcal{E}$ fitting in the diagram

$$
\begin{array}{c} A \xlongequal {\quad} A \xlongequal {\quad} A \\ f \Big \downarrow \qquad \qquad \qquad \Big \downarrow L f \qquad \qquad \qquad \Big \downarrow f \\ B \xleftarrow {s} E f \xrightarrow {R f} B. \end{array}
$$

As such, we speak of objects of $\mathsf{L}_{\mathfrak{p}}$-Coalg as pairs $(f,s)$. An object of L-Coalg is such a pair with the additional property that $E(\mathrm{id}_A,s)s = \delta_f s \colon f \to ELf$.

24