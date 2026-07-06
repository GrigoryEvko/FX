Explicitly, $\mathcal{E}^{\mathfrak{g}}$ is the full subcategory of $T \downarrow \mathcal{E}$ of objects $(A, B, f)$ for which $f\tau_A \colon A \to B$ is in $\mathcal{M}$. The left adjoint $\tau_*$ of $\tau$ restricts to a functor $\mathcal{E}_{\mathcal{M}}^{\rightarrow} \to \mathcal{E}^{\mathfrak{g}}$, so we have a restricted adjoint pair

$$\mathcal{E}_{\mathcal{M}}^{\rightarrow} \xleftrightarrow[\tau^!]{\tau_*} \mathcal{E}^{\mathfrak{g}}$$

that we abusively write with the same notation.

**Notation 2.3.17.** In the setting of Definition 2.3.16, write $\mathcal{M}^{\mathfrak{g}}$ for wide subcategory of $\mathcal{E}^{\mathfrak{g}}$ consisting of morphisms $(u \colon A \to A', v \colon B \to B') \colon (A, B, f) \to (A', B', f')$ with $u, v \in \mathcal{M}$.

**Definition 2.3.18.** Given a category $\mathcal{E}$, write $\mathrm{Tgt}_{\mathcal{E}} = (\mathrm{Tgt}_{\mathcal{E}}, \mathrm{tgt})$ for the well-pointed endofunctor on $\mathcal{E}^{\rightarrow}$ defined as follows:

- (i) $\mathrm{Tgt}_{\mathcal{E}}$ sends $f \colon A \to B$ to the identity $\mathrm{id}_B \colon B \to B$, with the evident functorial action.
- (ii) $\mathrm{tgt} \colon \mathrm{Id}_{\mathcal{E}} \to \mathrm{Tgt}_{\mathcal{E}}$ is given at $f \colon A \to B$ by the square

$$\begin{array}{c} A \xrightarrow{f} B \\ f \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \xleftarrow{} B. \end{array}$$

**Proposition 2.3.19.** The category $\mathrm{Tgt}_{\mathcal{E}}$-Alg is isomorphic over $\mathcal{E}^{\rightarrow}$ to the full subcategory $\mathcal{E}_{\cong}^{\rightarrow} \hookrightarrow \mathcal{E}^{\rightarrow}$ of isomorphisms in $\mathcal{E}$.

**Lemma 2.3.20.** Let $(\mathcal{E}, \mathcal{M}, \mathsf{T}) \in \mathrm{ConfMnd}_{\mathsf{p}}^n$. The pointed endofunctor $\mathrm{Tgt}_{\mathcal{E}}$ on $\mathcal{E}^{\rightarrow}$ restricts to $\mathcal{E}_{\mathcal{M}}^{\rightarrow}$, and the restricted pointed endofunctor transfers along $\mathcal{E}_{\mathcal{M}}^{\rightarrow} \colon \tau_* \xleftrightarrow{\longleftrightarrow} \tau^! \colon \mathcal{E}^{\mathfrak{g}}$ to define a well-pointed endofunctor $\mathsf{T}^{\mathfrak{g}}$ on $\mathcal{E}^{\mathfrak{g}}$ whose unit is valued in $\mathcal{M}^{\mathfrak{g}}$.

*Proof.* That $\mathrm{Tgt}_{\mathcal{E}}$ restricts to $\mathcal{E}_{\mathcal{M}}^{\rightarrow}$ is evident. Per Definition 2.3.9 and Proposition 2.3.10, $\mathrm{Tgt}_{\mathcal{E}}$ transfers to define a well-pointed endofunctor $\mathsf{T}^{\mathfrak{g}}$ on $\mathcal{E}^{\mathfrak{g}}$ provided that the following pushout in $\mathcal{E}^{\mathfrak{g}}$ exists for all $(A, B, f) \in \mathcal{E}^{\mathfrak{g}}$:

$$\begin{array}{c} (A, B \sqcup_A TA, v_1) \xrightarrow{\tau_* \mathrm{tgt}_{\tau^!(A,B,f)}} (B, TB, \mathrm{id}_{TB}) \\ \epsilon_{(A,B,f)} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (A, B, f) \xrightarrow{} (X, Y, k). \end{array} \tag{2.9}$$

The pushout $X$ of the domain components is trivially $B$; the pushout square is absolute and thus preserved by $T$. Hence $Y$ is simply computed as a pushout of the codomain components:

$$\begin{array}{c} B \sqcup_A TA \xrightarrow{\hat{\tau}(f\tau_A)} TB \\ [\mathrm{id}, f] \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \xrightarrow{} h \longrightarrow Y. \end{array} \tag{2.10}$$

The top map is the pushout application of $\tau$ to $f\tau_A$ and thus in $\mathcal{M}$ by 2.3.6(c), since $f\tau_A$ is in $\mathcal{M}$. Hence the pushout (2.10) exists and the bottom map $h$ is in $\mathcal{M}$ by 2.3.6(a). The map $k \colon TY \to X$

20