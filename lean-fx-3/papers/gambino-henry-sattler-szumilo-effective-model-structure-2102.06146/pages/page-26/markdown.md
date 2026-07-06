sending $w: U \rightarrow V$ in $[\Delta, \mathsf{Set}]$ and $i: A \rightarrow B$ in $\mathfrak{sE}$ to the map

$$H(V, B) \rightarrow H(V, A) \times_{H(U, A)} H(U, B) \quad (4.2)$$

in $[\mathcal{E}, \mathsf{Set}]$. Assume that domain and codomain of (4.2) have representing objects $Y$ and $X$, respectively (in particular, $Y$ is the $V$-weighted colimit of $B$). Then under the Yoneda embedding of $\mathcal{E}^{\mathrm{op}}$ into $[\mathcal{E}, \mathsf{Set}]$, (4.2) corresponds to a map $X \rightarrow Y$ in $\mathcal{E}$. We define this to be the *pushout weighted colimit* with $w: U \rightarrow V$ of $i: A \rightarrow B$ and denote it by $\widehat{\operatorname{colim}}^w i$. It forms a partial two-variable functor

$$\widehat{\operatorname{colim}}^{(-)}(=): [\Delta, \mathsf{Set}]^{[1]} \times \mathfrak{sE}^{[1]} \rightarrow [\mathcal{E}, \mathsf{Set}]^{[1]}.$$

Note that this is more general than a partially defined pushout construction of the two-variable weighted colimit functor because we do not require the individual colimits of $A$ with weight $V$ and $B$ with weights $U$ and $V$ to exist.

Unfolding the codomain of (4.2), we see that the relative latching map of $i: A \rightarrow B$ at level $m$ is precisely the pushout weighted colimit of $i$ with the coboundary inclusion $\partial \Delta^{\mathrm{op}}[m] \rightarrow \Delta^{\mathrm{op}}[m]$. Each side exist when the other does. This point of view is useful because it enables us to obtain pushout weighted colimits of $i$ with certain inclusions as cell complexes of relative latching maps.

We call a map $i$ a *Reedy complemented inclusion* if, for all $m$, the relative latching map of $i$ at level $m$ exists and is a complemented inclusion. This condition for $m < k$ suffices to guarantee the existence of the relative latching map at level $m = k$. Thus, in the inductive verification that a map is a Reedy complemented inclusion, the relevant latching maps always exist. Given a map $X \rightarrow Y$ in $\mathfrak{sE}$, the *relative matching map* at level $m$ is its weighted limit, i.e., pullback evaluation, at $\partial \Delta[m] \rightarrow \Delta[m]$, i.e., the map $X_m \rightarrow Y_m \times_{\operatorname{ev}_{\partial \Delta[m]} Y} \operatorname{ev}_{\partial \Delta[m]} X$. We call $X \rightarrow Y$ a *Reedy split epimorphism* if all its relative matching maps are split epimorphisms.

Following standard Reedy theory, Reedy complemented inclusions and Reedy split epimorphisms form a weak factorisation system. For this, we observe that instantiating the treatment of [RV14] and making use of Lemma 3.19, the use of (co)limits in $\mathfrak{sE}$ may be reduced to pushouts along complemented inclusions and pullbacks along split epimorphisms. We now relate this weak factorisation system to that of cofibrations and trivial fibrations, given in Theorem 4.2 (cf. also Proposition 4.1).

**Proposition 4.3.** *The weak factorisation system of cofibrations and trivial fibrations of Theorem 4.2 and Proposition 4.1 coincides with the weak factorisation system of Reedy complemented inclusions and Reedy split epimorphisms.*

*Proof.* Two weak factorisation systems coincide as soon as their right classes do. But, by inspecting the definition of a trivial fibration in Definition 1.3, a map in $\mathfrak{sE}$ is a Reedy split epimorphism if and only if it is a trivial Kan fibration. $\square$

The next lemma will be useful to simplify some saturation arguments in Section 6, as it allows us to avoid considering retracts, cf. the notion of a cell complex in Definition 3.16.

**Lemma 4.4.** *Every cofibration in $\mathfrak{sE}$ is an $I_{\mathfrak{sE}}$-cell complex.*

*Proof.* If $A \rightarrow B$ is a cofibration, then $B$ can be written as the colimit of its skeleta relative to $A$:

$$\operatorname{Sk}_A^{-1} B \longrightarrow \operatorname{Sk}_A^0 B \longrightarrow \operatorname{Sk}_A^1 B \longrightarrow \dots$$

26