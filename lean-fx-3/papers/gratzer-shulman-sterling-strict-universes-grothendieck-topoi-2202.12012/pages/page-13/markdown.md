STRICT UNIVERSES FOR GROTHENDIECK TOPOI

13

Next, observe that $f$ classifies $i^*P \rightarrow i^*P$ and this family extends along the monomorphism $m: i^*P \rightarrow \mathbf{1}$ to the family $\mathbf{1} \rightarrow \mathbf{1}$. However, there is no morphism classifying $\mathbf{1} \rightarrow \mathbf{1}$ that restricts to $f$ along $m$. Such a morphism would correspond to a $\mathsf{V}$-small presheaf $G: \mathcal{C}^{\mathsf{op}} \rightarrow \mathsf{V}$. If such a presheaf were to restrict correctly to both $i^*f_{01}$ and $i^*f_{10}$ correctly, it would need to satisfy $G_{00} = \mathbf{2}$ and $G_{00} = \mathbf{1}$, which is an impossibility. ■

### 3. Generalities on descent and $\kappa$-compactness

In preparation for our universe construction, we recall notions of descent and compactness together and develop the required theory. Accordingly, fix a Grothendieck topos $\mathcal{E}$. Unless specifically mentioned otherwise, we shall assume that all regular cardinals are infinite.

In Section 1 we observed that the natural notion of morphism between generic maps $\pi$, $\rho$ for a universe is not a merely a commuting square $\pi \rightarrow \rho$ but rather a *cartesian* square; only the latter ensures that a family classified by $\pi$ is also classified by $\rho$. While $\mathcal{E} \rightarrow$ readily adopts the essential characteristics of $\mathcal{E}$ (for instance, it is also a Grothendieck topos) the wide subcategory restricting to cartesian squares is not even cocomplete. We first recall the descent properties of $\mathcal{E}$ to show that this subcategory is closed under coproducts, filtered colimits and pushouts along monomorphisms (Lemma 3.1.4).

In Section 2 we worked with a universe of presheaves valued in small sets. While convenient, this definition of smallness relies on a choice of presentation of a topos as a particular category of presheaves. Under mild restrictions, however, $\tilde{S}_{\mathsf{V}}$ coincides with the class of relatively *compact* morphisms. Compactness is a 'presentation-invariant' notion and thereby readily available in $\mathcal{E}$. We recall the theory of $\kappa$-compactness in $\mathcal{E}$. We show that for sufficiently large $\kappa$, the class of relatively $\kappa$-compact morphisms form a universe satisfying (U1–7) closed under certain colimits (Lemma 3.2.7 and Theorem 3.3.9).

#### 3.1. DESCENT IN A GROTHENDIECK TOPOS.

3.1.1. DEFINITION. A diagram $J: \mathcal{D} \rightarrow \mathcal{E}$ is said to satisfy descent when for any cartesian natural transformation $\alpha: K \rightarrow J$, the induced morphisms $\alpha_d \rightarrow \operatorname{colim}_{d \in \mathcal{D}} \alpha_d$ in $\mathcal{E} \rightarrow$ are cartesian for each $d \in \mathcal{D}$, i.e. the following square is cartesian:

$$\begin{array}{c} K(d) \longrightarrow \operatorname{colim}_{\mathcal{D}} K \\ \downarrow \quad \downarrow \\ J(d) \longrightarrow \operatorname{colim}_{\mathcal{D}} J \end{array}$$

3.1.2. REMARK. We caution the reader that the usages of the word *descent* here and in (U7) are not identical. A diagram $F: \mathcal{D} \rightarrow \mathcal{E}$ satisfying descent essentially stipulates that we may fully characterize families over $\operatorname{colim} F$ by considering cartesian diagrams of families over $F(i)$. In particular, all categorical structures from the latter *descend* to the former. In contrast, (U7) states that a specific property—that of being $\mathcal{S}$-small—is