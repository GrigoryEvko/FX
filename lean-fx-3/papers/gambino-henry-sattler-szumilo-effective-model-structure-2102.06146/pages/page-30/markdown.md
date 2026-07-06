*Proof.* The first part is immediate since trivial Kan fibrations are Kan fibrations in simplicial sets. The second parts follows by adjointness using the weak factorisation systems of Theorem 4.2. $\square$

We now establish some formal properties of the two enriched weak factorisation systems, regarding the pushout-product, pushout-tensor and pullback-cotensor functors (cf. Remark 1.2).

# **Proposition 5.3** (Pushout-product properties).

(i) *In $\mathfrak{sE}$, cofibrations are closed under pushout product.*

(ii) *In $\mathfrak{sE}$, the pushout product of a cofibration and a trivial cofibration is a trivial cofibration.*

*Proof.* For part (i), recall that cofibrations in $\mathfrak{sSet}$ are closed under pushout product.$^{3}$ Since $S \mapsto \underline{S}$ preserves pushouts and products, it follows that the pushout product of generating cofibrations in $\mathfrak{sE}$ is a cofibration. The same follows for general cofibrations in $\mathfrak{sE}$ by Proposition 3.21. These pushout products exist by Lemma 2.13.

For part (ii), The result holds in $\mathfrak{sSet}$ by$^{4}$ [GZ67, Proposition IV.2.2] and thus it carries over to $\mathfrak{sE}$ by the argument of part (i). $\square$

**Lemma 5.4.** *Let $X \in \mathfrak{sE}$. For every finite simplicial set $K$, the tensor $K \cdot X$ exists and is given by $\underline{K} \times X$.*

*Proof.* Given $Y \in \mathfrak{sE}$, a morphism $X \rightarrow K \pitchfork Y$ consists of a family of morphisms $X_m \rightarrow Y_n^{(K \times \Delta[m])_n}$, natural in $m$ and dinatural in $n$. This corresponds to a family of morphisms $\underline{K \times \Delta[m]}_n \times X_m \rightarrow Y_n$, dinatural in $m$ and natural in $n$. Moreover:

$$\underline{K \times \Delta[m]}_n \times X_m = \underline{K}_n \times \underline{\text{Hom}([m], [n])} \times X_m.$$

Since $\int^{[m]} \underline{\text{Hom}([m], [n])} \times X_m = X_n$, such family of maps corresponds to a morphism $\underline{K}_n \times X_n \rightarrow Y_n$ natural in $n$, i.e., a morphism $\underline{K} \times X \rightarrow Y$ in $\mathfrak{sE}$. $\square$

**Proposition 5.5** (Pushout tensor properties). *Let $A \rightarrow B$ be a cofibration between finite simplicial sets. Then, the pushout tensor with $A \rightarrow B$ exists. Furthermore,*

(i) *it preserves trivial cofibrations,*

(ii) *it preserves cofibrations,*

(iii) *if $A \rightarrow B$ is a trivial cofibration, then it sends cofibrations to trivial cofibrations.*

*Proof.* The existence follows from Corollary 2.12 and Lemma 5.4. These other statements are dual to the ones of part (i) of Lemma 1.5 under the tensor-cotensor adjunction of Lemma 5.4. Note that for this conclusion it suffices to consider the underlying ordinary weak factorisation system of Lemma 3.6 so that we do not need to verify that the adjunction is enriched over $\text{Psh}\mathcal{E}$. $\square$

We now turn our attention to the cofibrations and the cofibrant objects in $\mathfrak{sE}$. From Section 3 and Proposition 4.1 these are exactly the maps with the left lifting property with respect to Kan fibrations. The next lemma provides us with a stock of cofibrant objects.

$^{3}$See [Hen18, Proposition 5.1.5] or [GSS19, Proposition 1.3.1] for the constructive version of this fact.

$^{4}$See [Hen18, Corollary 5.2.3] or [GSS19, Proposition 1.3.1] for the constructive version of this fact.

30