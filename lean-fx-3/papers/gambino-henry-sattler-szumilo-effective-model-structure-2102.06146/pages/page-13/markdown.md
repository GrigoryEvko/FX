**Lemma 2.11.** *Assume that $\mathcal{E}$ is countably lextensive. Then the full subcategory of $[\omega, \mathcal{E}]$ consisting of sequences of complemented inclusions has finite limits which are preserved by the colimit functor (sending each sequence to its colimit in $\mathcal{E}$).*

*Proof.* First note that the category of sequences of complemented inclusions has finite limits by part (ii) of Lemma 2.10. Moreover, part (ii) of Lemma 2.9 implies that colimits of such sequences exist. It suffices to show that this colimit functor preserves terminal objects and pullbacks. Terminal objects are preserved since $\omega$ is a connected category (it has an initial object). For the case of pullbacks, we consider a span $A \rightarrow C \leftarrow B$ of sequences of complemented inclusions. We need to show that the map

$$\operatorname{colim}_{k \in \omega} A_k \times_{C_k} B_k \rightarrow \operatorname{colim} A \times_{\operatorname{colim} C} \operatorname{colim} B$$

is invertible. We decompose this map into three factors:

$$\begin{array}{ccc} \operatorname{colim}_{k \in \omega} A_k \times_{C_k} B_k & \longrightarrow & \operatorname{colim} A \times_{\operatorname{colim} C} \operatorname{colim} B. \\ \downarrow & & \uparrow \\ \operatorname{colim}_{k \in \omega} A_k \times_{\operatorname{colim} C} B_k & \longrightarrow & \operatorname{colim}_{i,j \in \omega} A_i \times_{\operatorname{colim} C} B_j \end{array}$$

The left map is invertible even before taking colimits because $C_k \rightarrow \operatorname{colim} C$ is a monomorphism. The bottom map is invertible because the diagonal functor $\omega \rightarrow \omega \times \omega$ is final (it has a left adjoint). The right map is invertible by universality of the van Kampen colimits $\operatorname{colim} A$ and $\operatorname{colim} B$ (part (ii) of Lemma 2.9). $\square$

Let $D$ be a small category. We say that a morphism $\varphi: F \rightarrow G$ in $\mathcal{E}^D$, is a *levelwise complemented inclusion* if its components $\varphi_d: F_d \rightarrow G_d$, for $d \in D$, are complemented inclusions in $\mathcal{E}$. Note that this is considerably less restrictive than asking for $\varphi$ to be a complemented inclusion in $\mathcal{E}^D$.

**Corollary 2.12.** *Let $D$ be a small category.*

- (i) *If $\mathcal{E}$ is lextensive, then pushouts along levelwise complemented inclusions exist, are computed levelwise and are van Kampen colimits in $\mathcal{E}^D$.*
- (ii) *If $\mathcal{E}$ is countably lextensive, then colimits of sequences of levelwise complemented inclusions exist, are computed levelwise and are van Kampen colimits in $\mathcal{E}^D$.*

*Proof.* This follows immediately from Lemmas 2.3 and 2.9. $\square$

**Lemma 2.13.** *Let $D$ be a small category. If $\mathcal{E}$ is lextensive, then the pushout products of levelwise complemented inclusions in $\mathcal{E}^D$ with arbitrary morphisms exist. Moreover, the pushouts involved are van Kampen.*

*Proof.* By universality of coproducts, levelwise complemented inclusions are closed under pullbacks. Thus a pushout computing a pushout product with a levelwise complemented inclusion is a pushout along a levelwise complemented inclusion. They are van Kampen by Corollary 2.12. $\square$

The following statement will be needed in Section 4 to prove Lemma 4.5.

13