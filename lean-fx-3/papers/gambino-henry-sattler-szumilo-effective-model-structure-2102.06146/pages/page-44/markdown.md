By induction on $k$, we extend to a fibration $X_k \to A_k$. The maps $X_k \to X_{k+1}$ are cofibrations by part (i). In the end, we take the colimit and obtain a map $Y \to B$. By effectivity, it pulls back to the maps $X_k \to A_k$. It is a fibration by part (iii) of Lemma 3.18. Note that $Y$ is cofibrant by Lemma 3.9. $\square$

**Lemma 8.12.** *The class $\mathcal{H}$ is closed under codomain retracts.*

*Proof.* This is an instance of Lemma 8.4. $\square$

**Proposition 8.13** (Fibration extension property). *Trivial cofibrations in $\mathfrak{S}_{\mathrm{cof}}$ have the fibration extension property.*

*Proof.* We have to show that $\mathcal{H}$ includes all trivial cofibrations between cofibrant objects. By Proposition 3.17, any such trivial cofibration can be written as a codomain retract of a sequential colimit of pushouts of countable coproducts of tensors with objects of $E$ of maps in $J_{\mathfrak{S}_{\mathrm{cof}}}$. By induction, all the stages of the sequential colimit are cofibrant. This means that the above pushout squares all consist of cofibrant objects. The claim now follows starting from Corollary 8.8 using the closure properties of $\mathcal{H}$ given by Lemmas 8.9, 8.10, 8.11 and 8.12. $\square$

## 9 The effective model structure

The main goal of this section is to establish the existence of the effective model structure. Since the categories with which we work have finite limits but do not necessarily have finite colimits, it is appropriate to consider a slight generalisation of the usual notion of a model structure. For a category $\mathcal{E}$ with an initial object and a terminal object, a *model structure* on $\mathcal{E}$ consists of three classes of maps $\mathbf{W}$, $\mathbf{C}$, $\mathbf{F}$ such that

- $(\mathbf{C}, \mathbf{F} \cap \mathbf{W})$ and $(\mathbf{C} \cap \mathbf{W}, \mathbf{F})$ are weak factorisation systems;
- $\mathbf{W}$ satisfies the 2-out-of-3 property;
- $\mathcal{E}$ has pushouts along maps in $\mathbf{C}$;
- $\mathcal{E}$ has pullbacks along maps in $\mathbf{F}$.

It can then be shown that $\mathbf{W}$ is closed under retracts, as the known proof of this fact (see [JT07, Proposition 7.8] and [Rie14, Lemma 11.3.3]) applies also assuming only the restricted limits and colimits above. Thus, when $\mathcal{E}$ is finitely complete and cocomplete, this notion is equivalent to the usual one. Similarly, a model structure is determined by two of its three classes of maps also in this setting.

Let us now fix a countably lextensive category $\mathcal{E}$. The existence of the effective model structure on $\mathfrak{S}_{\mathrm{cof}}$ will be a formal consequence of the Frobenius property of Section 7, the (trivial) fibration extension property of Section 8, and elementary properties of the two weak factorisation systems of Theorem 4.2. To this end, we encapsulate what is used from Section 8 as a collection of extension operations that all follow the same pattern.

**Lemma 9.1.** *The following hold in $\mathfrak{S}_{\mathrm{cof}}$.*

44