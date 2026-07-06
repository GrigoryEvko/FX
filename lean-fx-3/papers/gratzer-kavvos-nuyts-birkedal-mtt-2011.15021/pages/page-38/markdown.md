11:38

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

can also prove it in a more abstract way: we paste together the two pullback squares

$$\begin{array}{ccc} \mathbf{P}_{[\mathbf{\Omega}_\mu]^*\tau_n}(\widetilde{\mathcal{T}}_m) & \xrightarrow{\phi_{\widetilde{\mathcal{T}}_m}} & \mathbf{P}_{\tau_m}(\widetilde{\mathcal{T}}_m) & \xrightarrow{\text{lam}} & \widetilde{\mathcal{T}}_m \\ \mathbf{P}_{[\mathbf{\Omega}_\mu]^*\tau_n}(\tau_m) & \downarrow & \mathbf{P}_{\tau_m}(\tau_m) & \downarrow & \downarrow & \tau_m \\ \mathbf{P}_{[\mathbf{\Omega}_\mu]^*\tau_n}(\mathcal{T}_m) & \xrightarrow{\phi_{\mathcal{T}_m}} & \mathbf{P}_{\tau_m}(\mathcal{T}_m) & \xrightarrow{\Pi} & \mathcal{T}_m \end{array}$$

The square on the right is the pullback that interprets $\Pi$ in the natural model $\tau_m$. The square on the left is a naturality square of the natural transformation

$$\phi : \mathbf{P}_{[\mathbf{\Omega}_\mu]^*\tau_n}(-) \Rightarrow \mathbf{P}_{\tau_m}(-)$$

which exists because the pullback square (7.2) defines a morphism of polynomials. Moreover, the naturality squares of $\phi$ are cartesian: see [New18, §§1.2.16–1.2.18]. $\square$

This theorem is a particularly flexible tool, as many modalities naturally form DRAs, and it is easier to check the DRA conditions than MTT model conditions as summarized in Definition 5.6. As a first example of this flexibility we show that it leads to an almost immediate proof of consistency.

**Corollary 7.2.** *No matter what the mode theory is, there is no term $\cdot \vdash M : \text{Id}_\mathbb{B}(\text{tt}, \text{ff}) \otimes m$. In other words, MTT is consistent.*

*Proof.* Suppose that we have a model of MLTT with one universe in some category $\mathcal{C}$. We may construct a functor $\mathcal{M}^{\text{coop}} \to \text{Cat}$ by sending every mode to $\mathcal{C}$, and everything else to the identity. This is strictly 2-functorial, and each identity functor is a DRA. Hence, by Theorem 7.1 there is a model of MTT in which each mode is interpreted by $\mathcal{C}$. Therefore, if a term $M : \text{Id}_\mathbb{B}(\text{tt}, \text{ff})$ were definable in MTT, we would have a term of that type in every model of MLTT. But MLTT itself is consistent: see [Coq19] for a short proof. $\square$

**7.3. DRAs from right adjoints.** Having established that a series of models of MLTT related by DRAs can be used to interpret MTT, we now turn to the problem of constructing those DRAs themselves. We shall prove a lemma that allows us to lift any well-behaved right adjoint to a DRA. Versions of this result have appeared before, both in the paper on DRAs [BCM$^+$20, Lemma 17], and in a technical report By the third author [Nuy18, Prop. 2.1.4].

In Section 5.3 we discussed the notion of a *strict* morphism of natural models. Using the same notation we define the following weaker notion.

**Definition 7.3.** *A weak morphism of natural models $(\mathcal{C}, \mathcal{T}_c) \to (\mathcal{D}, \mathcal{T}_d)$ consists of a functor $F : \mathcal{C} \to \mathcal{D}$, and a commuting square*

$$\begin{array}{ccc} \widetilde{\mathcal{T}}_c & \xrightarrow{\widetilde{\varphi}} & F^*\widetilde{\mathcal{T}}_d \\ \tau_c & \downarrow & \downarrow & F^*\tau_d \\ \mathcal{T}_c & \xrightarrow{\varphi} & F^*\mathcal{T}_d \end{array}$$