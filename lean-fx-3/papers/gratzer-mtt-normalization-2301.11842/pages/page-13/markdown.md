Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:13

Intuitively, $\tau$ displays pairs of terms with their types over types. These two objects organize into presheaves through substitution on terms and types. With this in mind, the representability condition encodes context extension.

In order to adapt this to MTT, we can no longer consider just a category of contexts. The existence of multiple modes mandates that we consider a 2-functor of contexts $F : \mathcal{M}^{\text{coop}} \longrightarrow \mathbf{Cat}$. The action of modalities $F(\mu) : F(m) \longrightarrow F(n)$ gives the semantic equivalent of $-\{\mu\}$, while the 2-cell component $F(\alpha)$ interprets $\{\alpha\}$.

Each mode $m : \mathcal{M}$ is equipped with a morphism $\tau_m : \mathcal{T}_m^\bullet \longrightarrow \mathcal{T}_m : \mathbf{PSh}(F(m))$ representing the terms and types of mode $m$ and each modality $\mu : n \longrightarrow m$ induces a functor which acts by precomposition $F(\mu)^*$.

**Definition 3.2.** A model of MTT without any type constructors is a strict 2-functor $F : \mathcal{M}^{\text{coop}} \longrightarrow \mathbf{Cat}$ together with a collection of morphisms $\tau_m : \mathcal{T}_m^\bullet \longrightarrow \mathcal{T}_m : \mathbf{PSh}(F(m))$ such that $F(\mu)^*(\tau_n)$ is representable for each $\mu : n \longrightarrow m$.

Connectives are individually specified on top of this structure. For instance, the following pullback square in $\mathbf{PSh}(F(m))$ for each mode $m$ ensures closure under dependent sums:

$$\begin{array}{c} \sum_{A:\mathcal{T}_m} \sum_{B:\tau_m[A] \to \mathcal{T}_m} \sum_{a:\tau_m[A]} \tau_m[B(a)] \longrightarrow \mathcal{T}_m^\bullet \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \sum_{A:\mathcal{T}_m} \prod_{\cdot:\tau_m[A]} \mathcal{T}_m \longrightarrow \mathcal{T}_m \end{array} \tag{3.1}$$

Diagram 3.1 takes advantage of the model of extensional MLTT in a presheaf topos [Hof97] and we have written $\tau_m[A]$ to denote the specialization of $\tau_m$ (viewed as a dependent type over $\mathcal{T}_M$) with $A$. We will freely take advantage of this model and use our assumption of a hierarchy of Grothendieck universes to equip it with an infinite hierarchy of cumulative universes [HS97]. We refer to a family of presheaves as *small* if it is classified by a universe.

Dependent products $(\mu \mid A) \to B$ are specified by a similar pullback square but their encoding in MTT presents a slight complication. Recall that dependent products include a modality $(\mu \mid A) \to B$. In order to account for $\mu$, we use $F(\mu)^*$; if elements of $\mathcal{T}_m(X)$ represent types from mode $m$ in context $X : F(m)$, elements $F(\mu)^*(\mathcal{T}_n)(X)$ represent types from mode $n$ but in context $F(\mu)(X)$. Accordingly, the presence of dependent products is encoded by the following pullback square:

$$\begin{array}{c} \sum_{A:F(\mu)^*(\mathcal{T}_n)} \sum_{B:F(\mu)^*(\tau_n)[A] \to \mathcal{T}_m} \prod_{a:F(\mu)^*(\tau_n)[A]} \tau_m[B(a)] \longrightarrow \mathcal{T}_m^\bullet \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \sum_{A:F(\mu)^*(\mathcal{T}_n)} F(\mu)^*(\tau_n)[A] \to \mathcal{T}_m \longrightarrow \mathcal{T}_m \end{array} \tag{3.2}$$

Given $\mu : n \longrightarrow m$, we can specify the formation and introduction rules of $\langle \mu \mid - \rangle$ with another commuting square:

$$\begin{array}{c} F(\mu)^*\mathcal{T}_n^\bullet \longrightarrow \mathcal{T}_m^\bullet \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F(\mu)^*\mathcal{T}_n \longrightarrow \mathcal{T}_m \end{array} \tag{3.3}$$