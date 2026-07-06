3.1. PRELIMINARIES

### 3.1.3 Models of $(\infty, n)$-categories

Notation 3.1.3.1. We denote by $\text{ho}(M)$ the homotopy category of a model category $M$.

Construction 3.1.3.2. Let $n \in \mathbb{N} \cup \{\omega\}$. We will consider the model structure on $\text{Psh}(\Theta_n \times \Delta)$ obtained as the left Bousfield localization of the injective model structure on $\text{Fun}(\Theta_n^{op}, \text{Psh}(\Delta)) \cong \text{Psh}(\Theta_n \times \Delta)$ along $\text{W}_n$ (definition 1.1.2.15) where $\text{Psh}(\Delta)$ is endowed with the Kan-Quillen model structure. This model structure is nice according to [Rez10].

Definition 3.1.3.3. Let $n \in \mathbb{N} \cup \{\omega\}$. A model of $(\infty, n)$-categories is a model category $M$ which is linked by a zigzag of Quillen equivalences to $\text{Psh}(\Theta_n \times \Delta)$.

A globular object for a model of $(\infty, n)$-categories $M$ is a functor $\mathbf{D}_-: \text{G}_{\le n} \to M$ such that $\text{G}_{\le n} \to \text{ho } M$ is equivalent to the inclusion of globes $\text{G}_{\le n} \to \Theta_n \to \text{ho } \text{Psh}(\Theta_n \times \Delta)$.

Proposition 3.1.3.4 (Barwick, Schommer-Pries). Let $M, N$ be two models of $(\infty, n)$-categories and $\mathbf{D}_-: \text{G}_{\le n} \to M$, $\mathbf{D}_-: \text{G}_{\le n} \to N$ be two globular objects.

Let $i: M \to N$ be a left Quillen functor that preserves the globes up to a zigzag of weak equivalences. Then $i$ is a Quillen equivalence.

Proof. This is [BSP21, proposition 15.10].

Theorem 3.1.3.5 (Bergner). Let $A$ be a category of stratified presheaves on a Reedy elegant category endowed with a nice model structure. If $A$ is a model of $(\infty, n)$-categories, then $\text{tSeg}(A)$ is a model of $(\infty, n+1)$-categories.

Proof. This is a direct consequence of [BSP21, example 15.8] using the Quillen equivalence between $\text{Seg}(A)$ and $\text{tSeg}(A)$ given in theorem 3.1.2.13.

### 3.1.4 Gray module

Definition 3.1.4.1. A family of intelligent $n$-truncations for $n \in \mathbb{N} \cup \{\omega\}$ for a model category $A$ is a family of left Quillen functors $\tau_i^\cdot: (\mathbb{N} \cup \{\omega\})^{op} \to \text{End}(A)$ such that

- $\tau_i^\omega = id$,
- for any $n \le m$, $\tau_i^n \tau_m^\cdot = \tau_n^\cdot$,
- for any $n \le m$, the natural transformation $\tau_m^\cdot \to \tau_n^\cdot$ is an entire monomorphism,

Definition 3.1.4.2. Let $A$ be a category of stratified presheaves on an elegant Reedy category, endowed with a nice model structure. We suppose furthermore that the terminal element of $A$, denoted by $e$, is representable.

A Gray module structure for the model category $A$ is the data of

- a family of intelligent $n$-truncation for any $n \in \mathbb{N} \cup \{\omega\}$.
- a left Quillen functor $_\otimes_-: \text{tPsh}(\Delta)^1 \times A \to A$,
- for any $a$ in $A$, and any pair of stratified simplicial sets $K, L$, a natural morphism $K \otimes (L \otimes a) \to (K \times L) \otimes a$.

such that

109