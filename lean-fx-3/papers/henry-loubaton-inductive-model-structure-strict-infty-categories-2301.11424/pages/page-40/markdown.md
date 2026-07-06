to be the category whose objects are triples $(X, X', f: X \to \tau_k(X'))$ where $X$ and $X'$ are respectively $k$-marked and $(k+1)$-marked $\infty$-categories. By adjunction, these objects are in bijection with sequences:

$$X \xrightarrow{f} X'$$

where $X$ and $X'$ are respectively $k$-marked and $(k+1)$-marked $\infty$-categories. There is an adjunction

$$\text{pLimLax}_{i \in \{k, k+1\}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i) \xrightarrow[\substack{\perp \\ \beta_k]{\alpha_k} \text{pLimLax}_{i \in \mathbb{N}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$$

where the left adjoint $\alpha_k$ sends $X \to Y$ to the sequence

$$\emptyset \to \cdots \to \emptyset \to X \xrightarrow{f} Y \to Y \to \cdots \to Y \to \cdots$$

while the right adjoint $\beta_k$ sends $X_\bullet$ to

$$X_k \xrightarrow{f} X_{k+1}.$$

**4.13 Lemma.** Let $i: A \mapsto B$ be a cofibration between cofibrant objects in $\infty\text{-}\mathbf{Cat}^{+k}$ and $I_A B$ a relative cylinder object for $i$ (as in Proposition A.7). Let $\phi$ be the morphism in $\text{pLimLax}_{i \in \{k, k+1\}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$ given by the square:

$$\begin{array}{c} A \longrightarrow B \\ \downarrow \qquad \qquad \downarrow \\ B \longrightarrow I_A B \end{array}$$

There exists a morphism $\psi$ in $\text{pLimLax}_{i \in \{k, k+1\}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$ corresponding to a square

$$\begin{array}{c} B \coprod_A B \longrightarrow I_A B \coprod_B I_A B \\ \downarrow \qquad \qquad \qquad \downarrow \\ I_A B \coprod_B I_A B \longrightarrow W \end{array} \tag{1}$$

where $W$ is a relative cylinder object for $B \coprod_A B \to I_A B$, and such that $\alpha_k(\psi)$ is a relative cylinder for $\alpha_k(\phi)$.

Proof. One can first observe that the horizontal map $B \coprod_A B \mapsto I_A B \coprod_B I_A B$ is already a relative cylinder object for $A \mapsto B$. By definition of the putative lax-limit left semi-model structure, we then have to construct a square of shape (1), with $W$ a relative cylinder object for $B \coprod_A B \to I_A B$, and such that the canonical map

$$(I_A B \coprod_B I_A B) \coprod_{(B \coprod_A B)} (I_A B \coprod_B I_A B) \to W$$

is a weak equivalence.

40