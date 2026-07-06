**Corollary 4.3.8.** Let $P: \mathcal{E} \rightarrow \mathcal{B}$ and $Q: \mathcal{F} \rightarrow \mathcal{B}$ be Grothendieck fibrations and $V: (\mathcal{F}, Q) \rightarrow (\mathcal{E}, P)$ be a fibered functor over $\mathcal{E}$. Given a morphism $\alpha: b \rightarrow b'$ in $\mathcal{B}$ and objects $\xi \in \left( \overline{\prod}_P V \right)_b$ and $\xi' \in \left( \overline{\prod}_P V \right)_{b'}$, the morphisms $\beta: \xi \rightarrow \xi'$ in $\overline{\prod}_P V$ over $\alpha$ are those natural transformations as in Proposition 4.3.7 which are valued in $Q$-cartesian morphisms. These correspond in particular to natural isomorphisms $\theta: \xi^\dagger \alpha^* \rightarrow \alpha^* \xi'^\dagger$ such that

$$\begin{array}{ccc} \mathcal{E}_b & \xrightarrow{\xi^\dagger} \mathcal{F}_b & \xrightarrow{V_b} \mathcal{E}_b \\ \alpha^* \uparrow & \theta & \alpha^* \uparrow & \cong \uparrow \alpha^* \\ \mathcal{E}_{b'} & \xrightarrow{\xi'^\dagger} \mathcal{F}_{b'} & \xrightarrow{V_{b'}} \mathcal{E}_{b'} \end{array} = \begin{array}{ccc} \mathcal{E}_b & \xlongequal{\quad} \mathcal{E}_b \\ \alpha^* \uparrow & \uparrow \alpha^* \\ \mathcal{E}_{b'} & \xlongequal{\quad} \mathcal{E}_{b'} \end{array}$$

Since the goal is to build a cellular notion of composable structure for extension operations, we are interested in colimits in pushforward categories. Here we need Van Kampen colimits in the base.

**Notation 4.3.9.** Fix a Grothendieck fibration $P: \mathcal{E} \rightarrow \mathcal{B}$, a diagram $b: \mathcal{K} \rightarrow \mathcal{B}$, and a cocone $\beta: b \rightarrow \Delta b_0$ in $\mathcal{B}$. Then we have a functor and natural transformation

$$\begin{array}{ccc} \mathcal{K} \times_{\mathcal{B}} \mathcal{E} & \xleftarrow{\text{pull}_P \beta} & \mathcal{K} \times \mathcal{E}_{b_0} \\ & \searrow \text{lift}_P \beta & \searrow \\ & \searrow & P^* \Delta b_0 \\ & \mathcal{E} & \end{array}$$

as follows: $\text{pull}_P \beta$ sends $(k, e)$ to $(k, \beta_k^* e)$ and $\text{lift}_P \beta$ sends $(k, e)$ to $\overline{\beta_k} e: \beta_k^* e \rightarrow e$.

**Lemma 4.3.10.** Let $P: \mathcal{E} \rightarrow \mathcal{B}$ and $Q: \mathcal{F} \rightarrow \mathcal{B}$ be Grothendieck fibrations and $V: (\mathcal{F}, Q) \rightarrow (\mathcal{E}, P)$ be a fibered functor over $\mathcal{E}$ which is itself an isofibration. Let a small category $\mathcal{K}$ and diagram

$$\begin{array}{ccc} \mathcal{K} & \xrightarrow{d} & \overline{\prod}_P V \\ & \searrow b \searrow_{\mathcal{B}} & \swarrow P_{\varepsilon} V \end{array}$$

be given, and suppose that $b: \mathcal{K} \rightarrow \mathcal{B}$ admits a colimit that is Van Kampen for $P$ and $Q$. Then the colimit of $d: \mathcal{K} \rightarrow \overline{\prod}_P V$ exists and is preserved by $P_{\varepsilon} V$.

*Proof.* By assumption, we have a colimit cocone $\beta: b \rightarrow \Delta b_0$. Consider the transpose $d^\dagger: \mathcal{K} \times_{\mathcal{B}} \mathcal{E} \rightarrow \mathcal{F}$. For each $e \in \mathcal{E}_{b_0}$, the composite

$$\mathcal{K} \xrightarrow{\mathcal{K} \times e} \mathcal{K} \times \mathcal{E}_{b_0} \xrightarrow{\text{pull}_P \beta} \mathcal{K} \times_{\mathcal{B}} \mathcal{E}$$

factors through $\mathcal{K} \times_{\mathcal{B}} \mathcal{E}_{\mathcal{B}\text{-cart}}$. Because $d$ is a diagram in the cartesian pushforward, its transpose $d^\dagger$ restricts to a functor $\mathcal{K} \times_{\mathcal{B}} \mathcal{E}_{\mathcal{B}\text{-cart}} \rightarrow \mathcal{F}_{\mathcal{B}\text{-cart}}$. From the diagram

$$\begin{array}{ccc} \mathcal{K} & \xrightarrow{\text{pull}_P \beta (\mathcal{K} \times e)} & \mathcal{K} \times_{\mathcal{B}} \mathcal{E}_{\mathcal{B}\text{-cart}} \xrightarrow{d^\dagger} \mathcal{F}_{\mathcal{B}\text{-cart}} \\ & \searrow b & \searrow \\ & \searrow & \searrow Q_{\mathcal{B}\text{-cart}} \end{array}$$

it follows by 4.3.4(a) that the family $d^\dagger \circ \text{pull}_P \beta: \mathcal{K} \times \mathcal{E}_{b_0} \rightarrow \mathcal{F}$ admits colimits pointwise in $e \in \mathcal{E}_{b_0}$, defining a family of colimits $f_0: \mathcal{E}_{b_0} \rightarrow \mathcal{F}_{\mathcal{B}\text{-cart}}$ and colimit cocones $\phi: d^\dagger \circ \text{pull}_P \beta \rightarrow f_0 \pi_1$.

50