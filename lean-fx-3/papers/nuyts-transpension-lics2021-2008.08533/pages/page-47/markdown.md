Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:47

Proof. We strictly the right hand sides below:

$$\begin{array}{l} \alpha : \Psi_{u} A (\hat{x}.R) : \cong (\hat{x} : (. : u \in \partial U) \to A) \times \langle \langle [u] \mid R \rangle, \\ \text{in} \Psi_{u} (.a) r := \alpha^{-1}(\lambda..a, \text{mod}_{[u]} r), \\ \text{out} \Psi \cdot_{\forall u} q := \text{unmer}_{u} \cdot_{\forall u} \pi_{2}(\alpha(q)). \end{array}$$

The fact that this is isomorphic to $A$ on the boundary follows from pole Theorem 9.1

Obviously then the transpension type $\langle [u] \mid T \rangle$ is also implementable from the $\Psi$-type as $\Psi_{u} \text{Unit} (.T)$.

10.4. Transpensivity. The $\Phi$-rule is extremely powerful but not available in all systems. However, when the codomain $C$ is a $\Psi$-type, then the in$\Psi$-rule is actually quite similar to the $\Phi$-rule if we note that sections of the $\Psi$-type are essentially elements of $R$. As such, we take an interest in types that are very $\Psi$-like. We have a monad (idempotent if $\mathbb{U}$ is $\top$-slice fully faithful)

$$\bar{\Psi}_{u} A := \Psi_{u} (.A) \left( \hat{x}. \langle \forall u \mid A \text{ext} \{ u \in \partial \mathbb{U} \ ? \ \hat{x} \ . \} [\mathbb{A}_{\text{reidx}_{u}}^{\text{app}_{u}}] \rangle \right),$$

where $A \text{ext} \{ \varphi \ ? \ a \}$ is the type of elements of $A$ that are equal to $a$ when $\varphi$ holds:

$$A \text{ext} \{ \varphi \ ? \ a \} := (x : A) \times ((. : \varphi) \to (x \equiv_{A} a)).$$

Definition 10.3. A type is transpensive over $u$ if it is a monad-algebra for $\bar{\Psi}_{u}$.

For $\top$-slice fully faithful and shard-free multipliers, $\Phi$ entails that all types are transpensive. For other systems, the universe of $u$-transpensive types will still be closed at least semantically under many interesting type formers, allowing to eliminate to these types in a $\Phi$-like way.

10.5. Glue, Weld, mill. Glue$\{A \leftarrow (\varphi \ ? \ T \ ; \ f)\}$ and Weld$\{A \to (\varphi \ ? \ T \ ; \ g)\}$ are similar to Strict but extend unidirectional functions. Orton and Pitts [OP18] already show that Glue [CCHM17, NVD17] can be implemented by strictifying a pullback along $A \to (\varphi \to A)$ [ND18b] which is definable internally using a $\Sigma$-type. Dually, Weld [NVD17] can be implemented if there is a type former for pushouts along $\varphi \times A \to A$ where $\varphi : \text{Prop}$ [Nuy20a, §6.3.3], which is sound in all presheaf categories.

Finally, mill [ND18b] states that $\forall (u : \mathbb{U})$ preserves Weld and is provable by higher-dimensional pattern matching (where $\circledast$ is the applicative operation of the modal type):

$$\begin{array}{l} \text{mill} : \langle \forall u \mid \text{Weld} \{ A \to (\varphi \ ? \ T \ ; \ g) \} \rangle \\ \quad \to \text{Weld} \{ \langle \forall u \mid A \rangle \to (\langle \forall u \mid \varphi \rangle \ ? \ \langle \forall u \mid T \rangle \ ; \ (\text{mod}_{\forall u} g) \circledast \sqcup) \} \end{array}$$

$$\text{mill } \hat{w} = \text{unmer}_{u} \cdot_{\forall u}$$

$$\text{case } (\text{app}_{u} \cdot_{[u]} (\hat{w}_{\text{const}_{u}}^{\text{drop}_{u}})) \text{ of } \left\{ \begin{array}{l} \text{weld } a \mapsto \text{mod}_{[u]} (\text{weld } (\text{mod}_{\forall u} (a_{\text{reidx}_{u}}^{\text{app}_{u}}))) \\ \varphi \ ? \ t \mapsto \text{mod}_{[u]} (\text{mod}_{\forall u} (t_{\text{reidx}_{u}}^{\text{app}_{u}})) \end{array} \right\}.$$

In the first clause, we get an element $a : A$ and can proceed as in Section 7.3. In the second clause, we are asserted that $\varphi$ holds (call the witness $p$) so that the left hand Weld-type equals $T$, and we are given $t : T$. Then inside the meridian constructor $\text{mod}_{[u]}$ we know that $\langle \forall u \mid \varphi \rangle$ holds as this is proven by $\text{mod}_{\forall u} (p_{\text{reidx}_{u}}^{\text{app}_{u}})$; hence the Weld-type in the codomain