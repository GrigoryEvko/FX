Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:39

7.3. Higher-dimensional pattern matching. Deriving HDPM from internal transposition for general multipliers is a bit more involved than it was for FFTraS (Section 2.4) because we have to use Eq. (7.2) instead of Eq. (7.1). However, we can construct an isomorphism \( i: \langle \forall u | A \uplus B \rangle \cong \langle \forall u | A \rangle \uplus \langle \forall u | B \rangle \) directly by translating from Section 2.4. Again, the map to the left is trivial by pattern matching (which is still the original eliminator for modal types!). The map to the right is given in either system by:

\[
\begin{array}{l} i: (\forall u. A \uplus B) \rightarrow (\forall u. A) \uplus (\forall u. B) \quad \boxed {\text {FFTraS}} \\ i \hat {c} = \text {unmer} \left(u. \text {case} \hat {c} u \text {of} \left\{ \begin{array}{l l} \text {inl} a & \mapsto \quad \text {mer} [ u ] (\text {inl} (\lambda u. a)) \\ \text {inr} b & \mapsto \quad \text {mer} [ u ] (\text {inr} (\lambda u. b)) \end{array} \right\}\right) \\ i: \langle \forall u | A \uplus B \rangle \rightarrow \langle \forall u | A \rangle \uplus \langle \forall u | B \rangle \quad \boxed {\text { MTraS }} \\ i \hat {c} = \text {unmer} _ {u} \cdot_ {\forall u} \text {case} (\text {app} _ {u} \cdot_ {\exists [ u ]} \hat {c} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}) \text {of} \left\{ \begin{array}{l} \text {inl} a \mapsto \text {mod} _ {\langle [ u ]} (\text {inl} (\text {mod} _ {\forall u} (a _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}}))) \\ \text {inr} b \mapsto \text {mod} _ {\langle [ u ]} (\text {inr} (\text {mod} _ {\forall u} (b _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}}))) \end{array} \right\}. \\ \end{array}
\]

## 8. ADDITIONAL TYPING RULES

In this section, we add a few extensions to MTraS in order to reason about boundaries, and in order to recover all known presheaf operators in Section 10.

8.1. Subobject classifier. We add a universe of propositions (semantically the subobject classifier) Prop :  \( U_{0} \) , with implicit encoding and decoding operations à la Coquand. This universe is closed under logical operators and weak DRAs [Nuy20a, §6.5]. This is necessary to talk about  \( \Psi \)  and  \( \Phi \) . We identify all proofs of the same proposition.

8.2. Boundary predicate. We add the following shape context constructor:

|  SHP-CTX-BOUNDARY  |   |
| --- | --- |
|  X shpctx | U shape  |
|  X, u : ∂U shpctx  |   |

modelling \(\llbracket \mathbb{X}, u : \partial \mathbb{U} \rrbracket = \llbracket \mathbb{X} \rrbracket \ltimes \partial U\) (Definition 6.23). Write \((u \in \partial \mathbb{U})\) for the presheaf morphism that includes \(\llbracket \mathbb{X}, u : \partial \mathbb{U} \rrbracket\) in \(\llbracket \mathbb{X}, u : \mathbb{U} \rrbracket\). We add a predicate of the same name \(\mathbb{X}, u : \mathbb{U} \mid \cdot \vdash u \in \partial \mathbb{U} : \text{Prop}\) corresponding in the model to this subobject \(\llbracket \mathbb{X}, u : \partial \mathbb{U} \rrbracket \subseteq \llbracket \mathbb{X}, u : \mathbb{U} \rrbracket\). Note that, since the direct boundary was not defined by pullback, the boundary predicate is not preserved by shape substitution \(\sigma : \llbracket \mathbb{X}_1 \rrbracket \to \llbracket \mathbb{X}_2 \rrbracket\), i.e. \(\langle \Omega[\sigma, u := u] | (u \in \partial \mathbb{U})_{\mathbb{X}_2} \rangle\) is not in general isomorphic to \((u \in \partial \mathbb{U})_{\mathbb{X}_1}\).

If we had modal type formers for left adjoints, then we could define the boundary predicate as  \( (\top,\mathbf{\Omega}_{[u\in\partial\mathbb{U}]}^{\Sigma(u\in\partial\mathbb{U})}) \) . However, MTT does not support such type formers and we do not know how to do this \( ^{19} \)  so we simply axiomatize the predicate by decreeing for every type X, u : U |  \( \Gamma\vdash A \)  type an isomorphism

\[
(u \in \partial \mathbb {U}) \rightarrow A \cong \left\langle \Pi (u \in \partial \mathbb {U}) \mid \left\langle \Omega [ u \in \partial \mathbb {U} ] \mid A [ \mathbf {\alpha} _ {\text { const } (u \in \partial \mathbb {U})} ^ {\text { drop } (u \in \partial \mathbb {U})} ] \right\rangle\right\rangle . \tag {8.1}
\]

\( ^{19} \) It is worth noting that  \( \Sigma^{\sigma\dagger} \)  is a parametric right adjoint so the work by Gratzer et al. [GCK \( ^{+} \) 22] could be relevant.