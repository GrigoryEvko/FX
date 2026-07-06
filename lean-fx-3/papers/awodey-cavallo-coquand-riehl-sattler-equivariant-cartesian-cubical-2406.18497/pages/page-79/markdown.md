**Definition A.5.3** (fibration.fibration.FibStr). An *equivariant filling structure* on a family of types $A$ over $\Gamma$ is a family of operations $c_A^n$ in $\mathsf{Fill}_{\mathbb{P}^n} \Gamma A$ for $n : \mathbb{N}$ each of which is *equivariant*, meaning that for any $\sigma$ in $\Sigma_n$, we have the *equivariance equation*

$$c_A^n \gamma (\sigma r_0) a_0 a (\sigma r_1) = c_A^n (\gamma \sigma) r_0 a_0 (a \sigma) r_1 \tag{A.5.4}$$

for every $\gamma : \Gamma^S$, $r_0 : S$, $a_0 : A (\sigma (\gamma r_0))$, compatible partial section $a : (\Pi_{r:S} A (\gamma r))^+$, and $r_1 : S$.

We write $\mathsf{Fill} \Gamma A$ for the type of all equivariant filling structures on $A$. These types of structure are reflected in each universe, so we have e.g. $\mathsf{Fill} : \Pi_{\Gamma:\mathcal{V}} (\Gamma \to \mathcal{V}) \to \mathcal{V}$.

**Definition A.5.5** (fibration.fibration. $\vdash^{\mathsf{F}}\mathsf{Type}_-$). An *equivariant fibration* over $\Gamma$ is a family of types $A$ over $\Gamma$ paired with an equivariant filling structure.

In this setting, building the model of HoTT consists in showing that each operator on types lifts to an operator on equivariant filling structures, checking in each case that the output structure satisfies the equivariance equation (A.5.4). Let us check for instance that we can interpret substitution in types; the corresponding property in the external development is the stability of equivariant fibration structures under pullback.

**Definition A.5.6** (fibration.fibration. $\circ^{\mathsf{FS}}$). Let $A$ be a family of types over $\Gamma$ and let $\alpha : \Delta \to \Gamma$. Given $c_A$ in $\mathsf{Fill} \Gamma A$, we define $c_A \circ \alpha$ in $\mathsf{Fill} \Delta (A \circ \alpha)$ by

$$(c_A \circ \alpha)^n \gamma r_0 a_0 a r_1 := c_A^n (\alpha \circ \gamma) r_0 a_0 a r_1$$

and it is then clear that $c_A \circ \alpha$ is equivariant if $c_A$ is equivariant.

**A.6. The Frobenius condition.** Proving the Frobenius condition, Definition 3.4.1, amounts to defining the interpretation of $\Pi$-types. The corresponding result in the external, equivariant development is Proposition 5.3.2. A more detailed comparison between external and type-theoretic proofs of the Frobenius condition can be found in [HR24, Appendix B].

**Definition A.6.1.** Given a type family $A$ over $\Gamma$ and a type family $B$ over $\Gamma.A$, write $\Pi_A B$ for the family of types over $\Gamma$ defined by

$$(\Pi_A B) \gamma := \Pi_{a:A\gamma} B(\gamma, a).$$

To prove the Frobenius condition in this setting is to show that, given filling structures on $A$ and $B$, we have a filling structure on $\Pi_A B$. In fact the hypothesis of a filling structure on $A$ can be weakened: we only need a *transport structure* in the following sense.

**Definition A.6.2** (fibration.transport.TranspStr). Given a type $S$ and family of types $A$ over $\Gamma$, the type $\mathsf{Transp}_S \Gamma A$ of $S$-*transport structures* on $A$ is the type of operations $t_A$ which take $r_0 : S$ and $a_0 : A (\gamma r_0)$ and produce an element $t_A \gamma r_0 a_0$ in $\Pi_{r:S} A (\gamma r)$ such that $t_A \gamma r_0 a_0 r_0 = a_0$.

An *equivariant transport structure* on $A$ is a family of operations $t_A^n : \mathsf{Transp}_n \Gamma A$ for $n : \mathbb{N}$ each of which satisfies the equivariance equation

$$t_A^n \gamma (\sigma r_0) a_0 (\sigma r_1) = t_A^n (\gamma \sigma) r_0 a_0 r_1$$

for every $\gamma : \Gamma^S$, $r_0 : S$, $a_0 : A (\sigma (\gamma r_0))$, and $r_1 : S$. We write $\mathsf{Transp} \Gamma A$ for the type of equivariant transport structures on $A$.

*Remark A.6.3* (fibration.transport.transpAndFiberwiseToFibStr). It is immediate that any (equivariant) filling structure on a type induces an (equivariant) transport structure by restricting to the partial section whose cofibration is $\bot$. As in [ABCHFL21], one can conversely construct an equivariant filling structure on $A$ given an equivariant transport structure on $A$ and an equivariant filling structure on the constant family $A \gamma$ for every $\gamma : \Gamma$. This decomposition would be the key to interpreting higher inductive types following [CHM18; CH19], but we do not pursue this here.

79