also forced to take this version of display to be in a totally décalaged context; recall that décalage makes sense for arbitrary (non-fibrant) contexts.

$$\frac {\gamma : \Gamma \vdash_ {\mathrm{sm} ^ {n + 1}} A \gamma \text {type} _ {\ell}}{\gamma^ {+} : \Gamma^ {D} , a : \pi A ^ {\rho_ {\Gamma}} \gamma^ {+} \vdash_ {\mathrm{sm} ^ {n}} A ^ {d} \gamma^ {+} a \text {type} _ {\ell}} \quad \frac {\gamma : \Gamma \vdash_ {\mathrm{sm} ^ {n + 1}} t \gamma : A \gamma}{\gamma^ {+} : \Gamma^ {D} \vdash_ {\mathrm{sm} ^ {n}} t ^ {d} \gamma^ {+} : A ^ {d} \gamma^ {+} \pi t ^ {\rho_ {\Gamma}}}$$

We will prove that display is stable under substitution by $\sigma : \Delta \to \Gamma$ in $\mathcal{C}^{\Delta_{n+1}^+}$, and satisfies the expected formulas relating it to décalage:

$$(A ^ {\sigma}) ^ {d} \equiv (A ^ {d}) ^ {W _ {2} ^ {\pi A ^ {\rho_ {\Gamma}}} \sigma^ {D}}$$

$$(t ^ {\sigma}) ^ {d} \equiv (t ^ {d}) ^ {\sigma^ {D}}$$

$$(\gamma : \Gamma , a : A \gamma) ^ {D} \equiv (\gamma^ {+} : \Gamma^ {D}, a : \pi A ^ {\rho_ {\Gamma}} \gamma^ {+}, a ^ {\prime} : A ^ {d} \gamma^ {+} a) \tag {4.9}$$

$$[ \sigma , t ] ^ {D} \equiv [ \sigma^ {D}, \pi t ^ {\rho_ {\Delta}}, t ^ {d} ]. \tag {4.10}$$

Finally, we will also define substitutions that give an the actions of morphisms in $\Delta_{n+1}^+$ on matching telescopes and on types:

$$\frac {\gamma^ {-} : \pi \Gamma \vdash_ {\mathrm{sm} ^ {n}} A \gamma^ {-} \text {type} _ {\ell} \quad b : \mathbb {B} ^ {(n + 1) , (m + 1)}}{\gamma_ {n + 1} : \Gamma_ {n + 1} , \partial a : A _ {\partial (n + 1)} \gamma_ {n + 1} \vdash_ {d m} \operatorname{act} _ {\partial b} ^ {A} \gamma_ {n + 1} \partial a : \pi^ {n - m} A _ {\partial (m + 1)} (\Gamma^ {b} \gamma_ {n + 1})}$$

$$\frac {\gamma : \Gamma \vdash_ {\mathrm{sm} ^ {n + 1}} A \gamma \text {type} _ {\ell} \quad b : \mathbb {B} ^ {(n + 1) , (m + 1)}}{\gamma_ {n + 1} : \Gamma_ {n + 1} , \partial a : \pi A _ {\partial (n + 1)} \gamma_ {n + 1} , a : A _ {n + 1} \gamma_ {n + 1} \partial a}$$

$$\vdash_ {d m} \operatorname{act} _ {b} ^ {A} \gamma_ {n + 1} \partial a a : \pi^ {n - m} A _ {m + 1} (\Gamma^ {b} \gamma_ {n + 1}) (\operatorname{act} _ {\partial b} \gamma_ {n + 1} \partial a)$$

We will show that these compute to the identities (i.e. weakening) when $b = 1_{(n+1)}$, are functorial such that for $b_1 : \mathbb{B}^{(n+1), (m+1)}$ and $b_0 : \mathbb{B}^{(m+1), (k+1)}$:

$$\operatorname{act} _ {\partial b _ {0}} ^ {\pi^ {n - m} A} \left(\Gamma^ {b _ {1}} \gamma_ {n + 1}\right) \left(\operatorname{act} _ {\partial b _ {1}} ^ {A} \gamma_ {n + 1} \partial a\right) \equiv \operatorname{act} _ {\partial (b _ {1} \circ b _ {0})} ^ {A} \gamma_ {n + 1} \partial a \tag {4.11}$$

$$\operatorname{act} _ {b _ {0}} ^ {\pi^ {n - m} A} \left(\Gamma^ {b _ {1}} \gamma_ {n + 1}\right) \left(\operatorname{act} _ {\partial b _ {1}} ^ {\pi A} \gamma_ {n + 1} \partial a\right) \left(\operatorname{act} _ {b _ {1}} ^ {A} \gamma_ {n + 1} \partial a a\right) \equiv \operatorname{act} _ {b _ {1} \circ b _ {0}} ^ {A} \gamma_ {n + 1} \partial a a \tag {4.12}$$

and are also stable under substitution in the sense that for $\sigma : \Delta \to \Gamma$ in $\mathcal{C}^{\Delta_{n+1}^+}$:

$$\operatorname{act} _ {\partial b} ^ {A ^ {\pi \sigma}} \equiv \left(\operatorname{act} _ {\partial b} ^ {A}\right) ^ {W _ {2} ^ {A _ {\partial (n + 1)} \sigma_ {n + 1}}} \tag {4.13}$$

$$\operatorname{act} _ {b} ^ {A ^ {\sigma}} \equiv \left(\operatorname{act} _ {b} ^ {A}\right) ^ {W _ {2} ^ {A _ {n + 1}} W _ {2} ^ {\pi A _ {\partial (n + 1)} \sigma_ {n + 1}}}. \tag {4.14}$$

Given these, we can then define the functorial structure of the putative object $(\gamma : \Gamma, a : A \gamma)$: a morphism $b_1 : \mathbb{B}^{(n+1), (m+1)}$ acts on it by:

$$(\gamma : \Gamma , a : A \gamma) ^ {b} \gamma_ {n + 1} \partial a a \equiv [ \Gamma^ {b} \gamma_ {n + 1}, \operatorname{act} _ {\partial b} ^ {\pi A} \gamma_ {n + 1} \partial a, \operatorname{act} _ {b} ^ {A} \gamma_ {n + 1} \partial a a ] \tag {4.15}$$

Equations (4.11) and (4.12) tell us that the assignment $(\gamma : \Gamma, a : A \gamma)^b$ is functorial, while eqs. (4.13) and (4.14) tell us that the extension $[\sigma, t]$ is a morphism of presheaves.

The above is the complete list of constructions and theorems that we need in order to inductively define the type and term presheaves in the models $\mathbf{sm}^n$ and their context extension function.

55