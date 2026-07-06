Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:33

Overloading some notations from Theorem 5.1 we denote the units and co-units as

$$\begin{array}{l} \mathsf {c o p y} _ {\mathbf {y} U} ^ {\Xi}: 1 \rightarrow \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \circ \exists_ {\mathbf {y} U} ^ {\Xi} \\ \operatorname {c o n s t} _ {\mathbf {y} U} ^ {\Xi}: 1 \rightarrow \forall_ {\mathbf {y} U} ^ {\Xi} \circ \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \\ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Xi}: 1 \rightarrow \mathbb {Q} _ {\mathbf {y} U} ^ {\Xi} \circ \forall_ {\mathbf {y} U} ^ {\Xi} \\ \mathsf {d r o p} _ {u} \vDash \mathsf {c o n s t} _ {u}: 1 \Rightarrow \forall u \circ \lrcorner [ u ] \\ \mathsf {a p p} _ {u} \vDash \operatorname{reidx} _ {u}: 1 \Rightarrow \mathbb {Q} [ u ] \circ \forall u \\ \mathsf {d r o p} _ {\mathbf {y} U} ^ {\Xi}: \exists_ {\mathbf {y} U} ^ {\Xi} \circ \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \rightarrow 1 \\ \mathsf {a p p} _ {\mathbf {y} U} ^ {\Xi}: \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \circ \forall_ {\mathbf {y} U} ^ {\Xi} \rightarrow 1 \\ \mathsf {u n m e r} _ {\mathbf {y} U} ^ {\Xi}: \forall_ {\mathbf {y} U} ^ {\Xi} \circ \mathbb {Q} _ {\mathbf {y} U} ^ {\Xi} \rightarrow 1 \\ \mathsf {c o p y} _ {u} \vDash \mathsf {a p p} _ {u}: \lrcorner [ u ] \circ \forall u \Rightarrow 1 \\ \mathsf {c o n s t} _ {u} \vDash \mathsf {u n m e r} _ {u}: \forall u \circ \mathbb {Q} [ u ] \Rightarrow 1 \\ \end{array}$$

where reidx stands for reindex and unmer is the negation of mer which stands for meridian.

Proof. Via left Kan extension, precomposition and right Kan extension [Sta19], the pair of adjoint functors $\exists_U^{\Xi} \dashv \mathbb{J}_U^{\Xi}$ gives rise to a quadruple of adjoint functors $\exists_{\mathbf{y}U}^{\Xi} \dashv \mathbb{J}_{\mathbf{y}U}^{\Xi} \dashv \mathbb{V}_{\mathbf{y}U}^{\Xi} \dashv \mathbb{Q}_{\mathbf{y}U}^{\Xi}$ between the presheaf categories. (For the middle two, we can choose whether we derive them from $\exists_U^{\Xi}$ or from $\mathbb{J}_U^{\Xi}$; the resulting functors are naturally isomorphic. We will specify our choice when relevant.)

Notation 6.30. Again, due to the (purely sugarous) usage of shape variables, we may end up with variable renamings that are sugar for the identity, e.g.

$$\mathsf {a p p} _ {(v / u: \mathbb {U})}: \mathbb {J} [ v: \mathbb {U} ] \circ \forall (u: \mathbb {U}) \Rightarrow \Omega [ v: \mathbb {U}, u := v ]$$

$$\operatorname{reidx} _ {(v / u: \mathbb {U})}: \Omega [ v: \mathbb {U}, u := v ] \Rightarrow \mathbb {Q} [ v: \mathbb {U} ] \circ \forall (u: \mathbb {U})$$

are exactly the same 2-cells as

$$\mathsf {a p p} _ {(u: \mathbb {U})}: \mathbb {J} [ u: \mathbb {U} ] \circ \forall (u: \mathbb {U}) \Rightarrow 1$$

$$\operatorname{reidx} _ {(u: \mathbb {U})}: 1 \Rightarrow \mathbb {Q} [ u: \mathbb {U} ] \circ \forall (u: \mathbb {U}).$$

Whereas Theorem 5.1 clearly states the meaning of the functors introduced there, little can be said about the meaning of the functors introduced in Theorem 6.29 without knowing more about the multiplier involved. The following theorem clarifies the leftmost three functors:

Theorem 6.31 (Quantification). If $\sqcup \ltimes U$ is

(1) $\top$-slice fully faithful, then $\mathsf{drop}_{\mathbf{y}U}^{\Xi}$, $\mathsf{const}_{\mathbf{y}U}^{\Xi}$ and $\mathsf{unmer}_{\mathbf{y}U}^{\Xi}$ are natural isomorphisms.
(2) copointed, then we have

(a) $\mathsf{hide}_{\mathbf{y}U}^{\Xi}: \Sigma_{\mathbf{y}U}^{\Xi} \to \exists_{\mathbf{y}U}^{\Xi}$ (if $\top$-slice right adjoint),
(b) $\mathsf{spoil}_{\mathbf{y}U}^{\Xi}: \mathbb{J}_{\mathbf{y}U}^{\Xi} \to \Omega_{\mathbf{y}U}^{\Xi}$, which can be internalized (if $\top$-slice right adjoint) as $\exists u \Leftarrow \Sigma u: \mathsf{hide}_u \vDash \mathsf{spoil}_u: \mathbb{J}[u] \Rightarrow \Omega[u]$,
(c) $\mathsf{cospoil}_{\mathbf{y}U}^{\Xi}: \Pi_{\mathbf{y}U}^{\Xi} \to \forall_{\mathbf{y}U}^{\Xi}$, which can be internalized as $\Omega[u] \Leftarrow \mathbb{J}[u]: \mathsf{spoil}_u \vDash \mathsf{cospoil}_u: \Pi u \Rightarrow \forall u$.

(3) cartesian, then we have:

$$\exists_ {\mathbf {y} U} ^ {\Xi} = \Sigma_ {\mathbf {y} U} ^ {\Xi}, \qquad \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} = \Omega_ {\mathbf {y} U} ^ {\Xi}, \qquad \forall_ {\mathbf {y} U} ^ {\Xi} = \Pi_ {\mathbf {y} U} ^ {\Xi}.$$

The equalities assume that $\exists_U: \mathcal{W}/U \to \mathcal{W}$ is defined on the nose by $\exists_U(W, \psi) = W$ and that $\mathbb{J}_{\mathbf{y}U}^{\Xi}$ and $\forall_{\mathbf{y}U}^{\Xi}$ are constructed from $\exists_U^{\Xi}$ by precomposition and right Kan extension, respectively. Failing this, we only get natural isomorphisms.

Let us try to interpret this on a more intuitive level: