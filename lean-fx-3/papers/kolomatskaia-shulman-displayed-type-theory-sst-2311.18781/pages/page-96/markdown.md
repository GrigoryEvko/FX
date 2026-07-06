4.5.5.7 Correctness of semi-simplicial types. Recall that our definition of semi-simplicial types $\mathsf{SST}_{\ell}$ is as a displayed coinductive type with $\Phi \equiv ()$, $A \equiv \mathsf{Type}_{\ell}$, and $\mathcal{B} \ a \equiv \{x : \mathsf{El} \ a\}$. Therefore, the construction in section 4.5.2 simplifies as follows:

$$\vdash_{sm} X^{\partial n} \text{ tel} \quad \partial x : X^{\partial n} \vdash_{sm} X^n \partial x \text{ tel} \quad \vdash_{sm} X^{\partial 0} \equiv ()$$

$$\vdash_{sm} X^{\partial (n+1)} \equiv (\partial x : X^{\partial n}, x : X^n \partial x) \quad \vdash_{sm} X^0 \equiv \mathsf{Type}_{\ell}$$

$$\partial x : X^{\partial n}, x : X^n \partial x \vdash_{sm} h_n \partial x \ x : \mathsf{Type}_{\ell} \quad x : X^0 \vdash_{sm} h_0 \ x \equiv x$$

$$\partial x : X^{\partial n}, x : X^n \partial x, x' : X^{n+1} [ \partial x, x ] \vdash_{sm} h_{n+1} [ \partial x, x ] x' \equiv h_n \partial x \ x$$

$$\partial x : X^{\partial n}, x : X^n \partial x, b : \mathsf{El} (h_n \partial x \ x) \vdash_{sm} t_n \partial x \ x \ b : (X^{\partial n})^d \partial x$$

$$x : X^0, b : \mathsf{El} (h_0 \ x) \vdash_{sm} t_0 \ x \ b \equiv [ ]$$

$$\partial x : X^{\partial n}, x : X^n \partial x, x' : X^{n+1} [ \partial x, x ], b : \mathsf{El} (h_n \partial x \ x) \vdash_{sm} t_{n+1} [ \partial x, x ] x' \ b \equiv [ t_n \partial x \ x \ b, x' \ b ]$$

$$\partial x : X^{\partial n}, x : X^n \partial x \vdash_{sm} X^{n+1} [ \partial x, x ] \equiv (b : \mathsf{El} (h_{n-1} \partial x)) \to (X^n)^d \langle \partial x, t_n \partial x \ x \ b \rangle \ x$$

We will prove inductively that

$$X^{\partial n} \equiv \Gamma^{\Delta_{n-1}} \quad \text{and} \quad X^n \equiv \Theta^{\partial \mathcal{L}(n)} \to \mathsf{Type}_{\ell}.$$

This will imply that $\mathsf{SST} = \lim_n X^{\partial n}$ is a classifying context for all of $\Delta$. The claim about $X^n$ clearly inductively implies the claim about $X^{\partial n}$. Also it is easy to show inductively that $h_n \equiv B^{(0)}$. So it remains to say something useful about $t_n$.

Let $I_n$ be the subcategory of $2 \times \Delta_n$ containing all the objects except $(1, \langle n \rangle)$, and let $J_n = \{0\} \times \Delta_n$ regarded as a sieve in $I_n$. The central fact is the following.

Lemma 4.58. For any $n$, there is a co-section $q_n : I_n^+ \to J_n$.

Proof. On objects, let $q_n((1, \langle k \rangle)) = (0, \langle k+1 \rangle)$ for $0 \leqslant k < n$. A morphism $(1, \langle k \rangle) \to (1, \langle l \rangle)$ is a length $l+1$ sequence with $k+1$ 1s, and we augment it by another 1 on the right to get a length $l+2$ sequence with $k+2$ 1s, hence a morphism $(0, \langle k+1 \rangle) \to (0, \langle l+1 \rangle)$. A morphism $(0, \langle k \rangle) \to (1, \langle l \rangle)$ is also a length $l+1$ sequence with $k+1$ 1s, but this time we augment it by a 0 on the right to get a length $l+2$ sequence with $k+1$ 1s, hence a morphism $(0, \langle k \rangle) \to (0, \langle l+1 \rangle)$. Finally, we send the new morphism $\mathcal{L}_{(1, \langle l \rangle)}$ to the sequence of $l+1$ 0s followed by one 1. Functoriality is easy to check. And to see that it is a discrete fibration, we observe that any binary sequence of length $l+2$ with a positive number of 1s must be of exactly one of these three forms: a positive number of 1s followed by a 1, a positive number of 1s followed by a 0, or a sequence of 0s followed by a 1.

Evidently $q_{n+1}$ restricts to $q_n$ as we shrink the categories. Thus, we also get a relative isomorphism $\partial \mathcal{L}_{(1, \langle n \rangle)}^+ \to \partial \mathcal{L}_{(0, \langle n+1 \rangle)}$ over $q_n$.

Now note that if we abstract over $b$, the type of $t_n$ matches that of $\gamma^{q_n}$. Thus, we can now prove by simultaneous induction that:

1. $X^{\partial n} \equiv \Gamma^{\Delta_{n-1}}$.

96