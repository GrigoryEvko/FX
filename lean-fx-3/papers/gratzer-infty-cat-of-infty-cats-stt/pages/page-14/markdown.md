Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

## A Formal syntax of MTT

We provide a succinct description of the formal syntax of MTT in this section. Since most connectives of type theory ($\Sigma$, $\Pi$, etc.) are not impacted by modalities, we focus only on those rules which must be changed. These are (1) some aspects of the substitution calculus and (2) the rules for modal types are modal $\Pi$ types. We assume a mode theory $\mathcal{M}$ which has 1 object and which is enriched in posets, as is in this paper.

First, we extend contexts with the following new forms:

$$\frac{\vdash \Gamma \text{ cx} \quad \mu : m \to m \in \mathcal{M}}{\vdash \Gamma.\{\mu\} \text{ cx}} \quad \frac{\vdash \Gamma \text{ cx} \quad \Gamma.\{\mu\} \vdash A \text{ type}}{\vdash \Gamma.(\mu \mid A) \text{ cx}}$$

Our previous notation with formal divisions was really syntactic sugar for these operations. In particular, $x :_{\mu/\nu} A, y :_{\text{id}/\nu} B, z : C$ becomes $1.(\mu \mid A).(\text{id} \mid B).\{\nu\}.C$. Notably, while $-/\mu$ was mere notation for the paper, it is actually the primitive operation in MTT. Any context built using either notation using the rules of the system is translatable.

We then add several new to the substitution calculus to account for this. This includes a new form of the variable rule (built using de Bruijn indices) to account for $\Gamma.\{\mu\}$.

$$\frac{\Delta \vdash \gamma : \Gamma}{\Delta.\{\mu\} \vdash \gamma.\{\mu\} : \Gamma.\{\mu\}} \quad \frac{\vdash \Gamma \text{ cx} \quad \mu \le \nu}{\Gamma.\{\nu\} \vdash \Gamma.\{\mu \le \nu\} : \Gamma.\{\mu\}}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type}}{\Gamma.(\mu \mid A) \vdash \uparrow : \Gamma}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Delta \vdash \gamma : \Gamma \quad \Delta \vdash M : A[\gamma.\{\mu\}]}{\Delta \vdash \gamma.M : \Gamma.(\mu \mid A)}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type}}{\Gamma.(\mu \mid A).\{\mu\} \vdash \text{var} : A[\uparrow.\{\mu\}]}$$

We have normal substitution rules around substitution extensions and weakenings. These are essentially standard, and so we omit them. We further require a handful of equations which ensure that $\Gamma \mapsto \Gamma.\{\mu\}$, $\gamma \mapsto \gamma.\{\mu\}$, and $-\{- \le -\}$ organize into a 2-functor from $\mathcal{M}^{\text{coop}}$ to Cat sending $m$ to the category of contexts. We refer the reader to Gratzer et al. [9] for a full account.

The additional types and terms are then given as follows:

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type}}{\Gamma \vdash \langle \mu \mid A \rangle \text{ type}} \quad \frac{\Gamma.\{\mu\} \vdash M : A}{\Gamma \vdash \text{mod}_\mu(M) : \langle \mu \mid A \rangle}$$

$$\frac{\Gamma.\{\nu \circ \mu\} \vdash A \text{ type} \quad \Gamma.(\nu \mid \langle \mu \mid A \rangle) \vdash B \text{ type}}{\Gamma.(\nu \circ \mu \mid A) \vdash b : B[\uparrow.\text{mod}_\mu(\text{var})] \quad \Gamma.\{\nu\} \vdash a : \langle \mu \mid A \rangle} \quad \frac{\Gamma.\{\nu\} \vdash a : \langle \mu \mid A \rangle}{\Gamma \vdash \text{let}_\nu \text{ mod}_\mu(-) \leftarrow a \text{ in } b : B[\text{id.}a]}$$

$$\frac{\Gamma.\{\nu \circ \mu\} \vdash A \text{ type} \quad \Gamma.(\nu \mid \langle \mu \mid A \rangle) \vdash B \text{ type}}{\Gamma.(\nu \circ \mu \mid A) \vdash b : B[\uparrow.\text{mod}_\mu(\text{var})] \quad \Gamma.\{\nu \circ \mu\} \vdash a : A} \quad \frac{\Gamma.\{\nu \circ \mu\} \vdash a : A}{\Gamma \vdash \text{let}_\nu \text{ mod}_\mu(-) \leftarrow \text{mod}_\mu(a) \text{ in } b = b[\text{id.}a] : B[\text{id.} \text{mod}_\mu(a)]}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Gamma.(\mu \mid A) \vdash B \text{ type}}{\Gamma \vdash (\mu \mid A) \to B \text{ type}}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Gamma.(\mu \mid A) \vdash b : B}{\Gamma \vdash \lambda M : (\mu \mid A) \to B}$$

$$\frac{\Gamma \vdash f : (\mu \mid A) \to B \quad \Gamma.\{\mu\} \vdash a : A}{\Gamma \vdash f(a) : B[\text{id.}a]}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Gamma.(\mu \mid A) \vdash b : B \quad \Gamma.\{\mu\} \vdash a : A}{\Gamma \vdash (\lambda b)(a) = b[\text{id.}a] : B[\text{id.}a]}$$

$$\frac{\Gamma \vdash f : (\mu \mid A) \to B}{\Gamma \vdash f = \lambda f[\uparrow](\text{var}) : (\mu \mid A) \to B}$$

## B Full list of axioms

**Axiom 1.** *The canonical map $A = \mathcal{U}_i, B \to A \simeq B$ sending refl to id is an equivalence.*

**Axiom 2.** *There is a set $\mathbb{I}$ equipped with the structure of a bounded distributive lattice $(0, 1, \wedge, \vee)$ such that $0 \ne 1$.*

**Axiom 3.** *If $A :_\mu \mathcal{U}$ and $a, b :_\mu A$, then the following canonical map sending refl to $\text{mod}_\mu(\text{refl})$ is an equivalence:*

$$\text{mod}_\mu(a) = \text{mod}_\mu(b) \to \langle \mu \mid a = b \rangle$$

**Axiom 4.** $0, 1 : \mathbb{I}$ induce an equivalence $\langle b \mid \text{Bool} \rangle \simeq \langle b \mid \mathbb{I} \rangle$

**Axiom 5.** *If $A :_b \mathcal{U}$, then is $\text{Equiv}(\langle b \mid A \rangle \to A)$ if is $\text{Equiv}(A \to A^\mathbb{I})$*

**Axiom 6.** *If $A, B :_b \mathcal{U}$ and $f :_b A \to B$, then $f$ is an equivalence if $\prod_{n:\text{Nat}} \text{isEquiv}((f_*)^\dagger : \langle b \mid \mathbb{I}^n \to A \rangle \to \langle b \mid \mathbb{I}^n \to B \rangle)$*

**Axiom 7.** *For every $A :_b \mathcal{U}$, the following holds:*

$$\prod_{n:\text{Nat}} \text{isEquiv}((\eta_*)^\dagger : \langle b \mid \Delta^n \to A \rangle \to \langle b \mid \Delta^n \to \square A \rangle)$$

**Axiom 8.** *For every $A :_b \mathcal{U}$, the following holds:*

$$\sum_{A :_b \mathcal{U}, \varepsilon :_b (A :_b \mathbb{I}) \to A} \prod_{B :_b \mathcal{U}} \text{isEquiv}(\langle b \mid B \to A :_b \rangle \to \langle b \mid B^\mathbb{I} \to A \rangle)$$

**Axiom 9.** *There is an equivalence $\langle \text{op} \mid \mathbb{I} \rangle \to \mathbb{I}$ which exchanges 0 for 1 and $\wedge$ for $\vee$.*

Define a *finitely-presented $\mathbb{I}$-algebra* to be a map of bounded distributive lattice $\mathbb{I} \to X$ where $X$ is equivalent to a bounded distributive lattice of the form $\mathbb{I}[x_1 \dots x_n]/(f_1 = g_1 \dots f_m = g_m)$ and $\mathbb{I} \to X$ is the canonical map. That is, $X$ is freely generated over $\mathbb{I}$ by the operations of a bounded distributive lattice, the indeterminates $x_1 \dots x_n$, and subject to the equations $f_i = g_i$. With this notation to hand, we state a duality axiom due originally to Kock [15] and proposed in this form by Blechschmidt [4].

**Axiom 10.** *If $\mathbb{I} \to X$ is a finitely presented $\mathbb{I}$-algebra, the following evaluation map is an equivalence of underlying sets:*

$$\lambda x, f, f(x) : X \simeq \mathbb{I}^{\text{hom}_U(X, \mathbb{I})}$$

## C Selected details from omitted proofs

If a proof of a proposition given in the main body is presented here in the appendix, we have ensured that the numbering in the appendix matches that of the main body. Propositions numbered "C.X" are therefore only intermediate results used in the process of proving those main results.