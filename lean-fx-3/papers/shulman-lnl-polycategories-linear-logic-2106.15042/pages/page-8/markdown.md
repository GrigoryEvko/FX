1:8

M. SHULMAN

Vol. 19:2

possible types. For the five possible combination of types for $\psi$ and $R$, this specializes to the following.

**Definition 2.8.** Let $X$ be a nonlinear object and $A$ a linear object.

- A nonlinear morphism $\psi \in \mathcal{P}(\Theta; X)$ is **universal in** $X$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta', X; Y) \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta; Y)$$

$$\mathcal{P}(\Theta', X \mid \Gamma; \Delta) \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta \mid \Gamma; \Delta).$$

- A nonlinear morphism $\psi \in \mathcal{P}(\Theta, X; Y)$ is **universal in** $X$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta'; X) \xrightarrow{\sim} \mathcal{P}(\Theta, \Theta'; Y).$$

- A linear morphism $\psi \in \mathcal{P}(\Theta, X \mid \Gamma; \Delta)$ is **universal in** $X$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta'; X) \xrightarrow{\sim} \mathcal{P}(\Theta, \Theta' \mid \Gamma; \Delta).$$

- A linear morphism $\psi \in \mathcal{P}(\Theta \mid \Gamma; \Delta, A)$ is **universal in** $A$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta' \mid \Gamma', A; \Delta') \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta \mid \Gamma', \Gamma; \Delta', \Delta).$$

- A linear morphism $\psi \in \mathcal{P}(\Theta \mid \Gamma, A; \Delta)$ is **universal in** $A$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta' \mid \Gamma'; \Delta', A) \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta \mid \Gamma', \Gamma; \Delta', \Delta).$$

A functor is said to **preserve** a certain kind of universal morphism if it takes any such morphism to a similarly universal morphism.

Universal morphisms are unique up to unique isomorphism:

**Proposition 2.9.** If $\psi \in \mathcal{P}(\Theta \mid \Gamma; \Delta, A)$ and $\psi' \in \mathcal{P}(\Theta \mid \Gamma; \Delta, A')$ are universal in $A$ and $A'$ respectively, then there is a unique isomorphism $\phi: A \cong A'$ such that $\phi \circ_A \psi = \psi'$; and similarly for other kinds of universal morphism.

*Proof.* As usual, $\phi$ is determined by applying the universal property of $\psi$ to $\psi'$, and conversely for its inverse. $\square$

We now explore the most important cases of universality, starting with versions of the polycategorical representability conditions from [CS97, BZ20]. For clarity and conciseness, we indicate the object in which a universal morphism is universal by underlining it, e.g. $\psi \in \mathcal{P}(\Theta \mid \Gamma, \underline{A}; \Delta)$.

**Definition 2.10.** Let $A, B$ be linear objects in an LNL polycategory $\mathcal{P}$.

- A **tensor product** of $A, B$ is a universal morphism $\psi \in \mathcal{P}(\mid A, B; \underline{A \otimes B})$.

- A **cotensor product** of $A, B$ is a universal morphism $\psi \in \mathcal{P}(\mid \underline{A \otimes B}; A, B)$.

- A **unit** $\mathbb{1}$ is a universal morphism $\psi \in \mathcal{P}(\mid; \mathbb{1})$.

- A **counit** $\perp$ is a universal morphism $\psi \in \mathcal{P}(\mid \perp;)$.

- A **dual** of $A$ is a universal morphism $\psi \in \mathcal{P}(\mid A, \underline{A^*};)$.

We say that $\mathcal{P}$ "has $\otimes$" if any $A, B$ have a tensor product, and so on.