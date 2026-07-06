190 Programming with parametricity

**inductive** Bool **where**

| tt ∈ Bool
| ff ∈ Bool

A *Church boolean* is a function that takes a type and two elements of that type and returns a third element of that type. There are two canonical such booleans: the function that always returns the first element, and the function that always returns the second.

**Definition 10.1.1.** We define the type of Church booleans, $\mathbb{B}$ type, as follows.

$$\mathbb{B} := (A : \cup) \rightarrow A \rightarrow A \rightarrow A$$

We define terms $\mathfrak{t}, \mathfrak{f} \in \mathbb{B}$ by $\mathfrak{t} := \lambda A. \lambda t. \lambda f. t$ and $\mathfrak{f} := \lambda A. \lambda t. \lambda f. f$.

The Church booleans enjoy a recursion principle: given $c : \mathbb{B}$, $a_0 : A$, and $a_1 : A$, we have $c A a_0 a_1 \in A$, and moreover we have reduction equations $\mathfrak{t} A a_0 a_1 = a_0 \in A$ and $\mathfrak{f} A a_0 a_1 = a_1 \in A$. However, they do not necessarily satisfy the *induction* (that is, dependent elimination) principle for the booleans—unless we assume parametricity [Wad90; Has94].

In the presence of parametricity and impredicative quantification, one can show that the *only* elements of $\mathbb{B}$ are $\mathfrak{t}$ and $\mathfrak{f}$, thus obtaining a type of booleans without relying on a primitive inductive type mechanism. Because our universes are predicative, this is not quite possible, but we *can* show that $\mathbb{B}$ is isomorphic to the primitive Bool when the latter type already exists.

**Theorem 10.1.2.** $\mathbb{B} \simeq$ Bool.

*Proof.* We can easily define functions in either direction. Starting with a Church boolean $c : \mathbb{B}$, we apply it to Bool, tt, and ff to obtain a primitive boolean; starting from a primitive boolean $b :$ Bool, we behave either as $\mathfrak{t}$ or as $\mathfrak{f}$ by case analysis on $b$.

$$\begin{aligned} H &:= \lambda c. c \text{ Bool tt ff} \in \mathbb{B} \rightarrow \text{Bool} \\ K &:= \lambda b. \lambda A. \lambda t. \lambda f. \text{elim}_{\text{Bool}} (\dots A; b; t, f) \in \text{Bool} \rightarrow \mathbb{B} \end{aligned}$$

One inverse condition is easy to check. Given $b$:Bool, we construct a path $H(Kb) \rightsquigarrow b$ by case analysis (i.e., by $\text{elim}_{\text{Bool}}$). In the case that $b$ is tt, we have $H(K\text{tt}) = H\mathfrak{t} \in \text{Bool}$ and then $H\mathfrak{t} = (\lambda A. \lambda t. \lambda f. t) \text{Bool tt ff} = \text{tt} \in \text{Bool}$. By the same token, we have $H(K\text{ff}) = \text{ff} \in \text{Bool}$.

It is the second condition that requires the use of parametricity. Let $c : \mathbb{B}$ be given. By function extensionality (Lemma 3.2.5), it suffices to show that, for all $A : \cup, t : A$, and $f : A$, we have a path $(K(Hc))A\,t\,f \rightsquigarrow cA\,t\,f$. Expanding the definition of $H$ and simplifying,