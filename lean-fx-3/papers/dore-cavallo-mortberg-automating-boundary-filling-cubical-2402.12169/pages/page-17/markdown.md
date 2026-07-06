Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:17

Now we define an inverse mapping, sending 1-cells over $\lceil X|R \rceil$ to elements of the presented group and 2-cells to equations between them. Again, these definitions make sense for any of the contortion theories we consider; we rely only of the fact that any dimension term in the unit context () is equal to either 0 or 1. For each definition, we go by structural induction on the Kan cell term formers; as mentioned in Remark 2.11, we treat the syntax here as coming with explicit substitutions, which simplifies the reasoning.

**Definition 3.18.** Fix a convenient presentation $\langle X|R \rangle$ of a group $G$. For each Kan cell $\lceil X|R \rceil \mid \Psi \vdash t$ cell, we define a family of elements $[t]_\psi \in G$ for each substitution $\psi: (i) \to \Psi$. We go by structural induction on $t$ as follows.

- Define $[t[\psi']]_\psi := [t]_{\psi'\psi}$.
- Define $[\star]_\psi := 1$.
- Define $[\hat{a}(\psi')]_\psi := g_a(\psi'\psi(0))^{-1}g_a(\psi'\psi(1))$, where $g_a(e)$ is defined for $e \in \{0, 1\}$ by $g_a(e) = a^e$, i.e.,

$$\begin{aligned} g_a(0) &:= 1 \\ g_a(1) &:= a \end{aligned}$$

Note that this assignment respects cell equality: we have $[\hat{a}(0)]_\psi = [\hat{a}(1)]_\psi = [\star]_\psi$.

- Define $[s_{a,b,c}(\psi')]_\psi := g_{a,c}(\psi'\psi(0))^{-1}g_{a,c}(\psi'\psi(1))$, where $g_{a,c}(e, e')$ is defined for $e, e' \in \{0, 1\}$ by

$$\begin{aligned} g_{a,c}(00) &:= 1 \\ g_{a,c}(01) &:= 1 \end{aligned} \quad \begin{aligned} g_{a,c}(10) &:= a \\ g_{a,c}(11) &:= c \end{aligned}$$

Again, we can check that $[s_{a,b,c}(r, 0)]_\psi = [\hat{a}(r)]_\psi$, $[s_{a,b,c}(r, 1)]_\psi = [\hat{c}(r)]_\psi$, $[s_{a,b,c}(0, r)]_\psi = [\star]_\psi$, and $[s_{a,b,c}(1, r)]_\psi = [\hat{b}(r)]_\psi$ as required by the equational theory.

- We define $[\text{fill}^{e \to r} \ell. [\phi] u]_\psi$ as follows. First, for $\psi': (i) \to (\Psi, \ell)$, say that $\phi$ is *satisfied at* $\psi'$ if we have some $(s = e' \mapsto t) \in \phi$ with $s[\psi'] = e'$; in this case, we write $[\phi]_{\psi'}$ to mean $[t]_{\psi' [s=e']}$. Note that if there are multiple applicable clauses in $\phi$, this value is independent of the choice. In general, define

$$[\phi]_{\psi'}^* := \begin{cases} [\phi]_{\psi'}, & \text{if } \phi \text{ is satisfied at } \psi' \\ 1, & \text{otherwise} \end{cases}$$

We now divide into two cases.

- If $\phi$ is satisfied at $\psi$, then set $[\text{fill}^{e \to r} \ell. [\phi] u]_\psi := [\phi]_{(\psi, r[\psi])}$.
- Otherwise, set

$$[\text{fill}^{e \to r} \ell. [\phi] u]_\psi := ([\phi]_{(\psi(0), i)}^*)^{e-r[\psi(0)]} [u]_\psi ([\phi]_{(\psi(1), i)}^*)^{r[\psi(1)]-e}$$

Here, for $e' \in \{0, 1\}$, $\psi[i = e'] : () \to \Psi[i = e']$ is the induced substitution between constrained contexts and thus we have $(\psi[i = e'], i) : (i) \to (\Psi[i = e'], \ell)$.

Once more, we check that the assignment respects cell equality: we have $[\text{fill}^{e \to e} \ell. [\phi] u]_\psi = [u]_\psi$ and $[\text{fill}^{e \to r} \ell. [\phi] u]_\psi = [t]_{(\psi, r)} = [t[i \mapsto r]]_\psi$ whenever $(e' = e' \mapsto t) \in \phi$.

**Lemma 3.19.** *Fix a convenient presentation $\langle X|R \rangle$ of a group $G$. For each word $w$ on $X$, we have $[\lceil w \rceil(i)]_{(i)} = w$ in $G$.*

*Proof.* By calculation using the definition of $\lceil w \rceil(i)$.

**Lemma 3.20.** *Fix a convenient presentation $\langle X|R \rangle$ of a group $G$. For each Kan cell $\lceil X|R \rceil \mid \Psi \vdash t$ cell, if $\psi: (i) \to \Psi$ is a constant substitution (i.e., either (0) or (1)), then $[t]_\psi = 1$.*