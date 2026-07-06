28

Martin-Löf's type theory

**Theorem 2.1.20 (Knaster-Tarski for power sets).** Let $S$ be a set and let $F$ be an operator on subsets of $S$. Suppose that $F$ is monotone: if $T \subseteq T' \subseteq S$, then $F(T) \subseteq F(T')$. Then there is a subset $\mu F \subseteq S$ satisfying the following properties.

- $\mu F$ is a *fixed-point* of $F$: we have $F(\mu F) = \mu F$.
- $\mu F$ is the *least pre-fixed-point* of $F$: if any subset $T \subseteq S$ satisfies $F(T) \subseteq T$, then $\mu F \subseteq T$.

In particular, $\mu F$ is also the *least fixed-point* of $F$.

We construct value type systems by applying this theorem to the set $Val \times Val \times PER(Val)$, the subsets of which are the candidate value type systems. We also apply the theorem with $Val \times Val$ in order to construct the relations interpreting individual types with recursive structure, such as the natural numbers and inductive types more generally. For these purposes, it is necessary that we obtain not only relations but PERs; in the case of a candidate type system, we also need to check the uniqueness condition. To do so, we introduce the following definitions.

**Definition 2.1.21.** Let $R$ be a binary relation. We define relations $Sym^+(R)$ and $Trans^+(R)$ as follows.

- $M \approx M' \in Sym^+(R)$ holds when $M \approx M' \in R$ and $M' \approx M \in R$.
- $M \approx M' \in Trans^+(R)$ when $M \approx M' \in R$ and for any term $N$, we have:

- if $N \approx M \in R$, then $N \approx M' \in R$
- if $M' \approx N \in R$, then $M \approx N' \in R$.

**Proposition 2.1.22.** Given any binary relation $R$, we have $Sym^+(\Downarrow R) = \Downarrow Sym^+(R)$ and $Trans^+(\Downarrow R) = \Downarrow Trans^+(R)$.

The following lemma, a trivial consequence of the universal property of the least pre-fixed-point, provides a convenient set of conditions we can check to verify PER-hood.

**Lemma 2.1.23.** Let $F$ be a monotone operator on binary relations. If $F(Sym^+(\mu F)) \subseteq Sym^+(\mu F)$, then $\mu F$ is symmetric; if $F(Trans^+(\mu F)) \subseteq Trans^+(\mu F)$, then $\mu F$ is transitive. In particular, if both hold, then $\mu F$ is a PER.

*Proof.* The hypotheses say exactly that $Sym^+(\mu F)$ and $Trans^+(\mu F)$ are pre-fixed-points of $F$, thus that $\mu F \subseteq Sym^+(\mu F)$ and $\mu F \subseteq Trans^+(\mu F)$. By inspection of the definitions of $Sym^+(\mu R)$ and $Trans^+(\mu F)$, these two inclusions give that $\mu F$ is symmetric and transitive respectively. $\square$