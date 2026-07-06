Equality in type theory 9

number $n \in \mathbb{N}$ as a quotient of $\mathbb{Int}$. Elements of $\mathbb{Int}_n$ are integers, but we say that $m_0, m_1 \in \mathbb{Int}_n$ are equal as soon as they differ by some integer multiple of $n$. (Thus $\mathbb{Int}_3$, for example, has three distinct elements: every element is equal to one of 0, 1, or 2.) In syntax, we intend the equality relation for $\mathbb{Int}_n$ to be given by the following type.

$$m_0 \approx m_1 := (p : \mathbb{Int}) \times \mathrm{Id}(\mathrm{Int}, m_1 - m_0, p \cdot n)$$

That is, $m_0$ and $m_1$ are equal whenever there is some $p \in \mathbb{Int}$ equipped with a proof that $m_1 - m_0$ is equal to $p \cdot n$.

In a traditional computation-based type theory, we could have something like the following rule for deducing equalities in $\mathbb{Int}_n$. A *rule* is simply a principle for deducing true judgments; we write the premises above a horizontal line and the conclusion below.

$$\frac{P \in m_0 \approx m_1}{\star \in \mathrm{Id}(\mathrm{Int}_n, m_0, m_1)}$$

That is, if we have some element $P$ of the type $m_0 \approx m_1$, we can conclude that $m_0$ and $m_1$ are equal in $\mathbb{Int}_n$. Because equality has no computational content, the program serving as evidence for this equality is simply a placeholder symbol $\star$.

Using this rule, we can check that the program that takes any element $P \in m_0 \approx m_1$ as input and returns $\star$-written ($\lambda P, \star$)-has the type $(m_0 \approx m_1) \rightarrow \mathrm{Id}(\mathrm{Int}_n, m_0, m_1)$. But what about the other direction? An element of $\mathrm{Id}(\mathrm{Int}_n, m_0, m_1)$ carries no information, so is no little help in constructing an element $P \in m_0 \approx m_1$. In the particular case of $\mathbb{Int}_n$, we can get by with the other information we have on hand: we can compute the quotient $Q := (m_1 - m_0)/n$ and know by the fact that $\mathrm{Id}(\mathrm{Int}_n, m_0, m_1)$ is inhabited that we will have $\langle Q, \star \rangle \in m_0 \approx m_1$. This route is not available in general, however. Consider quotienting $\mathbb{Int} \rightarrow \mathbb{Int}$, the type of functions from integers to integers, by the following relation, which identifies functions that agree on all arguments $m$ above some number $n$.

$$f_0 \bowtie f_1 := (p : \mathbb{Int}) \times ((m : \mathbb{Int}) \rightarrow (m > n) \rightarrow \mathrm{Id}(\mathrm{Int}, f_0 m, f_1 m))$$

Just knowing that there is *some* number $p$ with this property will not suffice to reconstruct such a number; writing $T$ for the quotient type, we can construct no program of type $\mathrm{Id}(T, f_0, f_1) \rightarrow (f_0 \bowtie f_1)$. There is thus a general mismatch between relations and the induced equalities in their quotient types, a failure of *effectivity of quotients*. Lack of effectivity is a serious problem: it prevents us from relating properties of $T$ with properties of $\mathbb{Int} \rightarrow \mathbb{Int}$.

In short, quotients are constructions where data and equality collide: we frequently want to quotient by a relation whose proofs carry data (like the $p \in \mathbb{Int}$ in these examples), what we will call a *contentful relation*. We simply cannot do so in a satisfactory way when we forbid proofs of equality from carrying data. (For a more formal analysis of this incompatibility, see [Mai98].)