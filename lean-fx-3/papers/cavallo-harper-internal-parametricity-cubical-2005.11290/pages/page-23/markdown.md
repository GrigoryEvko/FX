Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:23

This specification generates the following elimination principle and computation rule, which essentially says that maps out of line correspond to terms in a context extended with an interval variable.

$$\frac{\Gamma, a : \text{line} \gg C \text{ type} \quad \Gamma \gg M \in \text{line} \quad \Gamma, x : \mathbb{I} \gg Q_{\text{in}} \in C[\text{in}(x)/a]}{\Gamma \gg \text{interval-elim}_{a.C}(M, x.Q_{\text{in}}) \in C[M/a]}$$

$$\frac{\Gamma, a : \text{line} \gg C \text{ type} \quad \Gamma \gg r \in \mathbb{I} \quad \Gamma, x : \mathbb{I} \gg Q_{\text{in}} \in C[\text{in}(x)/a]}{\Gamma \gg \text{interval-elim}_{a.C}(\text{in}(r), x.Q_{\text{in}}) = Q_{\text{in}}[r/x] \in C[\text{in}(r)/a]}$$

The issue is in the computation rule, which applies the interval substitution $-[r/x]$ to $Q_{\text{in}}$. If our interval is affine, then this substitution will be nonsensical if $Q_{\text{in}}$ already mentions $r$. Moreover, it is not clear how to restrict the premises of interval-elim to ensure the substitution is sensible without ending up with an insufficiently powerful principle. On a more conceptual level, the line type is suspicious in an affine system in that structural maps out of line correspond to affine maps out of the interval.

The problem of higher inductive types is one reason why research in cubical type theory and models has shifted from substructural to structural interval variables. There is also the fact that structural variables are simply easier to work with. Still, the BCH model does have some intriguing advantages; for one, univalence can be implemented in Gel-like rather V-like fashion, and the former admits simpler implementations of coercion and composition.

### 3. APPLYING INTERNAL PARAMETRICITY

Now that we have laid out what we need of parametric cubical type theory, we can get started proving theorems. We will begin with a classic application of parametricity: relating inductive types to their Church encodings, in this case booleans.

3.1. Booleans. The Church booleans are the polymorphic binary operators, the elements of the type $\mathbb{B} := (A:\mathcal{U}) \to A \to A \to A$. Clearly this type has at least two elements, $\lambda A.\lambda t.\lambda_{\dots}t$ and $\lambda A.\lambda_{\dots}\lambda f.f$. It is a classical consequence of parametricity that these are the only two elements of $\mathbb{B}$. Using internal parametricity, we can prove that $\mathbb{B}$ is indeed isomorphic to the standard type of booleans (bool).

Theorem 3.1. bool $\simeq \mathbb{B}$.

Proof. It is easy to define functions $F \in \text{bool} \to \mathbb{B}$ and $G \in \mathbb{B} \to \text{bool}$ in either direction.

$$F := \lambda b.\lambda A.\lambda t.\lambda f.\text{if}_{\_A}(b; t, f) \quad G := \lambda k.k(\text{bool})(\text{tt})(\text{ff})$$

Moreover, it is easy to check by case-analysis that $G(Fb)$ is path-equal to $b$ for any $b : \text{bool}$.

We use parametricity to prove the other inverse condition. Let some $k : \mathbb{B}$ along with $A : \mathcal{U}, t : A, f : A$ be given. We intend to show that $F(Gk)Atf$ is path-equal to $kAtf$. We define a relation $R \in \text{bool} \times A \to \mathcal{U}$ as follows.

$$R\langle b, a \rangle := \text{Path}_A(FbAtf, a)$$

That is, $R$ is the graph of $\lambda b.FbAtf$. Abstracting a bridge interval variable $\boldsymbol{x}$, we can apply $k$ at the Gel-type corresponding to $R$.

$$k(\text{Gel}_\boldsymbol{x}(\text{bool}, A, R)) \in \text{Gel}_\boldsymbol{x}(\text{bool}, A, R) \to \text{Gel}_\boldsymbol{x}(\text{bool}, A, R) \to \text{Gel}_\boldsymbol{x}(\text{bool}, A, R)$$