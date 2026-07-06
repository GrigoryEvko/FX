5:16

E. CAVALLO AND R. HARPER

Vol. 17:4

The eliminator for $\mathbb{Z}/2\mathbb{Z}$ naturally takes clauses to handle the in and mod cases. The mod case is required to cohere with the in case on its boundary, which ensures that every function out of $\mathbb{Z}/2\mathbb{Z}$ takes $\text{in}(n)$ and $\text{in}(n+2)$ to path-equal results.

$$\begin{array}{l} \Gamma, a: \mathbb{Z}/2\mathbb{Z} \gg C \text{ type} \quad \Gamma \gg M \in \mathbb{Z}/2\mathbb{Z} \\ \Gamma, n: \mathbb{Z} \gg Q_{\text{in}} \in C[\text{in}(n)/a] \quad \Gamma, n: \mathbb{Z}, x: \mathbb{I} \gg Q_{\text{mod}} \in C[\text{mod}(n, x)/a] \\ \Gamma, n: \mathbb{Z} \gg Q_{\text{mod}}[0/x] = Q_{\text{in}} \in C[\text{in}(n)/a] \\ \Gamma, n: \mathbb{Z} \gg Q_{\text{mod}}[1/x] = Q_{\text{in}}[n+2/n] \in C[\text{in}(n+2)/a] \\ \hline \Gamma \gg \text{mod-elim}_{a.C}(M, n.Q_{\text{in}}, n.x.Q_{\text{mod}}) \in C[M/a] \end{array}$$

When applied to a constructor, the eliminator steps accordingly as shown below.

$$\text{mod-elim}_{a.C}(\text{in}(N), n.Q_{\text{in}}, n.x.Q_{\text{mod}}) = Q_{\text{in}}[N/n] \in C[\text{in}(N)/a]$$

$$\text{mod-elim}_{a.C}(\text{mod}(N, r), n.Q_{\text{in}}, n.x.Q_{\text{mod}}) = Q_{\text{mod}}[N/n][r/x] \in C[\text{mod}(N, r)/a]$$

## 2. PARAMETRIC TYPE THEORY

We now proceed to add parametricity primitives to our cubical type theory. We follow the blueprint of Bernardy, Coquand, and Moulin (BCM) [BCM15], which is a substantial simplification of Bernardy and Moulin's original parametric theory [BM12]. The BCM parametric type theory has the same basic shape as cubical type theory: relatedness is represented by maps out of an interval object I. We henceforth refer to $\mathbb{I}$ as the path interval and I as the bridge interval; we call maps out of I bridges, following [NVD17]. (As a general rule, we use boldface to distinguish bridge constructs from their path equivalents.) The connection between internal parametricity and cubical type theory has never been a secret; Bernardy and Moulin already remark on the similarity in [BM12], and later iterations of their work resemble cubical type theory even more strongly.

We go a bit further and compare the two in detail over the course of this section. First, there is the obvious difference: parametric type theory has no analogues of coercion and composition. More subtle is the difference between the two intervals $\mathbb{I}$ and I: the path interval behaves structurally, but the bridge interval is affine. This has two essential effects on the theory. First, it enables a "function extensionality" principle analogous to Lemma 1.2 that does not rely on coercion. Second, it means that we can avoid the V-shape of V-types, instead supporting a type former (Gel) that directly converts relations to bridges.

On a more mundane level, we present the parametricity elements using a notation more similar to that of cubical type theory. For a translation to Bernardy et al.'s (substantially different) notation, see Figure 10 on page 51.

2.1. The bridge interval. Recall our intuition for a term $x: \mathbb{I} \gg M \in A$: the path $x.A$ stands for an isomorphism $A[0/x] \simeq A[1/x]$ via univalence, and $x.M$ is a proof that $M[0/x]$ corresponds to $M[1/x]$ across this isomorphism. Likewise, a bridge of types $\boldsymbol{x}: \mathbf{I} \gg A$ type stands for a binary relation on $A[\mathbf{0}/\boldsymbol{x}]$ and $A[\mathbf{1}/\boldsymbol{x}]$, and a term $\boldsymbol{x}: \mathbf{I} \gg M \in A$ is a proof that $M[\mathbf{0}/\boldsymbol{x}]$ and $M[\mathbf{1}/\boldsymbol{x}]$ stand in this relation.

We start with a judgment $\Gamma \gg \boldsymbol{r} \in \mathbf{I}$. Like the path interval, it is populated by two endpoint $\mathbf{0}$ and $\mathbf{1}$, and we can suppose bridge interval variables.

$$\overline{\Gamma \gg \mathbf{0} \in \mathbf{I}} \qquad \overline{\Gamma \gg \mathbf{1} \in \mathbf{I}} \qquad \overline{\Gamma \text{ ctx}} \qquad \overline{\Gamma, \boldsymbol{x}: \mathbf{I} \text{ ctx}} \qquad \overline{\Gamma, \boldsymbol{x}: \mathbf{I} \gg \boldsymbol{x} \in \mathbf{I}}$$