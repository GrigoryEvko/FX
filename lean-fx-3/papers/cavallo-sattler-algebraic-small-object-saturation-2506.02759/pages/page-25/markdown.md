### 3.1.2 Double categories

Bourke and Garner [BG16a; BG16b; Bou23] observed that the category of (co)monad (co)algebras associated to an AWFS can be seen as the category of vertical morphisms of a double category: identities have canonical (co)algebra structures, and (co)algebra structures on a pair of composable maps can themselves be composed. We recall first some double-categorical terminology, then the double categories of copointed endofunctor and comonad coalgebras induced by an AWFS.

**Definition 3.1.5** (Grandis and Paré [GP99, §7.1]). A *pseudo double category* $\mathbb{A}$ is a “pseudo category object in the 2-category of categories”. By this, one means that $\mathbb{A}$ consists of

- (a) categories $\mathbb{A}_0$ and $\mathbb{A}_1$;
- (b) functors

$$\mathbb{A}_0 \xrightarrow[\text{cod}_\downarrow]{\text{dom}_\downarrow} \mathbb{A}_1 \xleftarrow{\star} \mathbb{A}_1 \times_{\mathbb{A}_0} \mathbb{A}_1,$$

making the diagrams

$$\begin{array}{ccc} & \mathbb{A}_0 & \\ \mathbb{A}_0 & \uparrow \text{dom}_\downarrow & \\ \mathbb{A}_0 \xrightarrow{\text{id}} & \mathbb{A}_1 & \\ & \downarrow \text{cod}_\downarrow & \\ & \mathbb{A}_0 & \end{array} \qquad \begin{array}{ccc} & \mathbb{A}_1 \xrightarrow{\text{dom}_\downarrow} \mathbb{A}_0 \\ \pi_1 \uparrow & & \uparrow \text{dom}_\downarrow \\ \mathbb{A}_1 \times_{\mathbb{A}_0} \mathbb{A}_1 \xrightarrow{\star} \mathbb{A}_1 \\ \pi_0 \downarrow & & \downarrow \text{cod}_\downarrow \\ \mathbb{A}_1 \xrightarrow{\text{cod}_\downarrow} \mathbb{A}_0 & & \end{array}$$

commute strictly;

- (c) natural isomorphisms $\alpha, \lambda, \rho$ witnessing the associativity and unitality of the composition $\star$ and identity **id** and satisfying various coherence laws.

We refer to Grandis and Paré [GP99, §7.1] for a complete definition. A *double category* is a pseudo double category in which the associator and unitors for $\star$ and **id** are strict equalities, in which case the coherence laws are automatically satisfied.

We call objects of $\mathbb{A}_0$ *objects of* $\mathbb{A}$, morphisms of $\mathbb{A}_0$ *horizontal morphisms*, objects of $\mathbb{A}_1$ *vertical morphisms*, and morphisms in $\mathbb{A}_1$ *squares*. We denote horizontal morphisms of a double category by ordinary arrows, as in $f: A \rightarrow B$. We write vertical morphisms of a double category in boldface, *e.g.*, $\boldsymbol{f}$, and indicate that $\text{dom}_\downarrow \boldsymbol{f} = A$ and $\text{cod}_\downarrow \boldsymbol{f} = B$ by writing a dotted arrow, as in $\boldsymbol{f}: A \rightarrow B$. We draw squares $\beta: \boldsymbol{f} \rightarrow \boldsymbol{g}$ as squares, as in

$$\begin{array}{ccc} A & \xrightarrow{h} & B \\ \boldsymbol{f} \downarrow & \beta & \downarrow \boldsymbol{g} \\ C & \xrightarrow{k} & D \end{array}$$

where $h = \text{dom}_\downarrow \beta$ and $k = \text{cod}_\downarrow \beta$, and draw vertical and horizontal composition of squares as vertical and horizontal juxtaposition respectively.$^2$

**Notation 3.1.6.** Given a pseudo double category $\mathbb{A} = (\mathbb{A}_0, \mathbb{A}_1, \dots)$, write $\mathbb{A}^\downarrow$ for its category of vertical morphisms $\mathbb{A}_1$.

$^2$We never draw any diagram with more than two vertical “layers”, so there is no chance of misinterpreting vertical juxtaposition as strictly associative.

25