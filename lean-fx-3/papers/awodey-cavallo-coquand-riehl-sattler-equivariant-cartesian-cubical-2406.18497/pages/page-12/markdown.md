recent insights into the triangulation functor enabled us to considerably simplify the proofs of the results in §6.

The first and fourth author were supported by the US Air Force Office of Scientific Research under award number FA9550-21-1-0009 as well as, for the first author, award number FA9550-20-1-0305. The second author was supported by the US Air Force Office of Scientific Research under award number FA9550-19-1-0216 and by the Knut and Alice Wallenberg Foundation (KAW) under grant numbers 2020.0266 and 2019.0116. The third author was supported by the ForCUTT project, ERC advanced grant number 101053291. The fourth author is also supported by US National Science Foundation via the grants DMS-2204304 and DMS-2507077 and by the President's Frontier Award at Johns Hopkins, which supported visits to the other authors. The fifth author was supported by the Swedish Research Council under grant number 2019-03765 and the US Air Force Office of Scientific Research under award number FA9550-24-1-0302.

## 2. NOTIONS OF FIBRED STRUCTURE AND UNIVERSES

A (model-categorical) model of HoTT comes with two classes of “right” maps: the *fibrations*, which model type families, and the *trivial fibrations*, which model contractible type families. A key feature of both classes of maps is their stability under pullbacks along arbitrary maps, which models substitution of terms for variables in type theory.

In this section, we consider such “notions of fibred structure” abstractly, proving general results that will apply to both the fibrations and the trivial fibrations in the model categories we construct. In §2.1, we recall the precise, technical meaning of the phrase “notion of fibred structure” and explore what it means when such fibred structure is *locally representable*. In §2.2, we specialize to elementary toposes and show that suitably structured maps that lift against the monomorphisms define a locally representable notion of fibred structure. In §2.3, introduce our notion of universe and, in the case of presheaf toposes, construct universes for locally representable notions of fibred structure from the Hofmann–Streicher classifiers.

2.1. **Locally representable and relatively acyclic notions of fibred structure.** The maps in a 1-category $\mathsf{E}$ with pullbacks assemble into a contravariant groupoid-valued pseudofunctor on $\mathsf{E}$ sending an object $X$ to the large groupoid of maps with codomain $X$. This pseudofunctor $\mathfrak{E}$ is referred to as the **core of self-indexing**—the “self-indexing” referring to the slice categories $\mathsf{E}_{/X}$ and the “core” referring to their groupoid cores. In [Shu19, 3.1], Shulman defines a **notion of fibred structure** on a category $\mathsf{E}$ with pullbacks as a strict discrete fibration with small fibers $\psi: \mathfrak{F} \rightarrow \mathfrak{E}$ in the 2-category of contravariant groupoid-valued pseudofunctors on $\mathsf{E}$ and pseudonatural transformations between them. Here, a *strict discrete fibration* is a strictly natural transformation whose components are fibrations of groupoids.

Unpacking this, a notion of fibred structure is given by:

- (i) for each map $f: Y \rightarrow X$ of $\mathsf{E}$, a set of “fibration structures”,

$$\begin{array}{c} W \xrightarrow{f^* g} Y \\ g^* f \downarrow \quad \downarrow f \\ Z \xrightarrow{g} X, \end{array} \tag{2.1.1}$$

a function from the set of fibration structures on $f$ to the set of fibration structures on $g^* f$ that is pseudofunctorial in pullback squares.

See [Shu19, §3] for considerably more discussion. Following Shulman, we refer to the “structured fibrations” associated to a notion of fibred structure $\mathfrak{F}$ as **$\mathfrak{F}$-algebras** and then refer to a pullback

12