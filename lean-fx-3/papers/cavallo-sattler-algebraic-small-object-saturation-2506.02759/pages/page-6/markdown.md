(a) colimits of \((1 + \alpha)\)-chains in \(\mathcal{M}\) are Van Kampen for \(P\) for \(\alpha \preceq \kappa\);
(b) cobase changes of maps in \(\mathcal{M}\) are Van Kampen for \(P\).

Any lift of  \( D_{u}\colon\mathcal{E}^{\rightarrow}\to\mathcal{E}^{\rightarrow} \)  through  \( U_{P}\colon\operatorname{Ext}_{P}\to\mathcal{E}^{\rightarrow} \)  induces a functor  \( L_{p}-Coalg\to Ext_{P} \)  over  \( E^{\rightarrow} \)  assigning an extension operation to every left map of the AWFS.

### 1.2 Intuition

The reduction of the algebraic small object argument to a free monad construction is useful for abstract reasoning, but it can obscure the intuition behind our saturation theorems 3.5.6, 3.5.13, and 3.5.16. To motivate them, we first review Quillen's small object argument, then unfold Garner's and compare.

#### 1.2.1 Quillen's small object argument

Given a set of generating left maps \( S \subseteq \mathcal{E}^{\rightarrow} \), the small object argument constructs a factorization of \( f \colon X \to Y \) by iteratively attaching new "cells" to \( X \), eventually arriving at a map \( f \colon X' \to Y \) that lifts against \( S \) together with a comparison left map \( m \colon X \to X' \) over \( Y \). In the first stage of the iteration, one takes each lifting problem \( \alpha \colon u \to f \) against a map \( u \colon A \to B \) in \( S \) and glues a copy of the codomain \( B \) onto the existing copy of the domain \( A \) in \( X \), defining a new object \( X_1 \):

\[
\begin{array}{c} \coprod_ {(u: A \to B) \in S} A \longrightarrow \coprod_ {(u: A \to B) \in S} B \\ \alpha : u \to f \\ \Biggl \downarrow \\ X \xrightarrow {m _ {1}} X _ {1} \\ f \xrightarrow {f _ {1}} Y \end{array} \tag {1.3}
\]

Any class defined by left lifting is closed under small coproducts and cobase change, so  \( m_{1} \)  is a left map. While  \( f_{1} \)  has a solution for every lifting problem  \( \alpha: u \to f_{1} \)  that factors through  \( f \to f_{1} \), it need not itself be a right map. Thus one iterates, producing a transfinite sequence  \( f \to f_{1} \to f_{2} \to \cdots \). The sequence does not typically converge, but the approximations do become right maps at some ordinal index  \( \kappa \)  given compactness assumptions on the domains of the maps in S (the titular “small objects”). The composite

\[
X \xrightarrow {m _ {1}} X _ {1} \xrightarrow {m _ {2}} X _ {2} \longrightarrow \dots \longrightarrow X _ {\kappa}
\]

is a left map, since any class defined by left lifting is closed under transfinite composition, and so  \( X \rightarrow X_{\kappa} \rightarrow Y \)  is the desired factorization. By construction, the left factors of the factorizations are cell complexes built from maps in S.

#### 1.2.2 Garner's algebraic small object argument

Garner's argument follows the same blueprint as Quillen's, but modifies both the one-step approximation construction and the process of iteration.

The one-step factorization (1.3) of Quillen's argument has a natural generalization to the diagram case. Rather than attaching a coproduct of all lifting problems against \( f \), one attaches the

6