Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

We may then check directly that this assignment preserves cocartesian arrows by unfolding their construction in the Gl and checking this holds on global data once more. In the end, it amounts to the proof that $\iota$ preserves cocartesian edges; when restricted to the global edges $0 \le 1, 1 \le 2$ and $2 \le 3$ we find that the above characterization of $F_{012}$ collapses to a single application of Gl along various cocartesian functors. $\square$

### C.6 Straightening–unstraightening

**Corollary 6.5.** *The map $U : (C \to \text{Cat}) \to \text{Cat}_{/C}$ is an embedding.*

PROOF. To show that $U$ is an embedding, we will show that $\Delta_U : (C \to \text{Cat}) \to (C \to \text{Cat}) \times_{\text{Cat}_{/C}} (C \to \text{Cat})$ is an equivalence. Applying Axiom 6 along with the fact that all of the objects involved here are simplicial, it suffices to show that the following map is an equivalence:

$$\langle b \mid \Delta^n \to \text{Cat} \rangle \to \langle b \mid \Delta^n \to (C \to \text{Cat}) \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \rangle$$

Since both sides of this are categories, we may restrict to the case where $n = 0, 1$. In this case, it suffices to show that if $f, g :_b \Delta^n \to (C \to \text{Cat})$ and $p :_b U \circ f = U \circ g$ then there is a path $(f, \text{refl}) = (g, p)$. However, this is precisely equivalent to asking that the fiber of $(U \circ -)^\top$ over $\text{mod}_b (U \circ f)$ is contractible. By previous results, we know the fiber is a proposition and it is inhabited by $(f, \text{refl})$. Consequently, it is contractible as required. $\square$

**Corollary 6.6** (Straightening–unstraightening). *If $D :_b \mathcal{U}$ is a category, a map $f :_b D \to \text{Cat}_{/C}$ lifts along $U$ to $\text{Cat}^C$ if and only if*

- (1) for each $d :_b D$, the functor $f(d)$ is a cocartesian family.
- (2) for each $d :_b \mathbb{I} \to D$, the functor induced by $f \circ d : \mathbb{I} \to \text{Cat}_{/C}$ is a cocartesian functor between the cocartesian families.

PROOF. Our goal is to characterize for which $f$ the following map is an equivalence:

$$D \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \to D$$

Notably, we know already this map is an embedding (it is the pullback of $U$) and so we merely wish to characterize when it is surjective. Using Axiom 6 along with the fact that both sides are categories, it suffices to consider when the following maps are surjective:

$$\begin{array}{l} \langle b \mid D \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \rangle \to \langle b \mid D \rangle \\ \langle b \mid \mathbb{I} \to D \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \rangle \to \langle b \mid \mathbb{I} \to D \rangle \end{array}$$

We now unfold these maps and use Proposition 2.8. These guarantee that the first map will hit $d :_b D$ if and only if $f(d)$ is a cocartesian family. Similarly, the second map will hit $d :_b \mathbb{I} \to D$ if and only if $f \circ d$ is a cocartesian functor between cocartesian families. $\square$