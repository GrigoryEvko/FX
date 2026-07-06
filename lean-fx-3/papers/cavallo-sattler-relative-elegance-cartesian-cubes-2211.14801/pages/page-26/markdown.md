26

E. Cavallo and C. Sattler

By way of this duality, we have in particular an embedding of $\square_{\vee}$ in the category of finite semilattices, induced by the embedding of its opposite in its category of models:

$$\square_{\vee} \xrightarrow{k} \mathbf{01SLat}_{\text{fin}}^{\text{op}} \xrightarrow{\simeq} \mathbf{SLat}_{\text{fin}}.$$

Here we use that the free semilattice on a finite set of generators is a finite semilattice. Unpacking, this embedding sends $T^n$ to $\mathbf{01SLat}(F(n), [1]) \cong \mathbf{Set}(n, U[1]) \cong [1]^n$.

Notation 4.6 Henceforth we regard $\square_{\vee}$ as a subcategory of SLat, in particular writing $[1]^n$ rather than $T^n$ for its objects.

We can also describe the cubes in SLat as free semilattices on posets. Given a poset $A$, write $1 \star A$ for the poset obtained by adjoining a minimum element $\bot$ to $A$. For any set $S$, we have a monotone map $\eta_n: 1 \star S \to [1]^S$ sending $\bot$ to $\bot$ and $i \in S$ to the element of $[1]^S$ with 1 at its $i$th component and 0 elsewhere.

Proposition 4.7 For any $S \in \mathbf{Set}_{\text{fin}}$, the map $\eta_S$ exhibits $[1]^S$ as the free semilattice on the poset $1 \star S$. That is, for any $A \in \mathbf{SLat}$ and monotone map $f: 1 \star S \to A$, there is a unique semilattice morphism $f^1: [1]^S \to A$ such that $f = f^1 \eta_S$.

### 4.2 Cubical-type model structure on semilattice cubical sets

We now define our model structure on $\mathrm{PSh}(\square_{\vee})$ using Corollary 3.33. That our case satisfies the corollary's hypotheses is essentially an application of existing work, namely [CMS19] or [Awo23], so we do not give many proofs, only enough of an outline to guide an unfamiliar reader through the appropriate references. We point to [GS17; Sat17; AGH24, §8] for further details on constructing model structures of this kind and to [LOPS18] for the definition of the universe in particular.

Assumption 4.8 For simplicity, we work with a single universe: we assume a strongly inaccessible cardinal $\kappa$ and define a model structure on the category $\mathrm{PSh}_{\kappa}(\square_{\vee})$ of $\kappa$-small presheaves. Outside of this section, we suppress the subscript $\kappa$. As described in Remark 3.34, it is possible to eliminate the use of universes at the cost of some complication; alternatively, one can assume that every fibration belongs to some universe to obtain a model structure on all of $\mathrm{PSh}(\square_{\vee})$.

Notation 4.9 We write $\mathbb{I} := k[1] \in \mathrm{PSh}(\square_{\vee})$ for the representable 1-cube. We write $\delta_k: 1 \to [1]$ for the endpoint inclusion picking out $k \in \{0, 1\}$ and write $\varepsilon$ for the unique degeneracy map $[1] \to 1$.

#### 4.2.1 Factorization systems

As analyzed by Gambino and Sattler [GS17], a key feature of cubical-type model structures is that their fibrations are characterized by a uniform lifting property. This characterization is used to obtain the model structure's factorization systems constructively and to define fibrant universes of fibrations. We avoid formally introducing algebraic

2025/10/16 00:43