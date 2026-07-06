has a section for all horn inclusions $\Lambda^L_+[n] \to \Delta_+[n]$ in $J_{\mathfrak{s},\text{Set}}$ and a *trivial fibration* if

$$X(\Delta_+[n]) \to X(\partial\Delta_+[n]) \times_{Y(\partial\Delta_+[n])} Y(\Delta_+[n])$$

has a section for all boundary inclusions $\partial\Delta_+[n] \to \Delta_+[n]$ in $I_{\mathfrak{s},\text{Set}}$. Similarly, *cofibrations* and *trivial cofibrations* are defined as $I_{\mathfrak{s},\mathcal{E}}$-cofibrations and $J_{\mathfrak{s},\mathcal{E}}$-cofibrations in the sense of Definition 3.2. Note that fibrations and trivial fibrations defined above coincide with $J_{\mathfrak{s},\mathcal{E}}$-fibrations and $I_{\mathfrak{s},\mathcal{E}}$-fibrations by the same argument as in Proposition 4.1.

**Lemma 12.1.** *If $\mathcal{E}$ is countably lextensive, then $\mathfrak{s},\mathcal{E}$ carries two enriched weak factorisation systems consisting of:*

- *cofibrations and trivial fibrations,*
- *trivial cofibrations and fibrations.*

*Proof.* This follows from Theorem 3.14 with the assumptions verified exactly as in the proof of Theorem 4.2. $\square$

**Theorem 12.2.** *The category of fibrant semisimplicial sets with weak homotopy equivalences as defined above (i.e., created by the free functor $L: \mathfrak{s},\text{Set} \to \mathfrak{s}\text{Set}$) is a fibration category.*

*Proof sketch.* The claim can be deduced from the existence of the fibration category of fibrant simplicial sets in [GSS19, Theorem 2.2.2]. The proof is analogous to the proof of [GSS19, Theorem 2.2.2] itself and depends on the following fact. If $f: X \to Z$ is a map between simplicial sets and $Uf$ factors (in semisimplicial sets) as a composite of a cofibration $i: UX \to B$ and a fibration $p: B \to UZ$, then $f$ factors as a composite of $i': X \to Y$ and $p': Y \to Z$ such that $i = Ui'$ and $p = Up'$. (Note that, in particular, $B = UY$, $i$ is a cofibration and $p$ is a fibration.) This holds by [Ste17, Theorem 2.1 and Addendum 2.2]. It will also rely the fact that $U$ preserves and reflects weak equivalences by [Hen19, Lemma 2.2.1].

Compared to the proof of [GSS19, Theorem 2.2.2], the present argument requires only two modifications. First, to construct a path object on a fibrant semisimplicial set $K$, we first apply the fact above (with $X = \emptyset$, $Y = K$ and $Z = 1$) to obtain a simplicial Kan complex $A$ such that $UA = K$. Then we obtain a path object on $K$ by applying $U$ to a path object on $A$. Second, we observe that the facts above imply that a fibration in $\mathfrak{s},\text{Set}$ is acyclic if and only if it is trivial (by reducing it to the same statement in $\mathfrak{s}\text{Set}$). Thus acyclic fibrations are stable under pullback. $\square$

**Lemma 12.3.** *A map $f: X \to Y$ in $\mathfrak{s},\mathcal{E}$ is a cofibration if and only if for all $n$ the map $X_n \to Y_n$ is a complemented inclusion. In particular, every object of $\mathfrak{s},\mathcal{E}$ is cofibrant.*

*Proof.* The claim follows already from the semisimplicial version of Proposition 4.3 since latching objects are empty, which is simpler to prove than Proposition 4.3 due to absence of degeneracy operators. $\square$

**Corollary 12.4.** *If $\mathcal{E}$ has finite limits, then every trivial fibration in $\mathfrak{s},\mathcal{E}$ admits a section.*

$^6$This is non-constructive, because of the use of [Ste17]. An alternative argument which works constructively can be found in [Hen19, Theorem 5.5.6]. It shows that semisimplicial set have a weak model structure analogous to the Kan–Quillen model structure. Given that even constructively all semisimplicial sets are cofibrant this is enough to obtain that the full subcategory of fibrant objects is a fibration category.

57