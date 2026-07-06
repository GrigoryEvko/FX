48

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

7.1. PROSPECTS FOR A CONSTRUCTIVE VERSION. Our constructions are highly classical; in particular, we rely on the theory of locally presentable categories and $\kappa$-compactness, both of which make heavy use of choice. Developing a constructively acceptable version of Section 4 remains an open problem. We briefly survey the landscape of universes within a particular constructive metatheory: the internal language of an elementary topos $\mathcal{E}$.

Although the literal definition of a Grothendieck universe is meaningless in $\mathcal{E}$, we can proceed analogously and fix a generic map $\tilde{\mathsf{V}} \rightarrow \mathsf{V}$ satisfying the appropriate version of (U2–4,6). The class $\mathcal{S}_{\mathsf{V}}$ classified by this map then satisfies (U1–6). Already some care must be taken; without choice, a family with $\mathsf{V}$-small fibers need not be classified by a map into $\mathsf{V}$. Absent the law of the excluded middle, (U8) is satisfied for at least the class of decidable monomorphisms $A \mapsto B$.

The Hofmann–Streicher construction exposed in Section 2 works over $\mathcal{E}$ without modification. In particular, the standard generic family of $\mathcal{S}_{\mathsf{V}}$ lifts to a universe in the category of internal presheaves $\Pr_{\mathcal{E}}(\mathcal{C})$ for any $\mathsf{V}$-small internal category $\mathcal{C}$. The class of maps $\tilde{\mathcal{S}}_{\mathsf{V}}$ classified by this map satisfies (U1–6). (U8) is satisfied only for the class of level-wise decidable monomorphisms: monomorphisms $A \mapsto B$ whose components $A(c) \mapsto B(c) \in \operatorname{Hom}_{\mathcal{E}}$ are all decidable [OP16]. In fact, Swan [Swa18] shows that this result is sharp: it is possible to choose a base topos in such a way that this generic map cannot satisfy (U8) for all monomorphisms, though it remains possible that there is another generic map satisfying (U8) for all monomorphisms. Finally, this universe induces a universe $\tilde{\mathcal{S}}_{\mathsf{V}}$ in any sheaf subtopos $\operatorname{Sh}_{\mathcal{E}}(\mathcal{C}, J)$. The construction is identical to that of Section 2 and $\tilde{\mathcal{S}}_{\mathsf{V}}$ satisfies (U1–6) just as in the classical setting. In this setting, however, the status of (U8) remains entirely open for this universe.

Over a base topos $\mathcal{E}$ not satisfying the axiom of choice, it is reasonable to hope that properties such as (U7) or (U8) might lift from $\mathcal{E}$ to any topos bounded over $\mathcal{E}$; this lifting is verified for (U7) in the context of algebraic set theory [JM95; vdB11], but the corresponding lifting for (U8) remains a conjecture.

# References

[AR94] Jiří Adámek and Jiří Rosický. Locally Presentable and Accessible Categories. London Mathematical Society Lecture Note Series 189. Cambridge University Press, 1994.

[Ang+21] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Kuen-Bang Hou (Favonia), Robert Harper, and Daniel R. Licata. “Syntax and models of Cartesian cubical type theory”. In: Mathematical Structures in Computer Science 31.4 (2021), pp. 424–468. DOI: 10.1017/S0960129521000347.

[AGV72] Michael Artin, Alexander Grothendieck, and Jean-Louis Verdier. Théorie des topos et cohomologie étale des schémas. Vol. 269, 270, 305. Lecture Notes in Mathematics. Séminaire de Géométrie Algébrique du Bois-Marie 1963–1964 (SGA 4), Dirigé par M. Artin, A. Grothendieck, et J.-L. Verdier. Avec la