replacement of both object. For $B^4\mathbb{Z}$ we discuss this above and it corresponds to take $B^4\mathbb{Z}^\sharp$. For $B^2\mathbb{N}$, as it has no non-identity invertible cells, $B^2\mathbb{N}^\flat$ is already fibrant. In particular $N(B^4\mathbb{Z})$ is a complicial set whose cells are all thin (marked). Hence the marking we put in $N(B^2\mathbb{N})$ actually do not matter in the computation and

$$[(B^2\mathbb{N})^\flat, (B^4\mathbb{Z})^\sharp]_{\mathbf{Strat}_V^{\perp m}} = [(B^2\mathbb{N})^\sharp, (B^4\mathbb{Z})^\sharp]_{\mathbf{Strat}_V^{\perp m}}$$

Hence we need to compute a set of homotopy class of maps between two complicial sets where every cell is marked - so this boils down to computing a set of homotopy class of maps in the Kan-Quillen model structure on simplicial set, using the unmarked Street nerve. We can now rely on two results from [2] to show arrive at our result:

Theorem 4.7 of [2] shows that for any group $G$, $N(B^n G)$ is an Eilenberg MacLane space $K(\pi, n)$. Theorem 4.9 (and especially example 4.10) shows that $N(B^2\mathbb{N})$ is homotopically equivalent to $N(B^2\mathbb{Z})$ and hence is also an Eilenberg MacLane $K(2, \mathbb{Z})$, so using the well known equivalence between simplicial sets and spaces, we can write

$$[N(B^2\mathbb{N}), N(B^4\mathbb{Z})]_{\mathbf{Strat}_V} \simeq [K(2, \mathbb{Z}), K(4, \mathbb{Z})]_{\mathrm{Space}}$$

and for this final hon set we can use methods from topology: $K(2, \mathbb{Z})$ can be realized as $\mathbf{CP}^\infty$ and hence

$$[K(2, \mathbb{Z}), K(4, \mathbb{Z})]_{\mathrm{Space}} = H^4(\mathbf{CP}^\infty) = \mathbb{Z}$$

where these last claim can be found in many algebraic topology textbook, for example [21].

## A Left Semi-model categories

Semi-model categories were first introduced by Spitzweck in [39], following a remark by Hovey in [25] that given a combinatorial symmetric monoidal model category $\mathcal{V}$, the category of monoids in $\mathcal{V}$ carries such a structure without assuming that $\mathcal{V}$ satisfies the "monoid axiom." This observation is sufficient for studying the homotopy theory of monoids in $\mathcal{V}$. A more general (but not equivalent) notion of semi-model structure was later introduced by Fresse in Section 12 of [18].

Contrary to what the name might suggest, a left semi-model category is not "half of a model category." It is a minor weakening of the definition of a Quillen model category that allows for nearly all standard homotopical constructions but is somewhat easier to define. This minor weakening often eliminates technical or unnatural assumptions in certain theorems, such as the monoid axiom mentioned above or the requirement of properness when constructing localizations (see Theorem A.8 below).

In brief, a left semi-model category is similar to a model category, but certain axioms, such as the lifting property and the existence of factorizations, are only required to hold for morphisms with cofibrant domains. Since any map can be replaced by an equivalent one with a cofibrant domain, and only maps between cofibrant and fibrant objects contribute directly to the homotopy theory, this

58