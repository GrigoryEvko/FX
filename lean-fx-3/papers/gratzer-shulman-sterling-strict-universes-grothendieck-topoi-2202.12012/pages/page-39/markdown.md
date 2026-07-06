STRICT UNIVERSES FOR GROTHENDIECK TOPOI

39

The independence of Markov's principle from intuitionistic higher-order logic is established easily by considering the internal logic of the topos of sheaves on Cantor space $\mathcal{C}$, *i.e.* the space of infinite binary sequences equipped with the product topology. If $\mathrm{Sh}(\mathcal{C})$ did not model universes, we would not however be able to use it directly to verify the independence of Markov's principle from Martin-Löf type theory with universes. Our result concerning universes in Grothendieck topoi, however, allows one to immediately deduce the independence of Markov's principle from Martin-Löf type theory with universes without needing to pass to the significantly more complex stack semantics of Coquand, Mannaa, and Ruch [CMR17], bypassing as well the detour through operational semantics of Coquand and Mannaa [CM16].

6.1.2. COROLLARY. *Neither Markov's principle nor its negation is derivable in Martin-Löf type theory with a cumulative hierarchy of strict universes.*

6.2. SEMANTICS OF THE UNIVALENT UNIVERSES. The semantics of univalent universes has proved to be a crucial technical difficulty in models of homotopy type theory and cubical type theory; in particular, it is necessary to translate facts between the language of model category theory and the language of universes. We briefly illustrate how judicious application of (U8) has been used in the literature to entirely eliminate these difficulties [Awo21; KL21; Shu15; Shu19; Str14]. In fact, this observation was the original motivation for Shulman [Shu15] to isolate (U8).

We illustrate the utility of (U8) by tracing through the salient aspects of the model given by Kapulkin, Lumsdaine, and Voevodsky [KL21] and defer to Shulman [Shu15; Shu19] for a more systematic approach. Concretely, we will work in **sSet** and fix a pair of strongly inaccessible cardinals $\kappa_0 < \kappa_1$ inducing universes $\mathcal{V}_0 \subseteq \mathcal{V}_1$ each satisfying (U1–8). Moreover, by Section 4.4, we can choose a generic map for $\mathcal{V}_0$ whose base lies in $\mathcal{V}_1$.

Let $\mathcal{U}_i \subseteq \mathcal{V}_i$ be the class of Kan fibrations in $\mathcal{V}_i$.

6.2.1. LEMMA. *The class of maps $\mathcal{U}_i$ satisfies (U1,3,4,8).*

PROOF. (U1,3) follow immediately from the fact that $\mathcal{V}_i$ satisfies (U1,3) and that any right-orthogonal class is closed under composition and pullback. (U4) is an immediate consequence of the right-properness of the Kan-Quillen model structure.

To show that $\mathcal{U}_i$ satisfies (U8), we being by fixing a generic family $\pi_{\mathcal{V}_i} \colon E_{\mathcal{V}_i} \longrightarrow U_{\mathcal{V}_i}$ for $\mathcal{V}_i$ and defining the following restriction of $U_{\mathcal{V}_i}$:

$$U_{\mathcal{U}_i} = \{X : U_{\mathcal{V}_i} \mid X \text{ is a Kan complex}\}$$

More precisely, a point $\alpha \colon \Delta^n \longrightarrow U_{\mathcal{V}_i}$ factors through $U_{\mathcal{U}_i}$ if $\pi^*(\alpha)$ is a Kan fibration. This is a well-defined simplicial set because Kan fibrations are stable under pullback. We define $\pi_{\mathcal{U}_i}$ (resp. $E_{\mathcal{U}_i}$) as the restriction of $\pi_{\mathcal{V}_i}$ (resp. $E_{\mathcal{V}_i}$) to $U_{\mathcal{U}_i}$. We first prove that $\pi_{\mathcal{U}_i} \in \mathcal{U}_i$, and then verify (U8).