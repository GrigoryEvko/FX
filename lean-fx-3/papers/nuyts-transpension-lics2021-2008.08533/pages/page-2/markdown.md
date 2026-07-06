16:2

A. NUYTS AND D. DEVRIESE

Vol. 20:2

combinations thereof [BBC$^{+}$19, CH21, RS17, WL20].$^{1}$ The presheaf models just cited almost all follow a common pattern: First one chooses a suitable base category $\mathcal{W}$. The presheaf category over $\mathcal{W}$ is automatically a model of dependent type theory with the important basic type formers [Hof97] as well as a tower of universes [HS97]. Next, one identifies a suitable notion of fibrancy and replaces or supplements the existing type judgement $\Gamma \vdash T$ type with one that classifies fibrant types:

**HoTT:** For homotopy type theory (HoTT, [Uni13]), one considers Kan fibrant types, i.e. presheaves in which edges can be composed and inverted as in an $\infty$-groupoid. The precise definition may differ in different treatments.

**Parametricity:** For parametric type theory, one considers discrete types [AGJ14, CH21, ND18a, NVD17]: essentially those that satisfy Reynolds' identity extension property [Rey83] which states that homogeneously related objects are equal. This can be expressed by requiring that any non-dependent function $\mathbb{I} \to A$ from the relational interval, is constant.

**Directed:** In directed type theory, one may want to consider Segal, covariant, discrete and Rezk types [RS17] and possibly also Conduché types [Gir64, Nuy18b][Nuy20a, ex. 8.1.27].

**Guarded:** In guarded type theory, one considers clock-irrelevant types [BM20]: types $A$ such that any non-dependent function $\odot \to A$ from the clock type, is constant.

**Nominal:** Nominal type theory [Che12, PMD15] can be modelled in the Schanuel topos [Pit13, §6.3]. This is the subcategory of nullary affine cubical sets (see Example 6.14 later on) that send pushouts in the base category to pullbacks in Set. This ensures that if a cell depending on names $\{i, j, k\}$ in fact only depends on $\{i, j\}$ and in fact also only depends on $\{i, k\}$, then it only depends on $\{i\}$.

To the extent possible, one subsequently proves that the relevant notions of fibrancy are closed under basic type formers, so that we can restrict to fibrant types and still carry out most of the familiar type-theoretic reasoning and programming. Special care is required for the universe U: it is generally straightforward to adapt the standard Hofmann-Streicher universe to classify only fibrant types, but the universe of fibrant types is in general not automatically fibrant itself.

**HoTT:** In HoTT, the Hofmann-Streicher universe of Kan types is usually automatically Kan.

**Parametricity:** In earlier work on parametricity with Vezzosi [NVD17, ND18a], we made the universe of discrete types discrete by modifying its presheaf structure and introduced a parametric modality in order to use that universe. In contrast, Atkey et al. [AGJ14] and Cavallo and Harper [CH21] simply accept that their universes of discrete types are not discrete.

**Directed:** In directed type theory, one could expect, perhaps via a directed univalence result [WL20], that the universe of covariant types is Segal.

**Guarded:** In guarded type theory, Bizjak et al. [BGC$^{+}$16] let the universe depend on a collection of in-scope clock variables lest the clock-indexed later modality $\triangleright : \forall (\kappa : \odot).U_{\Delta} \to U_{\Delta}$ (where $\kappa \in \Delta$) be non-dependent and therefore constant (not clock-indexed) by clock-irrelevance of $U \to U$ [BM20].

$^{1}$We omit models that are not explicitly structured as presheaf models [AHH18, LH11, Nor19].