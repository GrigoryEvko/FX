- We say that a cofibration in $\infty$-Cat$^{+m}$ is acyclic if it has the lifting property against all naive fibrations between fibrant objects.
- We say that a map in $\infty$-Cat$^{+m}$ is a fibration if it has the right lifting property against all acyclic cofibrations.

As before, it immediately follows from the small object argument that every morphism factors as an anodyne cofibration followed by a naive fibration, and all anodyne cofibrations are retracts of transfinite compositions of pushouts of the generating anodyne cofibrations.

2.39 Remark. It immediately follows from Proposition 2.36 that, as $j_+$ is a cofibration, all maps of the form $j_+ \hat{\odot} i$ are cofibrations. In particular, all acyclic fibrations are also naive fibrations and all anodyne cofibrations are cofibrations.

2.40 Proposition. Acyclic cofibrations and fibrations form a cofibrantly generated weak factorization system on $\infty$-Cat$^{+m}$. A morphism with fibrant target is a fibration if and only if it is a naive fibration.

Proof. This is a direct application of the results of Section 4 of [24]. Starting from the premodel (see Definition A.1) structure on $\infty$-Cat$^{+m}$ whose weak factorization systems are (cofibrations, acyclic fibrations) and (anodyne cofibrations, naive fibrations), we obtain the one with (cofibrations, acyclic fibrations) and (acyclic cofibrations, fibrations) as its "left saturation" L($\infty$-Cat$^{+m}$) in the sense of Theorem 4.1 of [24]. All the claims in the proposition follow from this Theorem 4.1.

2.41 Remark. Note that replacing $\hat{\odot}$ by $\hat{\odot}$ in Definition 2.38 would not change the definition. Indeed, if $X = Y^2$ is an $m$-marked $\infty$-category whose arrows of dimension strictly greater than 0 are all marked, then for any $m$-marked $\infty$-category $Z$ one has $X \odot Z = X \ominus Z$. As this applies to both the domain and the co-domain of $j_+$, it follows that $j_+ \hat{\odot} i = j_+ \hat{\odot} i$.

Also, the reader should not be worried about the use of $j_+$ in Definition 2.38 rather than $j_-$ or both $j_-$ and $j_+$. While using $j_-$ or both $j_-$ and $j_+$ instead of $j_+$ would change the definition of naive fibrations and anodyne cofibrations, this does not affect the definition of (naive) fibrations between fibrant objects; hence, the acyclic cofibrations and fibrations would not be changed. Indeed, once the existence of a (monoidal) model structure is established, it follows that $j_-$ is acyclic by 2-out-of-3, and hence all the maps $j_- \hat{\odot} i = j_- \hat{\odot} i$ are also acyclic cofibrations.

2.42 Lemma. If $f$ is an anodyne (resp. acyclic) cofibration and $g$ is a cofibration, then $f \hat{\odot} g$ and $f \hat{\odot} g$ are anodyne (resp. acyclic).

Proof. To get the result for "anodyne cofibrations," it is enough to prove it for the generating anodyne cofibrations. Let $i$ be one of the generating cofibrations and $f = j_+ \hat{\odot} i'$ be one of the generating anodyne cofibrations. We have $f \hat{\odot} i = j_+ \hat{\odot} (i \hat{\odot} i')$. As $i' \hat{\odot} i$ is a pushout of generating cofibrations $i_1, \ldots, i_k$ by Proposition 2.36, it follows that $j_+ \hat{\odot} (i \hat{\odot} i')$ is a pushout of the $j_+ \hat{\odot} i_k$ and hence is an anodyne cofibration.

The result for acyclic cofibrations follows from the formal properties of the pushout product: it follows that if $i$ is a cofibration and $p$ is a naive fibration,

19