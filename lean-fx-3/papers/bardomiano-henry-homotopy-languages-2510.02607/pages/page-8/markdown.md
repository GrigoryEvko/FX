## Further remarks

We finish by mentioning that this work is closely related to Makkai's notion of 'First-order logic with dependent sorts' or FOLDS from [Mak95]. In a sense, Makkai's FOLDS corresponds to the special case where $T$ is the theory of presheaves on a direct category $I$, encoded using dependent type axioms only, with an additional equality predicate for the types corresponding to maximal objects of $I$. Because Makkai does not make assumptions about the existence of a model structure he only establishes an invariance theorem for what he calls 'very surjective maps' (our 'anodyne fibrations'), that is the analogous to our theorem 2.32, more general notions of equivalence and homotopy are not clearly available in his setting.

In conclusion, the present work is at the same time considering a more general algebraic setting (by allowing terms and type in $T$), but also is restricting the setting by assuming the presence of a model structure that gives a good homotopy theory to be invariant under, and allows obtaining much more interesting results. This seems to make our approach considerably more usable in practice, given the richness of examples it potentially covers.

It should be noted however that there are some results in [Mak95] that we have not yet been able to generalize to this new setting: Makkai established several results that essentially say that any formula that has the desired invariance properties is equivalent to one in the language introduced. Similar results are also given in [Fre76] and [Bla78], and this paper contains no analogue to these results.

## Acknowledgment

This work was supported by the Natural Sciences and Engineering Research Council of Canada (NSERC), funding reference number RGPIN-2020-067 awarded to Simon Henry.

## 2 The homotopy invariant language

### 2.1 Syntactic approach: The first-order language of a generalized algebraic theory

In this section, we give a very classic syntactical approach to the language we consider in this paper. We start from a generalized algebraic theory, and we build its first-order language on top of it.

8