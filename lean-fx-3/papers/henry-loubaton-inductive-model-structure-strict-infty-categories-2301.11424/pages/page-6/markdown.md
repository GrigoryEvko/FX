of the $\tau_n$ tower, which corresponds to an “inductive” notion of equivalences, and its localization that turns the coinductive equivalences into equivalences$^2$. However, this localization should be different from the limit of the $\pi_n$-tower, which might not be an interesting notion of $(\infty, \infty)$-categories. What we mean here is that we are not aware of any attempt to give a concrete definition of $(\infty, \infty)$-categories that seems to produce something that could be equivalent to this limit.

### 1.3 Overview of the Paper

Finally, we give a short presentation of the contents of the paper, the various model structures, and Quillen functors we will construct. We will assume some familiarity with the theory of left semi-model categories—the necessary material is recalled in Appendix A.

In Section 2.1, we briefly recall the basics of the theory of strict $\infty$-categories, mostly in order to fix our notations. The category $\infty$-Cat$^{+m}$ of $m$-marked $\infty$-categories is introduced in Section 2.2, and in Section 2.3 we introduce the two monoidal structures $\ominus$ and $\ominus$ on $\infty$-Cat$^{+m}$, which both correspond to the Gray-Crans tensor products at the level of the underlying strict $\infty$-categories but behave differently on the markings. $\ominus$ is meant to correspond to the Lax Gray-Crans tensor product, while $\ominus$ corresponds to the pseudo Gray-Crans tensor product.

Next, in Section 2.4, exploiting these monoidal structures, we set up the first left semi-model structure on $\infty$-Cat$^{+m}$, which we call the *inductive* model structure, whose properties are summarized in:

**1.2 Theorem.** *For any $m \in \mathbb{N} \cup \{\infty\}$, there is a combinatorial left semi-model structure on the category $\infty$-Cat$^{+m}$ of $m$-marked $\infty$-categories, called the inductive or unsaturated inductive model structure and denoted $\infty$-Cat$^{+m}_{ind}$, such that:*

- *This model structure is monoidal for both tensor products $\ominus$ and $\ominus$ (from Section 2.3).*
- *The cofibrations are the maps that are cofibrations of the canonical model structure between the underlying $\infty$-categories. (Proposition 2.34)*
- *The fibrant objects are the marked $\infty$-categories in which all marked arrows admit marked inverses up to higher marked arrows, and in which if there is a marked arrow $a \rightarrow b$, then $a$ is marked if and only if $b$ is marked.*
- *Fibrations between fibrant objects are the “isofibrations” (as defined in Section 3.3).*
- *Weak equivalences between fibrant objects are “equivalences of marked $\infty$-categories” (as defined in Section 3.4).*

The existence of this model structure is established in Section 2.4, but some of its properties, in particular, the characterization of fibrant objects and fibrations between fibrant objects, will only be established in Section 3.

This model structure is intended as a model for “strict $(\infty, m)$-categories”, i.e., strict $\infty$-categories whose arrows of dimension strictly superior to $m$ are

$^2$Provided that we can define the notion of coinductively invertible arrow in a “model independent” way, which is not investigated in this article.

6