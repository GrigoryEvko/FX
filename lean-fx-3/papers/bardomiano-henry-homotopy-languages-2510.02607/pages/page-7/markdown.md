Finally, in section 4 we prove two more invariance theorems (theorem 4.2), that are this time about the expressive power of the language and can be stated informally as:

3$^{rd}$ **Invariance Theorem.** *If $A$ and $B$ are two cofibrant objects of $\mathcal{M}$, then each formula in context $A$ can be translated into a formula in context $B$ that is “equivalent” in the sense that its interpretation in any fibrant object is the same.*

4$^{th}$ **Invariance Theorem.** *If $\mathcal{M}$ and $\mathcal{N}$ are two Quillen equivalent weak model categories, then any formula in the language of $\mathcal{M}$ can be similarly translated into an equivalent formula in the language of $\mathcal{N}$.*

More details on these will be given in the introduction to section 4.

One should also mention that, despite the paper being stated in the language of “weak” model categories, all our examples are actual Quillen model categories, and the reader can replace weak model categories by Quillen model categories almost everywhere. The only reason for which we consider weak model categories is because the extra generality doesn’t affect any of our results, and also because at some point in the proof of the second half of theorem 4.2 we need to use our construction of a language to something that in general will not be a full Quillen model category (even if we only try to prove theorem 4.2 for Quillen model categories). The main difference between weak model categories and Quillen model categories is that many results (and axioms) of a Quillen model category can only be applied to arrows from cofibrant to fibrant objects in a weak model category. A review of the notion of weak model category is in section C.1.

Notably, we will use the terminology “*core cofibration*” to mean cofibration between cofibrant objects and “*core fibration*” to mean fibration between fibrant objects.

The paper has three appendices that serve to review or introduce basic material. They can either be read first, or skipped entirely: Section A reviews Cartmell’s notion of generalized algebraic theory, and generalizes it to the infinitary case. The goal of section B is to establish the link between generalized $\kappa$-algebraic theory and a notion of $\kappa$-clan, with a notion of $\kappa$-contextual category as an intermediate. This result is absolutely crucial for the paper, but is a very expected generalization of what happens in the finitary case. Finally, section C reviews some material on weak model categories and introduces a notion of Reedy model categories in that context, which is only used in section 4.

7