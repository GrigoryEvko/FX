8

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

next best thing” to monadic: they are “of descent type”, which in this case means that the comparison functors from doubly weak double categories to double bicategories *and* to cubical bicategories are fully faithful. Thus we can indeed describe a doubly weak double category as *structure* on a double graph with bigons, or on a double graph, though these structures are not monadic.

We refer to the resulting equivalent notions of doubly weak double category respectively as *tidy double bicategories* and *tidy cubical bicategories*. Tidiness in both cases is a similar condition: it says that the operations of composing a square or bigon with an identity square are bijections. As noted above, tidiness for double bicategories is not a new condition; it already appeared without a name in Verity’s thesis [Ver92, Lemma 1.4.9], and in [RvdWAN25] it is called *saturation*. Our general theory shows that this apparently *ad hoc* condition does indeed yield a “correct” definition, in any reasonable sense.

With that said, an advantage of tidy double bicategories is that they yield an entirely *finite* presentation of doubly weak double categories, which we will show can be reduced to a double graph with binary composition and identity operations, and associator and unitor coherence squares, and appropriate axioms. This is perhaps the simplest definition, and the most amenable to checking all the pieces by hand in an example.

Finally, we give one last equivalent finite presentation, exhibiting doubly weak double categories as *monadic* over the category of double computads containing only 0-cells, 1-cells, squares, and all four kinds of *monogons*.

1.4. **Outline.** The structure of the paper is as follows. In Section 2, we spell out in detail the correspondence between bicategories and representable implicit 2-categories, using a quick definition of implicit 2-categories as strict 2-categories with free underlying 1-category. Then in Section 3, we by analogy quickly define implicit double categories, doubly weak double categories, and pseudofunctors between them, and give some examples (one with proofs postponed to Appendix A).

Then we move on to the computadic definitions. In Section 4, we introduce double computads. In Section 5, we present implicit structures, weak structures, and strict structures as monads on computads. And in Section 6, we upgrade the categories of implicit and weak structures to 2-categories, upgrade the monads to 2-monads, and prove coherence theorems.

Finally we consider alternative definitions and finite presentations: we discuss tidy double bicategories in Section 7, tidy cubical bicategories in Section 8, and monogons in Section 9.

1.5. **Acknowledgments.** We are grateful to Nathanael Arkor for a careful reading and several helpful suggestions and to Bob Paré for helpful discussions.

## 2. BICATEGORIES

We first spell out the equivalence between bicategories and representable implicit 2-categories, alluded to in the introduction (Section 1.2). Although it is helpful to view implicit 2-categories as *prior* to 2-categories, to get the main ideas across as quickly as possible, we start with a definition of implicit 2-categories in terms of strict 2-categories. Later we will give an alternative definition without reference to strict 2-categories, and describe 2-categories as extra structure on top of it.