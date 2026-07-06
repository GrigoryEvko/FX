DOUBLY WEAK DOUBLE CATEGORIES

7

In fact, after this paper was completed, we learned that Keisuke Hoshino has characterized virtual double categories, and also augmented virtual double categories [Kou20] (which also allow length-0 paths as lower boundaries), as implicit double categories with appropriate composition and decomposition operations.

Like implicit structures, virtual structures allow the characterization of weak structures without explicit coherence axioms, but there are two main differences. Firstly, in an implicit 2-category we can define composites simply in terms of isomorphisms internal to the structure, whereas in a virtual 2-category composites must be defined by way of universal properties (since an inverse of a many-to-one morphism would be a one-to-many morphism, which virtual structures do not have). Secondly, both representable implicit 2-categories and representable virtual 2-categories can be identified with bicategories; however, the maps of implicit 2-categories (using the definition of homomorphism that is automatic from the essentially algebraic presentation) correspond to pseudofunctors, whereas the maps of virtual 2-categories correspond to *lax* functors.

Moreover, virtual structures apparently cannot be used to define doubly weak double categories, since there does not seem to be a sensible notion of a double category that is both horizontally and vertically virtual.

1.3. **Other definitions.** The presentation outlined in Section 1.2 gives a monad on double computads whose algebras are doubly weak double categories (with chosen composites). But we may also describe the algebras of this monad more directly, without factoring through the intermediate step of implicit double categories: a doubly weak double category is a double computad equipped with 1-cell composition and identities (satisfying no axioms), plus a way of composing any formal diagram of 2-cells$^{4}$ along any way of composing up its boundaries, satisfying appropriate coherence axioms (see Corollary 5.7).

This is similar to Garner's definition of cubical bicategory as described above in Section 1.1; the only difference is that our definition uses a double computad, whereas the 2-cells in Garner's definition are all *squares*, i.e. the horizontal and vertical sources and targets are length-1 paths. Indeed, we will show that Garner's and Verity's definitions both can be derived from ours by simply ignoring some of the structure of a double computad.

More precisely, the forgetful functor from doubly weak double categories to *double graphs* (double computads consisting of only 0-cells, 1-cells, and squares) induces a monad whose algebras are precisely Garner's cubical bicategories. Likewise, the forgetful functor to *double graphs with bigons* (double computads consisting of only 0-cells, 1-cells, squares, and horizontal and vertical bigons$^{5}$) induces a monad whose algebras are precisely Verity's double bicategories.

In particular, our doubly weak double categories are *not* monadic over double graphs or double graphs with bigons; additional shapes featured in a double computad are necessary. (This is perhaps surprising, since bicategories *are* monadic over 2-graphs, a.k.a. 2-globular sets.) However, these forgetful functors are 'the

$^{4}$Here we refer only to formal diagrams that 'ought to be composable in a double category'. There are other formal diagrams, such as 'pinwheels' [DP93, Daw95], that are not even composable in a strict double category, and these are not composable in our doubly weak double categories either. (Although one can also consider (strict or weak) double categories in which such diagrams are composable, e.g. [LR25].)

$^{5}$By a 'bigon' we mean a globular 2-cell, having two opposite boundary paths of length 1 and the other two opposite paths of length 0.