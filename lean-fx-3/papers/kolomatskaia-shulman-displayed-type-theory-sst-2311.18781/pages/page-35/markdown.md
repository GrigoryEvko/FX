### 3.2.5 Operations on semi-simplicial types

We can also use corecursion to define operations on semi-simplicial types that are essentially levelwise. For instance, any two semi-simplicial types have a product:

_×_ : SST → SST → SST
Z (X × Y) = Z X × Z Y
S (X × Y) ⟨ x , y ⟩ = (S X x) ×^d (S Y y)

Here in the S case, we have treated the non-displayed arguments of ×^d as implicit: its full type is

$$\_\times^d : \{X : SST\} \{X' : SST^d X\} \{Y : SST\} \{Y' : SST^d Y\} \to SST^d \{X \times Y\}$$

There is a similar dependently-typed version, i.e. a Σ-semi-simplicial-type:

Σ : (X : SST) → SST^d X → SST
Z (Σ X Y) = Σ (Z X) (Z^d Y)
S (Σ X Y) ⟨ x , y ⟩ = Σ^d (S X x) (S Y y)

There is an empty semi-simplicial type. Note that the S case can be omitted, since one of its arguments would belong to the empty type ⊥.

∅ : SST
Z ∅ = ⊥

Similarly, there is a trivial one:

T : SST
Z T = T
S T u = T^d

We can also take the product of any family of semi-simplicial types indexed by a discrete type. Note that the discreteness of A means that it doesn't need a displayed version when we apply ×^d in the S case.

X : (A :^Δ Disc) → ((a :^Δ A)) → SST) → SST
Z (X A X) = ((a :^Δ A) → Z (X a))
S (X A X) p = X^d A X (λ a → S (X a) (p a))

However, there are some things we would naturally expect to be able to define that do not seem possible with our current theory. For example, the disjoint union of semi-simplicial types should certainly have the disjoint union of 0-simplices, but the slice over a 0-simplex should come only from one of the two sides. That is, S (X + Y) (inl x) should be morally just S X x. However, S X x belongs to SST^d X, whereas S (X + Y) (inl x) must belong to SST^d (X + Y); thus we need to take its disjoint union with an empty semi-simplicial type displayed over Y.

We defined a 'global' empty semi-simplicial type above, and it seems intuitively that we should be able to define a 'constant' version of this displayed over Y. But as noted in section 3.1, without symmetry it does not seem possible to formulate a useful corecursor for SST^d, and without such a thing it is unclear how to define 'constantly displayed' semi-simplicial types. This suggests that further work in this direction might require the addition of symmetries.

35