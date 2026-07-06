The most common displayed structure is a displayed category; here the terminology was introduced by [AL19]. This arises from the record type of categories, defined in the usual dependently typed way (where we omit the axioms for concision):

record Cat : Type where
ob : Type
hom : ob → ob → Type
id : (x : ob) → hom x x
comp : {x y z : ob} → hom y z → hom x y → hom x z
...

We do not discuss record types (including  \( \Sigma \) -types) in this paper, but the extension of  \( ^{d} \)  to them produces another record type whose fields have  \( ^{d} \)  applied to them. For instance, from a  \( \Sigma \) -type:

record \(\Sigma (A:\text{Type})\) \((B:A\to \text{Type})\) : Type where  
fst : A  
snd : B fst

We obtain:

record \(\Sigma^d\) (A : Type) (\(A'\) : Type\(^d\) A) (B : A → Type)
(B' : (A → Type)\(^d\) B) : Type\(^d\) (\(\Sigma\) A B) where
fst\(^d\) : A\(^d\) fst
snd\(^d\) : (B fst)\(^d\) snd

Applying (1.4) and the similar rule Type \( ^{d} \)   \( A \equiv A \rightarrow \)  Type, this becomes:

record \(\Sigma^d\) (A : Type) (\(A'\) : A → Type) (B : A → Type)
(B' : (x : A) → \(A'\) x → B x → Type) (s : \(\Sigma\) A B) : Type where
fst\(^d\) : A' (fst s)
snd\(^d\) : B' (fst s) fst\(^d\) (snd s)

In a similar way, the above definition of the record type of categories yields:

record Cat\( ^{d} \) (C : Cat) : Type where
ob\( ^{d} \) : ob C → Type
hom\( ^{d} \) : (x : ob C) (x' : ob\( ^{d} \) x) (y : ob C) (y' : ob\( ^{d} \) y) → hom C x y → Type
id\( ^{d} \) : (x : ob C) (x' : ob\( ^{d} \) x) → hom\( ^{d} \) x x' x x' (id C x)
comp\( ^{d} \) : {x : ob C} {x' : ob\( ^{d} \) x} {y : ob C} {y' : ob\( ^{d} \) y} {z : ob C}
{z' : ob\( ^{d} \) z} (α : hom C y z) (α' : hom\( ^{d} \) y y' z z' α) (β : hom C x y)
(β' : hom\( ^{d} \) x x' y y' β) → hom\( ^{d} \) x x' z z' (comp C α β)
...

Thus a displayed category over C has a type of objects indexed by those of C, types of morphisms indexed by pairs of objects-over-objects and by a morphism of C, identity and composition operations on displayed objects and morphisms that lie strictly over those in C, and similarly for the axioms.

As observed in [AL19], one use of displayed categories is to state definitions such as Grothendieck fibrations in terms of the existence of cartesian liftings strictly over any morphism in C, without internalizing definitional equality. Another is to construct categories and prove their properties in a modular way out of dependent pieces, just as we do for types using  \( \Sigma \) -types and more general records. It is 'well-known' by now that any sort of

10