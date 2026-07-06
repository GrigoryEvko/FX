Fib' : (X : ASST) (x : Z⁺ X) → SST
Z (Fib' X x) = Z⁺ᵈ (S⁺ X) x
S (Fib' X x) y = Fib'ᵈ X (S⁺ X) x y

#### 3.4.2 Pointed semi-simplicial types

More interesting examples of displayed coinductive types have nontrivial parametrizations, often involving more semi-simplicial types. For instance, we can define the structure of a pointing on a semi-simplicial type displayed-coinductively:

codata Pt (X : SST) : Type where
zp : Pt X → Z X
sp : (p : Pt X) → Pt^d X (S X (zp p)) p

We then have, for p : Pt X,

zp p : Z X ≡ X₀
zpᵈ (sp p) : Zᵈ (S X (zp p)) (zp p) ≡ X₁ (zp p) (zp p)
zpᵈᵈ (spᵈ (sp p)) : X₂ (zp p) (zp p) (zpᵈ (sp p)) (zp p) (zpᵈ (sp p)) (zpᵈ (sp p))

and so on. That is, an element of Pt X equips X with a 'fat point', i.e. a chosen 0-simplex zp that comes with all of the higher 'degenerate simplices' that one would expect to be associated to zp if it were in a simplicial set rather than a semi-simplicial one.

#### 3.4.3 Morphisms of semi-simplicial types

With a double parametrization, we can define a type of morphisms of semi-simplicial types.

codata Hom (X Y : SST) : Type where
zhom : Hom X Y → Z X → Z Y
shom : (f : Hom X Y) (x : Z X) → Hom^d X (S X x) Y (S Y (zhom f x)) f

As usual, we can unravel this a few steps to see what it looks like. zhom f is a function between types of 0-simplices, which we may denote \( f_0 \). At the next dimension we have:

\( zhom^{d} \)  (shom f  \( x_{0} \) )  \( x_{0} \)   \( \beta_{0} \) :  \( Z^{d} \)  (S Y (zhom f  \( x_{0} \) )) (zhom f  \( x_{0} \) )

which is to say

\( zhom^{d} \)  (shom f  \( x_{0} \) )  \( x_{0} \) :  \( X_{1} \)   \( x_{0} \)   \( x_{0} \)  →  \( Y_{1} \)  ( \( f_{0} \)   \( x_{0} \) ) ( \( f_{0} \)   \( x_{0} \) ).

We may denote this function by  \( f_{1} \) , and go on to extract a function  \( f_{2} \)  between types of 2-simplices and so on. We expect other basic operations on semi-simplicial types to be internalizable in a similar way.

## 4 Semantics

We now discuss the semantics of dTT. Specifically, we will show that from any model of ordinary dependent type theory with infinite limits, we can construct a model of dTT in which the original model sits as the discrete mode.

39