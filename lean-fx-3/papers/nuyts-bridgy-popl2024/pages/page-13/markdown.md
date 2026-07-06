Internal and Observational Parametricity for Cubical Agda

8:13

makes use of capturing, as was the case for EXT- \( \beta \) . This means in particular that a semi-freshness constraint is checked when comparing two inhabitants of Gel.

2.5.2 The Second Inverse Condition. Regarding the second inverse condition needed to prove relativity, one has to show  \( \forall(AA:BridgeA_{0}A_{1})\to\text{Gel}A_{0}A_{1}(\lambda a_{0}a_{1}.BridgeP_{x,AAx}a_{0}a_{1})\equiv AA \) . Formally proving this lemma in Agda --bridges was far from trivial (see our accompanying library). In their paper and technical report, Cavallo and Harper [2019, 2021] sketch a proof of this lemma based on a relational extensionality principle for equivalences whose lengthy proof they also sketch. The principle is a characterization of the type of heterogeneous bridges between equivalences and its formulation is somewhat comparable to extentEquiv. We merely indicate here that our formal proof involves the pasting of several 2-dimensional paths in Type, whose construction relies on the path interval operations  \( \sim,\wedge,\vee \)  provided by Agda --cubical.

### 2.6 Other Relational Extensionality Principles

The primitives extent and Gel, gel, ungel we have implemented grant relational extensionality principles for the \(\Pi\) type former and for the universe Type, respectively. It turns out that their addition alone ensures the validity of similar principles for the other primitive type formers of the theory. For instance, as is the case for paths, a bridge at \(\Sigma[a\in A]Ba\) between pairs \((a_0,b_0),(a_1,b_1)\) can equivalently be regarded as a bridge in the base \(aa:Bridge_A a_0 a_1\) together with a heterogeneous bridge over it \(bb:BridgeP_{x,B(aax)}b_0b_1\). There also exist relational extensionality principles for the path type \(\equiv\) and the Bridge type itself. Essentially, those two principles reflect the fact that is always possible to swap the order of bridge and path variables in the context.

Relational extensionality principles for specific inductive data types can also be stated and proved in Agda --bridges. For instance, in their paper CH prove such a principle for the type of booleans Bool. The principle expresses that Bool is bridge-discrete, that is, the only bridges in Bool are the ones corresponding to its paths:  \( b_{0} \equiv_{Bool} b_{1} \simeq (\text{Bridge}_{\text{Bool}} b_{0} b_{0}) \) . Since Bool has no non-reflexivity paths (i.e., is an h-set in HoTT parlance), there are only two bridges in Bool: the reflexivity bridges at true and false. We have adapted the argument of CH to prove in Agda --bridges a similar principle for the List parametrized data type. More precisely, it is a dependent extensionality principle as it characterizes the type of heterogeneous bridges  \( \text{BridgeP}_{x,\text{List}(AAx)} as_{0} as_{1} \)  between two lists  \( (as_{0} : \text{List } A_{0}), (as_{1} : \text{List } A_{1}) \)  where AA : Bridge  \( A_{0} A_{1} \) .

ListRel : ∀ {A₀ A₁ : Type} (R : A₀ → A₁ → Type) → List A₀ → List A₁ → Type

ListRel R [] [] = Unit

ListRel R [] (_ ::_) = ⊥

ListRel R (_ ::_) [] = ⊥

ListRel \(R(a_0::as_0)(a_1::as_1) = Ra_0a_1\times \mathrm{ListRel}Ras_0as_1\)

ListvsBridgeP : ∀ {A₀ A₁ : Type} (AA : Bridge A₀ A₁) (as₀ : List A₀) (as₁ : List A₁) →

ListRel (BridgeP (λ x → AA x)) as₀ as₁ ≈ BridgeP (λ x → List (AA x)) as₀ as₁

The principle essentially expresses that a bridge between lists is a list of bridges. Indeed, ListRel R is an inductively defined relation between the types List  \( A_{0} \)  and List  \( A_{1} \)  which holds for  \( as_{0}, as_{1} \)  exactly when the latter lists have the same size and exhibit R-related values at each index.

### 2.7 Low-Level Parametricity

We are now ready to prove theorems for free from first principles in Agda --bridges. It is customary in type theories with internal parametricity (incl. CH) to prove free theorems by directly appealing

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.