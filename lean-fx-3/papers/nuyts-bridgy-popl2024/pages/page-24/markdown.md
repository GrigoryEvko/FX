8:24

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

counterpart, the latter type computes to the appropriate relational parametricity statement, i.e.:

\[
\text { param } \dots \mu F A (G r (\mu F r e c A f)):
\]

\[
(f _ {0}: F \mu F \rightarrow \mu F) (f _ {1}: F A \rightarrow A) (f r: \dots) \rightarrow \mu \text { Frec } A f (p \mu F f _ {0}) \equiv_ {A} p A f _ {1}
\]

By setting \( f_0 = \text{fold}, f_1 = f \) and providing an easy proof of their logical relatedness \( fr \) we get \( \mu \text{Frec } A f (p \mu F \text{ fold}) \equiv_A p A f \) and this proves the theorem.

Up to some reordering lemmas, we can obtain a Church encoding for the List data type as an instance of the above scheme of Church encodings: List \( A \simeq (X : \text{Type}) \to X \to (A \to X \to X) \to X \). To do this the \( S \) and \( P \) parameters of the scheme are set to \( S = 1 + A \) and \( P(\text{inl} tt) = \bot \), \( P(\text{inr} a) = \text{Unit} \). For this simpler List Church encoding, our bridge-discreteness hypotheses about \( S \) and \( P \) translate into the fact that \( A \) must be bridge-discrete for the encoding to hold. The reason is that, if \( A \) is not bridge-discrete, additional programs using their type variable non-parametrically will exist in the encoding. For instance Type is not bridge-discrete as its bridges are relations between types. Accordingly the encoding for List \( A \) with \( A = \text{Type} \) does not hold, essentially because some polymorphic programs can use their type variable non parametrically: \( \lambda X \, nl \, cs. \, cs \, X \, nl : (X : \text{Type}) \to X \to (\text{Type} \to X \to X) \to X \). Similar considerations appear in [Nuyts and Devriese 2018].

### 4.3 System F

We can prove Reynolds's abstraction theorem [Reynolds 1983] for predicative System F [Leivant 1991] using ROTT and param. Indeed predicative System F is a subset of ROTT and the param theorem for dRRGs in that subset exactly expresses the abstraction theorem.

COROLLARY 4.1. By analogy to Section 3.3.2, we have the following “inference rule”, which states that, given a kinding context \(\Gamma\) of predicative System \(F\) (consisting of type variables labeled with levels) and a type \(T\) of predicative System \(F\) over this context, all external dependent functions (i.e. all functions definable in Agda --bridges) from \([\Gamma]\) to \([T]\) respect logical relations, where \([-]\) is an object-level translation from System \(F\) contexts (resp. types) to RRGs (resp. dRRGs).

\[
\frac {\Gamma   C t x - F \qquad \Gamma \vdash_ {F} T   t y p e - F \qquad p : (\gamma : [ [ \Gamma ] ]) \to [ [ T ] ] _ {\gamma} \qquad \gamma_ {0} , \gamma_ {1} : [ [ \Gamma ] ] \qquad \gamma r : [ [ \Gamma ] ] \{\gamma_ {0} , \gamma_ {1} \}}{p a r a m [ [ \Gamma ] ] [ [ T ] ] p   \gamma_ {0}   \gamma_ {1}   \gamma r : [ [ T ] ] \{p   \gamma_ {0} , p   \gamma_ {1} \} _ {\gamma r}}   _ {P A R A M - F}
\]

We emphasize that this result proves parametricity of the obvious embedding  \( \left[\left[-\right]\right] \)  of predicative System F into Agda --bridges, which is definable in Agda --bridges. That is,  \( \left[\left[-\right]\right] \)  is defined the expected way. For instance, the System F type  \( X: *_{0} \vdash_{F} X \to X \)  type-F interprets as the dRRG Type \( _{0} \models X \to X \)  dRRG which has  \( \lambda X. X \to X \)  as its carrier. In other words, the dRRG model  \( \left[\left[-\right]\right] \)  is not some contrived construction, but simply a proof that all Agda --bridges types that read as System F types satisfy the SRP.

Hence we recover Reynolds's original notion of parametricity in Agda --bridges. We remark that [Nuyts et al. 2017] could not prove this result as it lacked the power of the extent rule and therefore could not properly characterize bridges between functions. Cavallo and Harper's [2021] system (which is almost identical to Agda --bridges) could prove this result equally well but the authors did not do this, and the same holds almost certainly for Bernardy et al. [2015]. Thus, as far as we are aware, this establishes the first formal relation between traditional parametricity as defined by Reynolds for System F using a logical relation, and internally parametric type theory.

## 5 REIMPLEMENTING HCOMP AND TRANSP

Recall from Section 2.1 that when compared to plain dependent type theory, cubical type theories feature additional language primitives: (1) a path interval, path types, path abstraction and application, (2) Kan operations, (3) additional type formers for turning equivalences into paths

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.