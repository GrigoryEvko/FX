arXiv:2605.15080v1 [cs.LO] 14 May 2026

# Eliminating reversals from cubical type theories

Evan Cavallo ✉ 🚩

Department of Computer Science and Engineering, University of Gothenburg and Chalmers University of Technology, Sweden

Christian Sattler ✉ 🚩

Department of Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg, Sweden

## Abstract

Cubical type theories are designed around an abstract unit interval from which types of paths, used to represent equalities, are defined. Varying the operations available on this interval yields different type theories. A reversal is an involutive operator on the interval that swaps its two endpoints. We show that for cubical type theories with self-dual interval theories, such as the minimal theory of two endpoints or the theory of a bounded distributive lattice, the extension of the theory with a reversal that internalizes the duality is a conservative extension. The key tool is a “twist construction”: the product of an interval and its dual is again an interval with a reversal given by swapping coordinates.

Our conservativity result applies to “opaque” cubical type theories, without strict equations reducing the filling operator at concrete type formers or eliminators from higher inductive types at path constructors. Using the same twist construction, we also construct models of strict cubical type theory with reversals in categories of cubical sets without reversals. We thereby give the first model of a theory with reversals whose homotopy theory corresponds to that of topological spaces.

**2012 ACM Subject Classification** Theory of computation → Type theory; Theory of computation → Constructive mathematics

**Keywords and phrases** Dependent type theory, univalence, cubical type theory

**Funding** *Evan Cavallo*: Knut and Alice Wallenberg Foundation (KAW), Grant No. 2019.0116
*Christian Sattler*: US Air Force Office of Scientific Research, award number FA9550-24-1-0302

## 1 Introduction

Cubical type theories [12, 3, 2] extend Martin-Löf’s dependent type theory [24] with an abstract unit interval $\mathbb{I}$ which behaves much like a type. Types of *paths* $a_0 \sim^A a_1$, i.e., of terms $i : \mathbb{I} \vdash a(i) : A$ varying over the interval with fixed endpoints $a(0) = a_0$ and $a(1) = a_1$, play the role of equality types. As equality types, path types are remarkably well-behaved. For example, they natively satisfy function extensionality: equalities of functions correspond to families of pointwise equalities. With additional type formers, cubical type theories can also support Voevodsky’s univalence axiom and higher inductive types (HITs) [13, 9], making them models of homotopy type theory (HoTT) [39].

Path types satisfy different strict equations than Martin-Löf’s identity types. On the one hand, they do not support a J eliminator with a strict computation rule [12, §9.1]. On the other hand, for example, one has an operator witnessing that functions $f : A \rightarrow B$ preserve paths, $\text{cong}_f := \lambda p.\lambda i.f(p(i)) : (a_0 \sim^A a_1) \rightarrow (f(a_0) \sim^B f(a_1))$, that commutes *strictly* with function composition: $\text{cong}_g \circ \text{cong}_f = \text{cong}_{g \circ f}$. Such equations make cubical type theory a convenient setting for *synthetic homotopy theory* (see, e.g., Mörtberg and Pujet [25]), homotopy theory developed in the language of type theory, which can involve complicated manipulations with iterated identity/path types.

The range of strict equations satisfied by a cubical type theory’s path types depends on its *interval theory*, the collection of operations available on $\mathbb{I}$. Given a *reversal* operator