8:6

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

be denoted with $\lambda x.f$, $\lambda x \rightarrow f$ (Agda syntax) or sometimes just $x.f$. Logical relations between e.g. $x_0$ and $x_1$ are typically denoted with a postfix $r$ notation $xr$. Bridges and paths between $x_0$ and $x_1$ are rather denoted with a double-letter notation $xx$. The $\varepsilon$ symbol systematically ranges in $\{0, 1\}$.

## 2 THE INTERNAL PARAMETRICITY OF AGDA BRIDGES

Agda --bridges is a proof assistant extending the Agda --cubical proof assistant [Vezzosi et al. 2021]. Accordingly, the type theory that Agda --bridges implements, i.e., its primitives and their equational theory, is an extension of the type theory that Agda --cubical implements (called CCHM in the literature [Cohen et al. 2017]). A reminder about Agda --cubical appears in Section 2.1.

The type theory of Agda --bridges is an adaptation of the internally parametric DTT of Cavallo and Harper [2021] (referred to as the CH theory). In other words, Agda --bridges implements the primitives and equations specified by the CH theory (we mostly keep the same names), or rather relatively close variants. The CH theory is not entirely standard as it is a *substructural* (alternatively 'affine') type theory. Indeed, most of its parametricity primitives have typing rules, including operational semantics, that can only be used if certain conditions on free variables are satisfied. This is discussed in Section 2.2. The first main difference between the Agda --bridges and CH theories lies in how they both handle substructurality. Our solution, *freshness typechecking constraints* on free variables, is discussed in Section 2.3. Note that the other main difference w.r.t. the CH theory is that both type theories extend different kinds of cubical type theories. The latter difference is rather discussed in Section 5.

In the CH theory, the bridge type former is postulated to represent *logical relations*: relations between types that respect their structure, or proofs of relatedness under such relations. Concrete examples of logical relations will appear below or can be consulted in [Hermida et al. 2013], for example. To ensure that bridges do uniquely correspond to logical relations, additional primitives called extent and Gel are postulated by the theory. Internal parametricity then refers to the fact that all programs preserve bridges, which are in one-to-one correspondence with logical relations. Accordingly, Agda --bridges features primitives BridgeP, extent and Gel whose implementation and rules are explained in Sections 2.3, 2.4, 2.5. Occurrences of these primitives in a program or type may generate freshness constraints at typechecking time.

In Section 2.6 and Section 2.7 we use the above primitives to derive within Agda --bridges core theorems for internal parametricity as well as the free theorem $\text{Bool} \simeq (X : \text{Type}) \rightarrow X \rightarrow X \rightarrow X$ in a low-level style.

### 2.1 The Cubical Fragment of Agda Bridges

Agda --cubical is an implementation of cubical type theory (CCHM) on top of the Agda proof assistant. Overall, cubical type theory modifies standard intensional type theory in several respects. First, it treats proofs of equality as if they were topological *paths* (see Section 2.1.1). Second, it features language primitives that let it realize *univalence* as a theorem (see Section 2.1.3). The latter property characterizes type equality as type equivalence (i.e. having a 'bijection') and constitutes a defining aspect of *homotopy type theory* (HoTT) [Program 2013]. Earlier instances of HoTT assume univalence as an axiom instead. Third, these primitives include the so-called Kan operations called transport, hcomp in Agda --cubical. Our adaptation of the Kan operations is rather discussed in Section 5. Lastly, as an instance of HoTT, cubical type theory defines higher inductive data types (HITs) which we do not discuss in this work. We now remind the reader about paths, equivalences, univalence and other extensionality principles.

#### 2.1.1 Paths.

A major difference between Agda and Agda --cubical lies in how each system treats propositional equality. By contrast with the inductively defined equality types $\equiv$ of standard

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.