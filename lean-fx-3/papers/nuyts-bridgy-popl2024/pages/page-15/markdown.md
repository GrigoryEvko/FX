Internal and Observational Parametricity for Cubical Agda

8:15

latter parametricity proof to shortcut proofs of free theorems at types having $-\rightarrow-\rightarrow-$ as a subexpression. Lastly, these proofs are typically long even for seemingly simple examples of free theorems. Furthermore their complexity quickly gets intractable when the size of the target type $T$ grows (there are several reasons for this, discussed in the next section).

All in all, these drawbacks motivated us to develop in Agda --bridges a library providing user-friendly, compositional and short proofs of free theorems. This is the content of Section 3.

### 3 THE OBSERVATIONAL PARAMETRICITY OF AGDA BRIDGES

As explained in Section 2.7, low-level proofs of internal free theorems are unsatisfactory in several respects. We improve these low-level proofs in two steps.

Our first improvement stems from the observation that, in order to make use of internal parametricity, it is always sufficient to prove appropriate relational extensionality principles. More precisely, we argue that obtaining internal free theorems for an Agda --bridges program $p: (\gamma: \Gamma) \to T\gamma$ can be reduced to providing (dependent) relational extensionality principles for $p$'s domain and codomain, so characterizations of their (dependent) bridge types as types of actual logical relations: an equivalence $\eta^T: \dots \cong \text{Bridge}_T\gamma_0\gamma_1$ and an equivalence $\eta^T: \dots \cong \text{Bridge}_{X,T(\gamma\gamma x)}(t_0: T\gamma_0)(t_1: T\gamma_1)$ where $\gamma\gamma: \text{Bridge}_T\gamma_0\gamma_1$. This is explained in Section 3.1 and illustrated on an example in Section 3.1.4.

We call this informal sufficient condition for obtaining free theorems, which asks that all (dependent) types are equipped with a characterization of their Bridge/BridgeP type as logical relations, the structure relatedness principle (SRP). The SRP is precisely stated in Section 3.1. The reason behind this name is that there exists an analogous principle asking instead that all (dependent) types feature a characterization of their $\equiv$/PathP types as types of isomorphisms. The latter principle is known (to varying degrees of generality, see Section 6.3) as the structure identity principle (SIP) in HoTT/UF.

The second improvement we make compared to low-level proofs stems from the observation that proving the SRP or the SIP "by hand" at a given type can quickly get intractable, as explained in Section 3.2. To remedy this situation we introduce in Section 3.3 a shallowly embedded domain-specific language (DSL) implemented as an Agda --bridges library that allow the user to (1) show the SRP at a type $T$ by merely writing their type $T$ in the DSL (using the rules in Section 3.3.1) and (2) derive free theorems for $T$ in a straightforward manner (see the param theorem of Section 3.3.2). We call our DSL relational observational type theory (ROTT). By contrast with low-level proofs, ROTT provides abstractions to write user-friendly, modular and concise proofs.

### 3.1 The SRP and Bare Parametricity

The first improvement we make for better internal parametricity proofs is to systematically factor proofs of free theorems into two simpler statements: the structure relatedness principle (SRP) on one side, and bare parametricity on the other. We first explain these principles and then illustrate their use by deriving the global free theorem (4) of Section 1 in Agda --bridges.

3.1.1 Bare Parametricity. Bare parametricity is simply the fact that all programs defined in Agda --bridges have a canonical action on bridges. It can be summarized as the following bare-param program:

$$\text{bare-param}: \forall \{\Gamma: \text{Type}\} \{T: \Gamma \to \text{Type}\} (p: \forall \gamma \to T\gamma) (\gamma_0\gamma_1: \Gamma)$$

$$(\gamma\gamma: \text{Bridge}\gamma_0\gamma_1) \to \text{BridgeP}(\lambda x \to T(\gamma\gamma x)) (p\gamma_0) (p\gamma_1)$$

$$\text{bare-param } p\gamma_0\gamma_1\gamma\gamma = \lambda x \to p(\gamma\gamma x)$$

3.1.2 The SRP, Relativistic Reflexive Graphs and the SIP. The structure relatedness principle (SRP) is the following metatheoretical principle:

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.