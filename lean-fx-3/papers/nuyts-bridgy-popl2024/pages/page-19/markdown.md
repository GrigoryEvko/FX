Internal and Observational Parametricity for Cubical Agda

8:19

### 3.2 Obstructions to the SRP and SIP

In this subsection we argue that proving the SIP, or worse, the SRP at a given type can get tedious. We begin with an example of SIP and SRP proofs for the type of pointed unary type operations PointedOp = Σ[F ∈ Type → Type] ((X : Type) → X → FX).

Example 3.3 (The SIP via extensionality principles). By repeatedly applying extensionality principles (see Section 2.1.3) we can characterize the meaning of a path between such pointed operations:

\[
\begin{array}{l} (F _ {0}, f _ {0}) \equiv_ {\text { PointedOp }} (F _ {1}, f _ {1}) \\ \simeq \Sigma [ F F \in F _ {0} \equiv_ {\text { Type } \rightarrow \text { Type }} F _ {1} ] \operatorname{PathP} _ {i. (X: \text { Type }) \rightarrow X \rightarrow F F i X} f _ {0} f _ {1} \\ \simeq \Sigma [ F F ^ {\prime} \in (X: \text { Type }) \rightarrow (F _ {0} X) \equiv_ {\text { Type }} (F _ {1} X) ] \operatorname{PathP} _ {i. (X: \text { Type }) \rightarrow X \rightarrow F F ^ {\prime} X i} f _ {0} f _ {1} \\ \simeq \Sigma [ e \in (X: \text { Type }) \rightarrow F _ {0} X \simeq F _ {1} X ] \operatorname{PathP} _ {i. (X: \text { Type }) \rightarrow X \rightarrow \mathrm{ua} (e X) i} f _ {0} f _ {1} \\ \simeq \Sigma [ e \in (X: \text { Type }) \rightarrow F _ {0} X \simeq F _ {1} X ] ((X: \text { Type }) \rightarrow (x: X) \rightarrow \operatorname{PathP} _ {i. u a (e X) i} (f _ {0} X x) (f _ {1} X x)) \\ \simeq \Sigma [ e \in (X: \text { Type }) \rightarrow F _ {0} X \simeq F _ {1} X ] ((X: \text { Type }) \rightarrow (x: X) \rightarrow f _ {0} X x [ e X ] f _ {1} X x) \\ \end{array}
\]

We conclude that a path between pointed operations \((F_0, f_0)\) and \((F_1, f_1)\) consists of a pointwise equivalence between \(F_0\) and \(F_1\), compatible with the pointings \(f_0\) and \(f_1\).

Example 3.4 (The SRP via relational extensionality principles). Set \(\operatorname{Rel} X_0 X_1 := X_0 \to X_1 \to \text{Type}\) and ra := relativity. We can characterize bridges at PointedOp by applying the principles discussed in Section 2.5.1, 2.6.

\[
\begin{array}{l} \operatorname{Bridge} _ {\text { PointedOp }} \left(F _ {0}, f _ {0}\right) \left(F _ {1}, f _ {1}\right) \\ \simeq \Sigma [ F F: \operatorname{Bridge} _ {\text { Type } \rightarrow \text { Type }} F _ {0} F _ {1} ] \operatorname{BridgeP} _ {y. (X: \text { Type }) \rightarrow X \rightarrow F F y X} f _ {0} f _ {1} \\ \simeq \Sigma [ F F ^ {\prime}: (X _ {0} X _ {1}: \text {Type}) \rightarrow \operatorname{Bridge} _ {\text {Type}} X _ {0} X _ {1} \rightarrow \operatorname{Bridge} _ {\text {Type}} (F _ {0} X _ {0}) (F _ {1} X _ {1}) ] \\ (X _ {0} X _ {1}: \text { Type }) (X X: \text { Bridge } _ {\text { Type }} X _ {0} X _ {1}) (x _ {0}: X _ {0}) (x _ {1}: X _ {1}) \rightarrow \\ \operatorname{Bridge} \mathrm{P} _ {y. X X y} x _ {0} x _ {1} \rightarrow \operatorname{Bridge} \mathrm{P} _ {y. F F ^ {\prime} X _ {0} X _ {1} X X y} \left(f _ {0} X _ {0} x _ {0}\right)\left(f _ {1} X _ {1} x _ {1}\right) \\ \simeq \Sigma [ F r: (X _ {0} X _ {1}: \text { Type }) \rightarrow \operatorname{Rel} X _ {0} X _ {1} \rightarrow \operatorname{Rel} (F _ {0} X _ {0}) (F _ {1} X _ {1}) ] \\ (X _ {0} X _ {1}: \text { Type }) (R: \operatorname{Rel} X Y) (x _ {0}: X _ {0}) (x _ {1}: X _ {1}) \rightarrow \\ \operatorname{Bridge} \mathrm{P} _ {y. \mathrm{ra} R y} x _ {0} x _ {1} \rightarrow \operatorname{Bridge} \mathrm{P} _ {y. \mathrm{ra} (F r X _ {0} X _ {1} R) y} \left(f _ {0} X _ {0} x _ {0}\right)\left(f _ {1} X _ {1} x _ {1}\right) \\ \simeq \Sigma [ F r: (X _ {0} X _ {1}: \text { Type }) \rightarrow \operatorname{Rel} X _ {0} X _ {1} \rightarrow \operatorname{Rel} (F _ {0} X _ {0}) (F _ {1} X _ {1}) ] \\ (X _ {0} X _ {1}: \text { Type }) (R: \operatorname{Rel} X Y) (x _ {0}: X _ {0}) (x _ {1}: X _ {1}) \rightarrow \\ (R x _ {0} x _ {1}) \rightarrow F r X _ {0} X _ {1} R (f _ {0} X _ {0} x _ {0}) (f _ {1} X _ {1} x _ {1}) \\ \end{array}
\]

We conclude that a bridge between pointed operations \((F_0, f_0)\) and \((F_1, f_1)\) consists of a relation transformer \(Fr\) between them such that the pointings \(f_0\) and \(f_1\) send related pairs to related pairs.

The examples above required rote work: we had to apply a series of extensionality principles which was entirely dictated by the formation of PointedOp. Hence, it is clear that proofs of the SIP and SRP at a type T scale at least with the complexity of T: for each type former F used to define T, an appropriate extensionality principle must be used to swap PathP/BridgeP and F.

Moreover we argue that proving the SRP is in general strictly harder than proving the SIP, because of three obstructions which we list here.

The first obstruction is that the extentEquiv principle of Section 2.4 always produces an extra Bridge type when characterizing the type of bridges between two given functions. Both generated Bridge types must be further characterized to finish the SRP proof at hand. This is to compare with the funextEquiv principle of Section 2.1.3 which (if not in the fully dependent case) does not produce an extra PathP type.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.