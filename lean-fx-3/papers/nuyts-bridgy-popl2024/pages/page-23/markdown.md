Internal and Observational Parametricity for Cubical Agda

8:23

Similarly, we can reprove the lowChurchBool theorem of Section 2.7. The call to param-prf and the CH-inverse-cond module appearing in Fig. 2 are replaced by the following call to the param theorem and definition of an appropriate dRRG using ROTT:

param TypeRRG X≠X→X→X k Bool A (λbx → boolToCh b At f ≡ x) true t refl false f refl

X≠X→X→X : DispRRG TypeRRG

X≠X→X→X = →Form (X≠EIX) (→Form X≠EIX X≠EIX)

### 4.2 Church Encodings

Using ROTT and param we were able to prove a scheme of Church encodings for data types obtained out of a strictly positive functor, represented as a container [Abbott et al. 2005]. We first state the theorem and briefly explain its proof in Agda --bridges, and then discuss its hypotheses and significance in the more concrete case of the List type former.

Assume a type of shapes \(S: \text{Type}\) and a type family of positions \(P: S \to \text{Type}\). Assume that \(S: \text{Type}\) is bridge-discrete, i.e. has an equivalence \(\eta^S: (s_0 \equiv s_1) \simeq \text{Bridge}_S s_0 s_1\). Assume that \(P: S \to \text{Type}\) is dependently bridge-discrete, that is, for every \(s_0, s_1, (sr: s_0 \equiv s_1), (ss: \text{Bridge}_S s_0 s_1)\) such that \(sr[\eta^S]ss\) and for every \(p_0: Ps_0\) and \(p_1: Ps_1\), there exists an equivalence \(\eta^P: \text{PathP}_{i, P(sr i)} p_0 p_1 \simeq \text{BridgeP}_{x, P(ss x)} p_0 p_1\). Define \(F: \text{Type} \to \text{Type}\) as \(FX = \Sigma[s \in S] Ps \to X\). Additionally define the following Agda data type \(\mu F\):

data μF : Type where

fold : F ( μF ) → μF

Note here that the data type declaration is accepted by Agda since \( F \) is a container functor and its input \( X \) occurs strictly positively\(^{8}\). We assert that the following equivalence holds \( \mu F \simeq (X : \text{Type}) \to (FX \to X) \to X \). The proof follows a standard pattern. Recall that \( \mu F \) has an elimination principle \( \mu \text{Frec} : \forall T \to (FT \to T) \to \mu F \to T \). Going from left to right we can define a map toCh using the latter principle. Going from right to left we can define a map \( \lambda p \to p \mu F \) fold. Proving the first inverse condition is done by induction. The other condition requires parametricity and reads as follows (using funExt whenever needed):

\[
(p: (X: \text { Type }) \rightarrow (F X \rightarrow X) \rightarrow X) (A: \text { Type }) (f: F A \rightarrow A) \rightarrow
\]

\[
\operatorname{toCh} (p \mu F \text { fold }) A f \equiv_ {A} p A f
\]

This of course looks like a global free theorem in the sense of (4). We wish to obtain this equality by applying param at program \( p \) and at the (logical) relation given by the graph of the function \( \mu \mathrm{Frec} A f : \mu \mathrm{F} \to A \). We denote this graph as \( \mathrm{Gr}(\mu \mathrm{Frec} A f) : \mu \mathrm{F} \to A \to \mathrm{Type} \). To that end we must supply a RRG structure for the domain of \( p \) and a dRRG structure for its codomain. For its domain we use Tyfm as above. For its codomain we must show \( X : \mathrm{Type} \vDash (FX \to X) \to X \) dRRG. Applying the \( \Pi \mathrm{fm} \) rule of ROTT and other structural rules not displayed in Fig. 4 the goal is reduced to \( X : \mathrm{Type} \vDash FX \) dRRG. Recalling that \( FX = \Sigma [s \in S] Ps \to X \) we can apply the \( \Sigma \mathrm{fm} \) and \( \Pi \mathrm{fm} \) rules of ROTT thereby reducing the goal to providing a RRG structure for \( S \) and providing \( s : S \vDash Ps \) dRRG. We can repackage our bridge-discreteness hypotheses \( \eta^S, \eta^P \) as such structures. At this stage all premises of param have been supplied and so we expect to obtain from param something of type \( (\lambda X.(FX \to X) \to X)\{p\mu F, pA\}_{\mathrm{Gr}(\mu \mathrm{Frec} A f)} \). Again, contrary to its BridgeP

\( ^{8} \) Agda conveniently looks through the definition of F to decide this.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.