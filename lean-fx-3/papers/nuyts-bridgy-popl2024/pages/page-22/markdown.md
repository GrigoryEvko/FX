8:22

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

RRG \(\Gamma\) and a displayed RRG \(T\) over it, all external dependent functions (i.e. all functions definable in Agda --bridges) from \(\Gamma\) to \(T\) respect logical relations.

\[
\frac {\Gamma \text {RRG} \qquad \Gamma \vDash T \text {dRRG} \qquad p : (\gamma : \Gamma) \to T _ {\gamma} \qquad \gamma_ {0} , \gamma_ {1} : \Gamma \qquad \gamma r : \Gamma \{\gamma_ {0} , \gamma_ {1} \}}{\text {param} \Gamma T p \gamma_ {0} \gamma_ {1} \gamma r : T \{p \gamma_ {0} , p \gamma_ {1} \} _ {\gamma r}} _ {\text {PARAM}}
\]

The proof of this theorem is elementary and proceeds in three steps, similar to the proof appearing in Section 3.1.4. We omit to write .fst to extract direct maps out of equivalences. First convert the logical relation \(\gamma r\) into a bridge \(\eta^{\Gamma}\gamma r:\mathrm{Bridge}_{\Gamma}\gamma_{0}\gamma_{1}\). Second use bare parametricity to obtain bare-param \(p\gamma_0\gamma_1\) (\(\eta^{\Gamma}\gamma r\)) which has type \(\mathrm{BridgeP}_{x,T(\eta^{\Gamma}\gamma r x)}(p\gamma_0)(p\gamma_1)\). Third by definition we know that \(\gamma r\eta^{\Gamma}\). Hence we may use the relativistic equivalence \(\eta^T\) of \(T\) to obtain \(\eta^{T - 1}(\mathrm{bare - param}p\gamma_0\gamma_1(\eta^{\Gamma}\gamma r))\) which has type \(T\{p\gamma_0,p\gamma_1\}_{\gamma r}\). This concludes the proof and definition of param.

The param theorem draws inspiration from observational type theory. It can indeed be seen as a relational analogue of the ap inference rule (see e.g. [Altenkirch et al. 2022] and Section 6) which states that terms of observational type theory act on identifications or isomorphisms, that is, observational proofs of equality. For this reason we say that our internal param-eticity theorem is also observational. In the next section we use ROTT and its param rule to obtain modular and concise proofs of internal free theorems.

## 4 INTERNAL OBSERVATIONAL PARAMETRICITY APPLIED

In this section we obtain several free theorems as one-liner invocations of the param theorem of Section 3.3.2. This is done by first constructing appropriate (d)RRGs using the rules of ROTT. All of our examples can be consulted in our accompanying library.

### 4.1 Reproving fthm and lowChurchBool

We begin by recasting our proof of the global free theorem fthm from Section 3.1.4, this time using ROTT and its param rule. Let \( p: (X: \text{Type}) \to \text{List } X \to \text{List } X \), let \( f: A_0 \to A_1 \) for \( A_0, A_1 \) two types and let \( as: \text{List } A_0 \). We want to apply param at program \( p \) and at (logical) relation \( \text{Gr } f: A_0 \to A_1 \to \text{Type} \). In order to do so we must first provide an RRG structure for Type, the domain of \( p \). This is achieved using the Tyfm rule of ROTT. Second, we must prove that \( X: \text{Type} \vDash \text{List } X \to \text{List } X \) dRRG. By the \( \Pi \)fm rule of ROTT (or rather \( \to \text{FM} \) of Fig. 3) it is sufficient to prove (twice) that \( X: \text{Type} \vDash \text{List } X \) dRRG. The latter displayed RRG appears as an example in Section 3.1.3. At this point all premises of param have been supplied.

Note how ROTT allows a significant improvement compared to proofs of the SRP “by hand” as shown Section 3.1.4. Instead of proving a lengthy equivalence chain, we simply have to write the following in Agda --bridges, using the →Form and XListX programs implemented by the ROTT library (Agda identifiers can feature symbols, as in XListX).

XListX→ListX : DispRRG TypeRRG

XListX→ListX = →Form XListX XListX

Looking at the conclusion of param we are about to obtain something of type  \( (\lambda X \rightarrow \text{List } X \rightarrow \text{List } X)\{p A_{0}, p A_{1}\}_{\text{Gr } f} \)  and contrary to the BridgeP type former, the latter type reduces to the expected relational parametricity statement, i.e.:

param TypeRRG XListX→ListX p A0 A1 (Gr f) :

\[
\forall x s _ {0} x s _ {1} (x s r: \text { ListRel } (\text { Gr } f) x s _ {0} x s _ {1}) \rightarrow \text { ListRel } (\text { Gr } f) (p A _ {0} x s _ {0}) (p A _ {1} x s _ {1})
\]

By applying this function to \( xs_0 = as_0, xs_1 = \text{map } f \, as_0 \) and by remarking that \( \text{ListRel} (\text{Gr } f) \, l_0 \, l_1 \) is the same predicate than \( \text{map } f \, l_0 \equiv l_1 \) we conclude the proof of \( \text{fthm} \).

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.