8:18

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

family \(\lambda X\to\) List \(X\) is a displayed RRG over the Type RRG, i.e., \((X:\mathrm{Type})\models\mathrm{List}X\) dRRG. The reason is that we can pick \((\lambda X\to \mathrm{List}X)\{as_0,as_1\}_{R} = \mathrm{ListRel}Ras_0as_1\), the inductive characterization of \(\mathrm{BridgeP}_{x,\mathrm{List}(AAx)}\) discussed in Section 2.6.

3.1.4 SRP + Bare Parametricity. Next, we illustrate how the SRP and bare parametricity can be used to improve proofs of internal free theorems. The main idea is that since (1) bare parametricity tells us that programs act on bridges and (2) the SRP guarantees that bridges uniquely correspond to logical relations, we expect that (3) programs act on logical relations as well. And all free theorems are consequences of the latter fact. We derive the global free theorem (4) of Section 1 in Agda --bridges, or rather a slightly reduced version of it for sparing space.

\[
\begin{array}{l} \text {fthm}: \forall \left\{A _ {0} A _ {1}: \text {Type} \right\} (f: A _ {0} \rightarrow A _ {1}) (a s _ {0}: \text {List} A _ {0}) \\ (p: (X: \text {Type}) \rightarrow \text {List} X \rightarrow \text {List} X) \rightarrow \text {map} f (p A _ {0} a s _ {0}) \equiv p A _ {1} (\text {map} f a s _ {0}) \end{array}
\]

The first step of our proof is to derive the SRP for the domain and codomain of \( p \). In other words we must (1) equip Type with an RRG structure (we chose the one induced by relativity) and (2) equip the type family \( \lambda X \). List \( X \to \text{List } X \) with a dRRG structure over the Type RRG. This amounts to proving the following characterization of the BridgeP type of \( \lambda X \). List \( X \to \text{List } X \) where \( A_0, A_1: \text{Type}, R: A_0 \to A_1 \to \text{Type}, AA: \text{Bridge } A_0 A_1, \text{Aprf}: R[\text{relativity}] AA, \) and \( q_\varepsilon: \text{List } A_\varepsilon \to \text{List } A_\varepsilon \) for \( \varepsilon = 0, 1 \). The proof uses the relational extensionality principles extentEquiv, ListvsBridgeP and the one for Gel (see Section 2.5.1, 2.6) as well as the fact that all type formers preserve equivalences. In the spirit of parametricity translations, an appropriate relational extensionality principle is used based on the head of the type former appearing in the BridgeP type at hand.

\[
\begin{array}{l} \operatorname{BridgeP} _ {x, \text { List } (A A x) \rightarrow \text { List } (A A x)} q _ {0} q _ {1} \simeq \\ \forall a s _ {0} a s _ {1} \rightarrow \operatorname{BridgeP} _ {x, \text {List} A A x} a s _ {0} a s _ {1} \rightarrow \operatorname{BridgeP} _ {x, \text {List} (A A x)} (q _ {0} a s _ {0}) (q _ {1} a s _ {1}) \simeq \\ \forall a s _ {0} a s _ {1} \rightarrow (\text { ListRel } (\text { BridgeP } _ {x, A A x}) a s _ {0} a s _ {1}) \rightarrow (\text { ListRel } (\text { BridgeP } _ {x, A A x}) (q _ {0} a s _ {0}) (q _ {1} a s _ {1})) \simeq \\ \forall a s _ {0} a s _ {1} \rightarrow (\text { ListRel } R a s _ {0} a s _ {1}) \rightarrow (\text { ListRel } R (q _ {0} a s _ {0}) (q _ {1} a s _ {1})) \\ \end{array}
\]

The second step of our proof is to “conjugate” bare-param with the SRP proof obligations we produced for Type and  \( \lambda X \) . List  \( X \rightarrow \)  List X. Let  \( A_{0}, A_{1}, f, as_{0}, p \)  be as in fthm. We first convert the graph relation of f denoted Gr f =  \( \lambda a_{0} a_{1} \rightarrow f a_{0} \equiv_{A_{1}} a_{1} \)  into a bridge denoted AA : BridgeType  \( A_{0} A_{1} \) , using relativity. Then we apply bare parametricity to AA.

\[
\text { bare - param } \{T = \lambda X \rightarrow \text { List } X \rightarrow \text { List } X \} p A _ {0} A _ {1} A A: \text { BridgeP } _ {x, \text { List } (A A x) \rightarrow \text { List } (A A x)} (p A _ {0}) (p A _ {1})
\]

Finally we use the above dependent principle for \(\lambda X\). List \(X \to\) List \(X\) and obtain a proof pf: \(\forall as_0 as_1 \to (\text{ListRel}(\text{Gr } f) as_0 as_1) \to (\text{ListRel}(\text{Gr } f) (p A_0 as_0) (p A_1 as_1))\). By a simple list induction we see that ListRel (Gr \(f\)) is equal to the relation \(\lambda as_0 as_1 \to (\text{map } f) as_0 \equiv as_1\). Thus pf \(as_0\) (map \(f as_0\)) refl grants the free theorem fthm.

The technique of factoring free theorems into SRP proof obligations and a call to bare-param is an improvement compared to low-level parametricity proofs like the one presented in Section 2.7. The proofs are conceptually easier. Moreover they allow for more compositionality. Indeed, contrary to Section 2.7 we are now in position to reuse the SRP proof obligations obtained for Type and \(\lambda X\). List \(X \to\) List \(X\) to derive (1) other free theorems for programs \(p: (X: \text{Type}) \to \text{List } X \to \text{List } X\) and even (2) shorter proofs of free theorems for a composite type having List \(-\to\) List - as a subexpression. However it turns out that proving SRP obligations "by hand" like in the above is challenging, in fact strictly more challenging than SIP obligations, as explained in the next subsection.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.