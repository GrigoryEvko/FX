8:20

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

The second and third obstructions relate to the fact that, in the SIP case, some tools are available to dismiss part of the rote work seen above. A first such tool is a theorem (see Rijke [2022] e.g.) that can be seen as a reformulation in cubical type theory of the $J$ rule of equality types. Recall that a type $A$ is contractible (isContr $A$) if it is equivalent to the unit type $\{\ast\}$.

THEOREM 3.5 (FUNDAMENTAL THEOREM OF IDENTITY TYPES). Assume $A : \text{Type}$ and a relation $Eq : A \rightarrow A \rightarrow \text{Type}$. Suppose that $Eq$ is reflexive, i.e., $\forall a \rightarrow Eq \, a \, a$. Additionally, suppose that $\forall a_0 \rightarrow \text{isContr}(\sum a_1 \in A \mid Eq \, a_0 \, a_1)$. Then $\forall a_0 \, a_1 \rightarrow (Eq \, a_0 \, a_1) \simeq (a_0 \equiv_A a_1)$.

This theorem might allow us to shortcut proofs as in Example 3.3, especially in the case of ordinary data types, by simply proving that the end result satisfies the above criteria. However, since bridges have no elimination principles like $J$, the theorem does not to our knowledge translate to the relational setting.

Similarly, the third obstruction is the lack of the following result, standard in HoTT but only available in case of the SIP. Recall that a type $P$ is an h-proposition if any two inhabitants of $P$ are equal, i.e., $\text{isProp} \, P = \forall p_0 \, p_1 \rightarrow p_0 \equiv_P p_1$. For instance the empty and unit types are h-propositions. The theorem guarantees the existence and unicity of heterogeneous paths between proofs of h-propositions.

THEOREM 3.6 (HETEROGENOUS EQUALITY OF PROOFS). Let $P : I \rightarrow \text{Type}$ be a line of h-propositions, i.e., there is a map $\text{isp} : (i : I) \rightarrow \text{isProp}(P \, i)$. Suppose that $p_0 : P \, i0$ and that $p_1 : P \, i1$. Then $\text{isContr}(Path P_{i, P \, i} \, p_0 \, p_1)^5$.

Typically, this theorem is used while proving the SIP for structured types of the form $\sum a \in A$ where for all $a, P \, a$ is an h-proposition. For instance this is the reason why two equivalences $e_0, e_1 : A_0 \simeq A_1$ are equal if and only if their underlying functions are equal $e_0 \equiv e_1 \simeq (e_0 \cdot \text{fst} \equiv e_0 \cdot \text{fst})$. This is to compare with the relational extensionality principle for equivalences evoked in Section 2.5.2 which has the hardest proof amongst basic relational principles.

Because of these obstructions to SRP proofs, we have developed a domain-specific language (DSL) to obtain proofs of the SRP at a given type $T$ by merely writing the type $T$ in the DSL. Our DSL is explained in the next subsection.

### 3.3 ROTT

The second improvement we make compared to low-level proofs of free theorems is the introduction of *relational observational type theory* (ROTT): a domain-specific language (DSL) implemented as a library in Agda --bridges. It allows users to (1) show the SRP at a type $T$ by merely writing their type $T$ in the DSL and (2) derive free theorems for $T$ in a straightforward manner.

Since ROTT has abstractions that compose *dependent types* $T$ satisfying the SRP (i.e. dRRGs from Definition 3.2), it is itself a dependent type theory. To be more precise, ROTT is a type theory *shallowly embedded* in Agda --bridges. This means that ROTT is not defined as some kind of data type of expressions whose constructors would be inference rules used to write types $T$. Instead, ROTT is an Agda --bridges library (part of our accompanying library) comprised of a bunch of theorems called 'semantic rules' explaining how to compose dRRGs. These Agda --bridges theorems are discussed in Section 3.3.1. As an example, we program in Fig. 3 the $\rightarrow$FM semantic rule of ROTT directly in Agda --bridges.

Additionally, ROTT also features a param theorem letting the user straightforwardly deduce free theorems from appropriate (d)RRGs instances (obtained with ROTT, e.g.). We see param as one of the rules of ROTT. It is discussed in Section 3.3.2.

$^5$For bridges, only $\text{isProp}(\text{Bridge} P_x \cdot P_x \cdot p_0 \cdot p_1)$ holds. By (2.5.1), $\text{Bridge} P_x \cdot \text{Gel} \cdot P_0 \cdot P_1 \cdot (\lambda \rightarrow \bot) \cdot x \cdot p_0 \cdot p_1 \simeq \bot$.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.