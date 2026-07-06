Internal and Observational Parametricity for Cubical Agda

8:25

in the universe, necessary to prove univalence, (4) (optionally) higher inductive types with path constructors.

The Kan operations of cubical type theory are necessary to make paths act as well-behaved proofs of equality. For instance, these operations are used to compose paths (i.e. prove transitivity of $\equiv$) or to turn the univalence map into an equivalence. The operational semantics of these operations is somewhat peculiar as it is defined by specifying how these operations reduce *at each type former*, i.e., by induction on the syntax of types. Hence the process of extending cubical type theory with a new type former $F$ requires extra work: specifying how the Kan operations reduce at $F$.

Agda --bridges is an extension of Agda --cubical which implements CCHM cubical type theory [Cohen et al. 2017]. Thus, Agda --bridges must implement reduction clauses for the Kan operations of Agda --cubical at the BridgeP and Gel type formers. In Agda --cubical, the Kan operations are primitives named *homogeneous composition* (hcomp) and *transport* (transp).

$$\text{transp} : (A : \text{I} \rightarrow \text{Type}) (\varphi : \text{I}) (u_0 : A \text{i}0) \rightarrow A \text{i}1$$

$$\text{hcomp} : \{A : \text{Type}\} \{\varphi : \text{I}\} (u : (i : \text{I}) \rightarrow \text{Partial } \varphi A) (u_0 : A) \rightarrow A$$

We now explain the transp (Section 5.1) and hcomp (Section 5.2) operations and how Agda --bridges extend these. The exact equations can be consulted in our implementation. Further details about transp, hcomp can be found in [Vezzosi et al. 2021]. This section ends with a brief comparison between the Kan operations implemented by Agda --bridges and those specified by the CH theory.

## 5.1 Transport

The transp operation provides a way to coerce elements of a type into elements of a path-equal type. Indeed, given $AA : A_0 \equiv_{\text{Type}} A_1$ we obtain transp $(\lambda i, AA \text{i}) \text{i}0 : A_0 \rightarrow A_1$. This map can in turn be upgraded into an equivalence and thus transp can be used to validate one direction of the univalence equivalence $A_0 \equiv A_1 \rightarrow A_0 \simeq A_1$.

Regarding the $\varphi : \text{I}$ argument of transp, we merely indicate that it controls where the resulting coercion function is definitionally the identity. In other words, transp $A \text{i}1 u_0$ reduces to $u_0$ (a typechecking side condition asks that $A$ is constant when $\varphi = \text{i}1$). 'Normal' transport is recovered by setting $\varphi = \text{i}0$ as illustrated above.

As explained before, the transp primitive reduces by induction on the formation of the line $A$, that is, a clause describing how transp reduces is specified when $A$ is a line of $\Pi$-types, $\Sigma$-types, data types, record types, etc. Compared to --cubical, Agda --bridges implements two additional clauses for transp, handling lines of BridgeP and Gel types. For Gel, we indicate that the clause uses capturing (see Definition 2.2). We provide some details regarding the clause for BridgeP since it requires a generalized hcomp operation called mhcomp in Agda --bridges and explained hereafter.

*Transporting bridges.* Assume $A : \text{I} \rightarrow (@x : \text{BI}) \rightarrow \text{Type}$ and $a_i : (i : \text{I}) \rightarrow A \text{i} \text{bic}$. The Agda --bridges implementation adds a clause for transp specifying how the following term should reduce transp $(i, \text{BridgeP}_{x, A \text{i}x} (a_0 \text{i}) (a_1 \text{i})) (\varphi : \text{I}) u_0$. This term can be represented as the dotted line in the following diagram.

$$\begin{array}{ccc} a_0 \text{i}1 & \longrightarrow & a_1 \text{i}1 \\ a_0 \uparrow & & a_1 \uparrow \\ a_0 \text{i}0 & \xrightarrow{u_0} & a_1 \text{i}0 \end{array}$$

Setting the result of this reduction to be the bridge $\lambda(x : \text{BI})$, transp $(i, A \text{i}x) \varphi (u_0 x)$ does not work. Indeed the latter term does not have the required endpoints $a_0 \text{i}1, a_1 \text{i}1$ definitionally.

A second idea is to use the hcomp primitive (its type appears above) of --cubical, which is used to reduce transp along lines of path types. In general, the sole purpose of hcomp is to allow terms to be

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.