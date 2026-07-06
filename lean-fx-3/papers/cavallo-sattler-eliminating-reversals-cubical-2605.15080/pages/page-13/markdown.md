E. Cavallo and C. Sattler

13

In a self-dual interval theory \((\Phi, \phi)\), the value of \(\phi\) at an operator \(\mathbf{r}: \mathbb{I}^n \to \mathbb{I}\) in \(\Phi\) is an expression \(\phi(\mathbf{r}): \mathbb{I}^n \to \mathbb{I}\) over \(\Phi\): the dual of \(\mathbf{r}\).

▶ Example 24. The cartesian theory  \( \Phi_{cart} \)  is self-dual with the trivial isomorphism  \( 1 \cong 1 \) . The theory  \( \Phi_{DL} \)  is self-dual with  \( \phi \)  defined by  \( \phi(-\wedge -)(i,j) = i \vee j \)  and vice versa.

▶ Definition 25. Given a self-dual interval theory ( \( \Phi, \phi \) ), its extension by a reversal  \( Rev_{\phi}\Phi \in INT \)  is the extension of  \( \Phi \)  with

(a) an operator  \( \neg: I \rightarrow I \) ,
(b) equations  \( \neg0\equiv1:\mathbb{I},\neg1\equiv0:\mathbb{I}, \)  and  \( (\mathbf{i}:\mathbb{I})\to\neg(\neg(\mathbf{i}))\equiv\mathbf{i}:\mathbb{I}, \)  and
(c) for each \(\mathbf{r}:(\mathbf{i}_1:\mathbb{I},\ldots ,\mathbf{i}_n:\mathbb{I})\to \mathbb{I}\) in \(\Phi\) , an equation

\[
(\mathbf {i} _ {1}: \mathbb {I}, \dots , \mathbf {i} _ {n}: \mathbb {I}) \rightarrow \neg (\mathbf {r} (\mathbf {i} _ {1}, \dots , \mathbf {i} _ {n})) \equiv \phi (\mathbf {r}) (\neg (\mathbf {i} _ {1}), \dots , \neg (\mathbf {i} _ {n})): \mathbb {I}.
\]

▶ Example 26. The interval theory  \( Rev_{\phi}\Phi_{cart} \)  for  \( \phi:1\cong1 \)  consists simply of the operator  \( \neg:I\to I \)  and equations  \( \neg0\equiv1:I,\neg1\equiv0:I \) , and  \( (\mathbf{i}:\mathbb{I})\to\neg(\neg(\mathbf{i}))\equiv\mathbf{i}:\mathbb{I} \) . The interval theory  \( Rev_{\phi}\Phi_{DL} \) , for the isomorphism  \( \phi:\Phi_{DL}\cong\Phi_{DL} \)  from Example 24, is the algebraic theory of a De Morgan algebra bounded by 0 and 1.
▶ Definition 27 (Twist interpretation of the interval). For a self-dual interval theory  \( (\Phi, \phi) \) , we define a representable map functor  \( T: \mathbb{INT}[\mathrm{Rev}_{\phi}\Phi] \to \mathbb{INT}[\Phi] \)  by the following interpretation:

1. On sorts, we set  \( T\mathbb{I} := I \times I \) .

2. We interpret 0 as (0,1) and 1 as (1,0).

3. We interpret each \(\mathbf{r}:(\mathbf{i}_1:\mathbb{I},\ldots ,\mathbf{i}_n:\mathbb{I})\to \mathbb{I}\) in \(\Phi\) by

\[
\operatorname{Tr} \left(\left(\mathrm{i} _ {1 0}, \mathrm{i} _ {1 1}\right), \dots , \left(\mathrm{i} _ {n 0}, \mathrm{i} _ {n 1}\right)\right) := \left(\mathbf {r} \left(\mathrm{i} _ {1 0}, \dots , \mathrm{i} _ {n 0}\right), \phi (\mathbf {r}) \left(\mathrm{i} _ {1 1}, \dots , \mathrm{i} _ {n 1}\right)\right).
\]

4. We interpret  \( \neg \)  by  \( \mathrm{T}\neg((\mathbf{i}_{0},\mathbf{i}_{1})) := (\mathbf{i}_{1},\mathbf{i}_{0}) \) .

### 4.2 Interpreting cubical type theory

Cubical type theory being an extension of the theory of an interval, any environment  \( \Phi \)  over INT can also be regarded as an environment  \( \iota\Phi \)  over CTT, from which we can produce a new SOGAT CTT[ \( \iota\Phi \) ]: cubical type theory with the interval theory  \( \Phi \) .

We now extend T:  \( \mathbb{INT}[\mathrm{Rev}_{\phi}\Phi] \to \mathbb{INT}[\Phi] \)  for a self-dual interval theory  \( (\Phi,\phi) \)  to an interpretation T:  \( \mathbb{CTT}[\iota\mathrm{Rev}_{\phi}\Phi] \to \mathbb{CTT}[\iota\Phi] \) . The specification of this interpretation occupies the remainder of this section; we summarize in Theorem 42.

▶ Component 28 (T, sorts). We set Tl := I × I and interpret all other sorts by themselves: TTy := Ty, (TTm)(A) := Tm(A), TCof := Cof, (TTrue)(P) := True(P).
▶ Notation 29. For infix operators, we use a subscript to denote interpretation, for example writing  \( \approx_{T} \)  instead of  \( T(-\approx-) \) .
▶ Component 30 (T, interval theory). We interpret the operations of  \( Rev_{\phi}\Phi \)  in  \( CTT[\iota\Phi] \)  as in Definition 27.
▶ Component 31 (T, cofibration theory). We interpret the cofibration-forming operations as follows.

\[
\left(\mathbf {i} _ {0}, \mathbf {i} _ {1}\right) \approx_ {\mathrm{T}} \left(\mathbf {j} _ {0}, \mathbf {j} _ {1}\right) := \left(\mathbf {i} _ {0} \approx \mathbf {j} _ {0}\right) \cap \left(\mathbf {i} _ {1} \approx \mathbf {j} _ {1}\right)
\]

\[
\mathrm{T} \top := \top
\]

\[
\mathrm{P} \cap_ {\mathrm{T}} \mathrm{Q} := \mathrm{P} \cap \mathrm{Q}
\]

\[
\mathrm{T} \bot := \bot
\]

\[
\mathrm{P} \cup_ {\mathrm{T}} \mathrm{Q} := \mathrm{P} \cup \mathrm{Q}
\]

These definitions validate the associated axioms for the True judgment. We interpret the  \( elim_{\perp}^{Ty} \) ,  \( elim_{\perp}^{Tm} \) ,  \( elim_{\cup}^{Ty} \) , and  \( elim_{\cup}^{Tm} \)  eliminators as themselves.