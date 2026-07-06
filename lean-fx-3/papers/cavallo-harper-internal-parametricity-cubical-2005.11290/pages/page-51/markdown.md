Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:51

|  This paper | [BCM15] | [Mou16]  |
| --- | --- | --- |
|  \( Bridge_{x.A}(a_0, a_1) \) | \( A \ni_x a \) | \( (\forall x.A) \ni a \)  |
|  \( \lambda^I x.a \) | \( a \cdot x \) | \( (\langle x \rangle a)! \)  |
|  \( p@x \) | \( (a, x p) \) | \( (\langle a, x p \rangle) \)  |
|  \( extent_x(-; a_0.t_0, a_1.t_1, a_0.a_1.\overline{a}.u) \) | \( \langle \lambda a.t, x \lambda a.\lambda \overline{a}.u \rangle \) | \( (\langle \lambda a.t, x \lambda a.\lambda \overline{a}.u \rangle) \)  |
|  \( Gel_x(A_0, A_1, a_0.a_1.R) \) | \( (a : A) \times_x R \) | \( A \bowtie_x R \)  |
|  \( gel_x(a_0, a_1, c) \) | \( (a, x c) \) | \( (\langle a, x p \rangle) \)  |
|  \( ungel(x.a) \) | \( a \cdot x \) | \( (\langle x \rangle a)! \)  |

Figure 10: Translation dictionary for internal parametricity

the bridge interval. \( ^{3} \)  As our notation is quite different from that of Bernardy et al., we provide a comparison in Figure 10. Note that the mapping is not one-to-one because of the additional equations imposed in their theory. We also include notations from Moulin's thesis [Mou16]. In that work, the notion of a function  \( (i:\mathbb{I})\to A \)  without a fixed endpoint (called a "ray") is included separately from bridge types, and term formers that are primitive in [BCM15] are often implemented as combinations of terms relating first interval dependency to rays and then rays to bridges. In particular,  \( A\bowtie_{x}R \)  is syntactic sugar for a term  \( (A,\Psi_{A}R)\circledast x \) , while  \( (f,xh) \)  is sugar for  \( (f,\Phi_{f}h)\circledast x \) ; as a result, the equivalents of Gel and extent are sometimes called  \( \Psi- \)  and  \( \Phi \) -operators respectively in the literature.

A second approach to internal parametricity has been proposed by Nuyts, Vezzosi, and Devriese [NVD17]. Their system resembles our own in that it is based on bridges and paths, each of which is represented by a kind of map from an interval. Whereas our bridge and path structures are more-or-less orthogonal to each other, Nuyts et al. use a modality to connect the two. Terms are checked under different modalities depending on whether they are used in type or element positions, capturing the phase separation between type and element-level computation that is often identified as a consequence of parametricity. We see the two approaches of Bernardy et al. and Nuyts et al. as internalizing different perspectives on parametricity: the former internalizes the relational interpretation, while the latter internalizes this phase separation.

Nuyts et al. also distinguish between continuous and parametric function types: the former preserve paths and bridges, while the latter take bridges to paths. By contrast, we consider the former to already be “parametric”—as we have seen, one can prove parametricity theorems in our setting using only this property. However, the stronger condition does obviate the need to identify the class of bridge-discrete types as a replacement for the identity extension lemma. For example, any parametric function  \( U \rightarrow A \)  in their setting is constant, without any assumptions on A (cf. Lemma 3.18), because it takes the bridges in U to paths. Also notable is that their path and bridge intervals both behave structurally, whereas we use an affine interval for bridges. Given the other divergences from Bernardy et al.’s approach, it is difficult to say how the issues we raise with using structural variables for parametricity affect their system, if at all; it seems that they are ameliorated by the stronger condition on parametric functions. One notable limitation is that iterated parametricity is impossible, that is, the results produced by parametricity are not subject to further parametricity theorems.

\( ^{3} \) We conjecture that binary internal parametricity is more powerful than unary parametricity, but that ternary parametricity and so on provide no additional strength, because we can iterate binary parametricity to mimic  \( 2^{n} \) -ary parametricity for any n.