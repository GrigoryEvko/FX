10 Introduction

We are naturally led, then, to search for a computational interpretation that *does* allow equality proofs to carry data, what we will call *contentful equality*. (Effectivity of quotients is not the sole reason to do so, not by a long shot, but is a convenient potted motivation for the purposes of this thesis.) We take inspiration and intuition from two phenomena: the informal treatment of isomorphisms as equalities in everyday mathematics, and the notion of *path* in topology and homotopy theory.

**Isomorphism as equality** We look to *isomorphism* as an example of a contentful relation that is often treated like equality on an informal level. For an illustrative example, we draw from group theory, the study of sets equipped with binary operations and satisfying certain axioms we will not enumerate. One example of a group is the set of real numbers with the operation of addition: $(\mathbb{R}, +)$. Another is the set of positive real numbers with the operation of multiplication: $(\mathbb{R}_+, \cdot)$. These two groups are not *equal* in the standard sense, but they *are* isomorphic. That is, there are functions $\exp \in \mathbb{R} \rightarrow \mathbb{R}_+$ and $\ln \in \mathbb{R}_+ \rightarrow \mathbb{R}$ converting between the two sets that (1) are mutually inverse, meaning that $\ln(\exp(a)) = a$ and $\exp(\ln(b)) = b$, and (2) preserve the operations, meaning that $\exp(a + b) = \exp(a) \cdot \exp(b)$ and $\ln(a \cdot b) = \ln(a) + \ln(b)$. The existence of this isomorphism means that $(\mathbb{R}, +)$ and $(\mathbb{R}_+, \cdot)$ are *practically identical* from the perspective of group theory. Any “group-theoretic property” that holds of one will hold of the other. Unlike an actual equality, however, we cannot only remember that $(\mathbb{R}, +)$ and $(\mathbb{R}_+, \cdot)$ *are* isomorphic: we need to remember *how* they are isomorphic. As an example, consider the following true statement.

For every $a \in \mathbb{R}$, we have $a + 0 = a$. $\checkmark$

If $(\mathbb{R}, +)$ and $(\mathbb{R}_+, \cdot)$ were *equal*, we would be able to replace one with the other and get another true statement. But the following is clearly false!

For every $a \in \mathbb{R}_+$, we have $a \cdot 0 = a$. $\times$

To convert results between the two groups properly, we need to *transport* the constant 0 along the isomorphism $(\exp, \ln)$. In this case, we have $\exp(0) = 1$, so the result is the following true statement.

For every $a \in \mathbb{R}_+$, we have $a \cdot 1 = a$. $\checkmark$

Moreover, there actually *multiple* isomorphisms between $(\mathbb{R}, +)$ and $(\mathbb{R}_+, \cdot)$: a second sends $a \in \mathbb{R}$ to $1/\exp(a) \in \mathbb{R}_+$ and $b \in \mathbb{R}_+$ to $-\ln(b) \in \mathbb{R}$. Thus, $(\mathbb{R}, +)$ and $(\mathbb{R}_+, \cdot)$ are “equal” in (at least) two different ways. When we use the fact that they are “equal” to transport facts between them, we need to be consistent about which “equality” we are