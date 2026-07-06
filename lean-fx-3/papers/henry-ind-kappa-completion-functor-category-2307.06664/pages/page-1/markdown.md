arXiv:2307.06664v2 [math.CT] 9 Oct 2024

# When does \(\mathrm{Ind}_{\kappa}(C^I)\simeq \mathrm{Ind}_{\kappa}(C)^I?\)

Simon Henry

## Abstract

We investigate under which condition the  \( \kappa \) -ind completion of a functor category  \( C^{I} \)  is equivalent to the category of functors from I to the  \( \kappa \) -ind completion of C. A published theorem implies this is true for any Cauchy complete category C and  \( \kappa \) -small category I, but we show this is not the case in general. We prove two results that seem to cover all applications of this incorrect theorem we could find in the literature: The result holds if C has  \( \kappa \) -small colimits and I is  \( \kappa \) -small, or if C is an arbitrary category and I is well-founded and  \( \kappa \) -small. In both cases, we show that the conditions are optimal in the sense that the result holds for all C if and only if I satisfies the given assumption.

## Contents

1 Introduction 1
2 Proof of Theorem 1.2. 4

2.1 Proof of (L1) or (L2) \(\Rightarrow\) (L3) 6
2.2 Proof of (L3) \(\Rightarrow\) (L1) 7

3 Proof of Theorem 1.3. 8

3.1 Well-founded categories 8
3.2 Proof of (A2) \(\Rightarrow\) (A4) 11
3.3 Proof of (A4) \(\Rightarrow\) (A1) 12

## 1 Introduction

Given \(\kappa\) a regular cardinal and \(C\) a category we denote by \(\mathrm{Ind}_{\kappa}(\mathcal{C})\) the \(\kappa\)-ind completion of \(\mathcal{C}\), that is the pseudo-initial object in the locally full subcategory of \(\mathcal{C} \backslash \mathbf{Cat}\) whose objects have \(\kappa\)-filtered colimits and morphisms are functors preserving these \(\kappa\)-filtered colimits. \(\mathrm{Ind}_{\kappa}(\mathcal{C})\) can be explicitly described as the full subcategory of the presheaf category \(\mathbf{Sets}^{\mathcal{C}^{\mathrm{op}}}\) of functors that are small \(\kappa\)-directed colimits of representables. If \(\mathcal{C}\) is small this is also equivalent to the category of \(\kappa\)-flat functors \(\mathcal{C}^{\mathrm{op}} \to \mathbf{Sets}\).

The construction \(\mathrm{Ind}_{\kappa}\) is a covariant endofunctor functor of the bicategory of locally small categories. In particular, for each \(i\in I\) the evaluation functor \(ev_{c}:\mathcal{C}^{I}\to \mathcal{C}\), induces a functor preserving \(\kappa\)-filtered colimits \(\mathrm{Ind}_{\kappa}(C^{I})\to \mathrm{Ind}_{\kappa}(C)\), which together induce a functor:

2020 Mathematics Subject Classification. 18A25, 18C35

email: shenry2@uottawa.ca

1