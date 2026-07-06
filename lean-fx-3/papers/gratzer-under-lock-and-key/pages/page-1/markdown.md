# Under Lock and Key:
A Proof System for a Multimodal Logic

G. A. Kavvos Daniel Gratzer

Tuesday 8th November, 2022

1. INTRODUCTION

Many-dimensional [Gab+03], multimodal [CP08] or poly-modal [Ben10] have found a number of successful applications. To name but a few:

|  temporal logic | **F**φ, **G**φ, **X**φ | [DGL16]  |
| --- | --- | --- |
|  epistemic logic | *K*ιφ, *B*ιφ, *C*Γφ | [Fag+95]  |
|  dynamic logic | [a]φ, ⟨a⟩φ | [HKT00]  |
|  dynamic epistemic logic | *K*ιφ, [α]φ | [DHK08]  |
|  Hennessy-Milner logic | [α]φ, ⟨α⟩φ | [Sti01]  |

The majority of work on the aforementioned logics has a number of common features:

- **The propositional substrate is almost always classical.** While a classical approach is more than sufficient for modelling knowledge and computational systems, it precludes the making of a close connection with categorical logic, where the *internal language* of many categories is intuitionistic [Pit01].
- **The modal fragment is almost always inspired by a Kripke semantics, and lacks a proof system.** The Kripke semantics usually model some intensional aspect of interest, such as states of knowledge, the execution trace of a machine, and so on. While this is indeed more than adequate for modelling purposes, it precludes the immediate formulation of a well-behaved, computational theory for these logics under the Curry-Howard correspondence [GLT89; SU06].
- **There is no cohesive, unifying account.** While there have been a few attempts at building a framework [CP08, §8], as well as a host of results on combining simpler modal logics using *product* and *fusion* operators [Gab+03, §§3–4], we have yet to obtain a unifying account of logics with multiple interacting modalities.

In this paper we present a new modal logic. Unlike previous work, this logic fixes neither the number nor the interactions of modalities in advance. Instead, it is given

1