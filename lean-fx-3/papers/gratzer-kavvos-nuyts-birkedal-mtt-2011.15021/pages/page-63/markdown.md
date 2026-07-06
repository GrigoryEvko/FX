Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:63

**Towards an Implementation of MTT.** A major point of future work is the development of an implementation of MTT. Substantial preliminary implementation efforts are already underway with Menkar [Nuy19]. In addition to the engineering effort, a systematic account for an algorithmic syntax of MTT as well as proof of normalization is needed. We believe that the general ideas of [GSB19a] are applicable to this situation and there is ongoing work to apply them to MTT through more modern *gluing* techniques [Coq19]. Eventually, this work should prove that $\Gamma \vdash M = N : A \oplus m$ and $\Gamma \vdash A = B \text{ type}_\ell \oplus m$ are decidable relative to a decision procedure for equality in the underlying mode theory.

**Left Adjoints.** As discussed in Section 11.4, MTT trades a measure of generality for a degree of simplicity, as compared to LSR. One might hope, however, that it would be possible to include a connective for *left adjoints*, as well as the current connective which models right adjoints without losing all of this simplicity. It is not obvious that this can be done without significantly changing MTT: the introduction rule for modalities is exceptionally specific to a right adjoint. This additionally flexibility would allow us to model several modalities which are currently out of reach. For instance, when modeling a string of adjoints, we always fail to model the final left adjoint. Concretely speaking, the inclusion of left adjoints would allow MTT to model computational effects [Mog91, Lev12], as we will be able to internally recover the corresponding monad as the composite of the two parts of an adjoint pair.

**Acknowledgements.** We are grateful for productive conversations with Carlo Angiuli, Dominique Devriese, Adrien Guatto, Magnus Baunsgaard Kristensen, Daniel Licata, Rasmus Ejlers Møgelberg, Matthieu Sozeau, Jonathan Sterling, and Andrea Vezzosi.

Alex Kavvos was supported in part by a research grant (12386, Guarded Homotopy Type Theory) from the VILLUM Foundation. Andreas Nuyts was supported by a PhD Fellowship from the Research Foundation - Flanders (FWO) at imec-DistriNet, KU Leuven. This work was supported in part by a Villum Investigator grant (no. 25804), Center for Basic Research in Program Verification (CPV), from the VILLUM Foundation.

# REFERENCES

[Abe06] Andreas Abel. *A Polymorphic Lambda-Calculus with Sized Higher-Order Types*. PhD thesis, Ludwig-Maximilians-Universität München, 2006.
[Abe08] Andreas Abel. Polarised subtyping for sized types. *Mathematical Structures in Computer Science*, 18(5):797–822, 2008.
[AK16] Thorsten Altenkirch and Ambrus Kaposi. Normalisation by Evaluation for Dependent Types. In Delia Kesner and Brigitte Pientka, editors, *1st International Conference on Formal Structures for Computation and Deduction (FSCD 2016)*, volume 52 of *Leibniz International Proceedings in Informatics (LIPIcs)*, pages 6:1–6:16, Dagstuhl, Germany, 2016. Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik.
[AM13] Robert Atkey and Conor McBride. Productive Coprogramming with Guarded Recursion. In *Proceedings of the 18th ACM SIGPLAN International Conference on Functional Programming*, ICFP '13, pages 197–208. Association for Computing Machinery, 2013.
[And92] Jean-Marc Andreoli. Logic Programming with Focusing Proofs in Linear Logic. *Journal of Logic and Computation*, 2(3):297–347, 06 1992.
[AS12] Andreas Abel and Gabriel Scherer. On Irrelevance and Algorithmic Equality in Predicative Type Theory. *Logical Methods in Computer Science*, 8(1), 2012.
[Awo10] Steve Awodey. *Category Theory*. Oxford Logic Guides. Oxford University Press, 2010.
[Awo18] Steve Awodey. Natural models of homotopy type theory. *Mathematical Structures in Computer Science*, 28(2):241–286, 2018.