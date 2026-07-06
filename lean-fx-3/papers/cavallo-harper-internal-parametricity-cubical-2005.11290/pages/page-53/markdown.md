Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:53

The formalism we develop in Section 5 must be supported by metatheoretic results such as normalization in order to be truly utile. We have implemented an experimental type-checker for (non-cubical) parametric type theory, **ptt**, based on *normalization by evaluation*; in theory, this implementation implicitly contains a proof of normalization for the Section 5 formalism. However, we have not attempted to extract such a proof, nor have we verified the algorithm's correctness. The current **ptt** theory is also somewhat weaker than that of Section 5: we found it more convenient to give the Gel type a positive eliminator rather than a projection with $\eta$-principle. The $\eta$-expansion rule we have used in this paper applies only to terms that can be put in the form $Q[r/x]$, a condition that is to our knowledge expensive and painful (though we believe possible) to check.

#### ACKNOWLEDGMENTS

We thank Carlo Angiuli, Steve Awodey, Daniel Gratzer, Kuen-Bang Hou (Favonia), Dan Licata, Anders Mörtberg, Emily Riehl, Christian Sattler, Michael Shulman, Jonathan Sterling, and Andrew Swan for many helpful discussions.