2. An (trivial) cofibration if it is a (trivial) Reedy cofibration.
3. An (trivial) fibration if it is a (trivial) Reedy fibration.

Remark C.12. When the Reedy category is directed, this model structure coincides with the projective weak model structure. It is straightforward to define this last weak model category. In this weak model, the weak equivalences and the fibrations are the level-wise weak equivalences and fibrations respectively. Similarly, when the Reedy category is an inverse category, then the Reedy weak model structure is Quillen equivalent to the injective model structure. In this other case, weak equivalences and cofibrations are given level-wise.

We now prove the theorem:

Lemma C.13. Let I be a direct category and X : I → M be a diagram. Let U ⊂ V ⊂ I be two sieves of I, such that V - U has a finite number of objects. Assume that the colimit

$$X(U) := \text{Colim}_{u \in U} X(u)$$

exists and is cofibrant, and that for each v ∈ V - U, the latching object L_v X exists and is cofibrant, and the map L_v X → X(v) is a cofibration. Then X(V) exists and the comparison map X(U) → X(V) is a cofibration. If L_v X → X(v) is actually a trivial cofibration for every v ∈ V - U, then X(U) → X(V) is a trivial cofibration.

Proof. This is immediate by induction on the number of objects of V - U. If it only has one object, then X(U) → X(V) can be seen to be a pushout of the core cofibration L_v X → X_v to the cofibrant object X(U). If V - U has several objects, we iterate this process once for each object of V - U. □

Corollary C.14. Let R be a locally finite Reedy category, X : R → M be a diagram and let k ∈ R an object. Assume that X is Reedy cofibrant at every r such that deg(r) < deg(k), then the latching object L_k(X) exists and is cofibrant.

Proof. Using a proof by induction on deg(x), we can freely assume that all the latching object L_r(X) are cofibrant for all r such that deg(r) < deg(x). We can then just apply the theorem C.13 to the finite direct category I = R⁺/x and U = ∅, V = I. □

That is subcategories with the property that if there is an arrow x → x' and x' ∈ V then x ∈ V.

150