Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:31

$$\left\{ \begin{array}{l l} \mathsf {i f} (z, A, t _ {0}, t _ {1}, b) & \mathsf {p r f} = \iota_ {1} (z) \\ \downarrow_ {A (b)} \mathsf {i f} (\lambda v. A (\uparrow v). \mathsf {c o d e}, \downarrow t _ {0}, \downarrow t _ {1}, e) & \mathsf {p r f} = \iota_ {2} (\iota_ {1} (e, -)) \\ \mathsf {r e c} _ {2} (b _ {0}; t _ {0}; t _ {1}) & \mathsf {p r f} = \iota_ {2} (\iota_ {2} (b _ {0}, -)) \end{array} \right.$$

In this definition, three different incarnations of the elimination rule for booleans are used. The first branch deals uses if $$(z,\ldots)$$ which is the elimination rule from the syntactic model, the second uses the neutral form if associated to if, and the third is the “ordinary” elimination principle for booleans available within the model.

**Lemma 5.10.** $$(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$$ is closed under intensional identity types and the relevant constants lie over their counterparts in $$(\mathsf{Ty}_m, \mathsf{Tm}_m)$$.

*Proof.* We must implement the following constants:

$$\begin{array}{l} \mathsf {I d} ^ {*}: (A: \mathsf {T y} _ {m} ^ {*}) (a _ {0}, a _ {1}: \mathsf {T m} _ {m} ^ {*} (A)) \\ \rightarrow \left\{\mathsf {T y} _ {m} ^ {*} \mid z: \mathbf {s y n} \mapsto \mathsf {I d} (z, A, a _ {0}, a _ {1}) \right\} \\ \operatorname {r e f l} ^ {*}: (A: \mathsf {T y} _ {m} ^ {*}) (a: \mathsf {T m} _ {m} ^ {*} (A)) \\ \rightarrow \left\{\mathsf {T m} _ {m} ^ {*} (\mathsf {I d} ^ {*} (A, a, a)) \mid z: \mathbf {s y n} \mapsto \operatorname {r e f l} (z, A, a) \right\} \\ \mathsf {J} ^ {*}: (A: \mathsf {T y} _ {m} ^ {*}) \\ \rightarrow (B: (a _ {0}, a _ {1}: \mathsf {T m} _ {m} ^ {*} (A)) \rightarrow \mathsf {T m} _ {m} ^ {*} (\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1})) \rightarrow \mathsf {T y} _ {m} ^ {*}) \\ \rightarrow (b: (a: \mathsf {T m} _ {m} ^ {*} (A)) \rightarrow \mathsf {T m} _ {m} ^ {*} (B (a, a, \operatorname {r e f l} (a)))) \\ \rightarrow (a _ {0}, a _ {1}: \mathsf {T m} _ {m} ^ {*} (A)) (p: \mathsf {T m} _ {m} ^ {*} (\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1}))) \\ \rightarrow \left\{\mathsf {T m} _ {m} ^ {*} (B (a _ {0}, a _ {1}, p)) \mid z: \mathbf {s y n} \mapsto \mathsf {J} (z, B, b, p) \right\} \\ \_ : (A: \mathsf {T y} _ {m} ^ {*}) \\ \rightarrow (B: (a _ {0}, a _ {1}: \mathsf {T m} _ {m} ^ {*} (A)) \rightarrow \mathsf {T m} _ {m} ^ {*} (\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1})) \rightarrow \mathsf {T y} _ {m} ^ {*}) \\ \rightarrow (b: (a: \mathsf {T m} _ {m} ^ {*} (A)) \rightarrow \mathsf {T m} _ {m} ^ {*} (B (a, a, \operatorname {r e f l} (a)))) \\ \rightarrow (a: \mathsf {T m} _ {m} ^ {*} (A)) \rightarrow \mathsf {J} ^ {*} (A, B, b, \operatorname {r e f l} ^ {*} (a)) = b (a) \\ \end{array}$$

Fix $$A: \mathsf{Ty}_m^*$$ and $$a_0, a_1: \mathsf{Tm}_m^*(A)$$. Just as with the normalization structure for booleans, we begin by defining $$\Phi$$ by realignment:

$$\mathbf {r e c o r d} \Phi : \left\{\mathrm{U} _ {1} \mid z: \mathbf {s y n} \mapsto \mathsf {T m} _ {m} (z, \mathsf {I d} (A, a _ {0}, a _ {1})) \right\} \mathbf {w h e r e}$$

$$\mathsf {t m}: \mathsf {N f} _ {m} (\mathsf {I d} (A, a _ {0}, a _ {1}))$$

$$\mathsf {p r f}: \bullet \left( \begin{array}{l} \sum_ {e: \mathsf {N e} _ {m} (\mathsf {I d} (A, a _ {0}, a _ {1}))} \mathsf {t m} = \mathbf {u p} (e) \\ + \sum_ {a: A. \mathsf {p r e d}} a _ {0} = a _ {1} \times \mathsf {t m} = \mathsf {r e f l} (\downarrow_ {A} a) \end{array} \right)$$

We now define $$\mathsf{Id}^*$$:

$$\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1}). \mathsf {c o d e} = \mathsf {I d} _ {\mathsf {c o d e} A} (\downarrow_ {A} a _ {0}, \downarrow_ {A} a _ {1})$$

$$\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1}). \mathsf {p r e d} = \Phi$$

$$\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1}). \mathsf {r e f l e c t} = \lambda e. \langle \mathbf {u p} (e), \eta (\iota_ {1} (e, \star)) \rangle$$

$$\mathsf {I d} ^ {*} (A, a _ {0}, a _ {1}). \mathsf {r e i f y} = \lambda p. p. \mathsf {t m}$$

We define reflexivity by $$\mathsf{refl}^* = \langle \mathsf{refl}, \eta(\iota_2(\star, \star, \star)) \rangle$$. Finally, the elimination principle is defined using the induction principle for $$\bullet X$$.

$$\mathsf {J} ^ {*} (B, b, a _ {0}, a _ {1}, p = \langle \mathsf {t m}, \mathsf {p r f} \rangle) =$$