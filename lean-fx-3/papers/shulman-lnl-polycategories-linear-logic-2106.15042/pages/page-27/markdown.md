Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:27

|  Subterminal S | Universal properties | Equivalent structure  |
| --- | --- | --- |
|  LNLPOLY | \( \times, 1, \rightarrow, \otimes, \mathbb{1}, (\cdot)^{*}, F, U \) | *-autonomous closed LNL adjunction  |
|  LNLMULTI | \( \times, 1, \rightarrow, \otimes, \mathbb{1}, \multimap, F, U \) | closed LNL adjunction  |
|  SYMPOLY | \( \otimes, \mathbb{1}, (\cdot)^{*} \) | *-autonomous category  |
|  SYMMULTI | \( \otimes, \mathbb{1}, \multimap \) | closed symmetric monoidal category  |
|  CARTMULTI | \( \times, 1, \rightarrow \) | cartesian closed category  |
|  CBPV | \( \times, 1, \rightarrow, \multimap, \multimap, \times, \mathbb{1}^{\dagger}, F^{\dagger}, U \) | structure of Corollary 3.14  |

\( ^{\dagger} \)  with restricted universal property.

TABLE 2. Bifibrations over subterminals

Following [LSR17, BZ20], we define:

Definition 4.11. A functor \(\pi : \mathcal{P} \to \mathcal{Q}\) is a bifibration if for any list \(\Phi\) of signed objects in \(\mathcal{P}\) and any morphism \(g \in \mathcal{Q}(\pi \Phi, L)\) there exists a \(\pi\)-cartesian morphism \(f \in \mathcal{P}(\Phi, K)\) such that \(\pi(f) = g\).

When \(\mathcal{Q}\) is one of our distinguished subterminal objects (including the terminal object LNLPOLY), bifibrations \(\pi : \mathcal{P} \to \mathcal{Q}\) reduce to more familiar structures:

Theorem 4.12. For each row in Table 2, with subterminal object S listed in the first column, the following structures are equivalent:

(i) A bifibration \(\pi : \mathcal{P} \to \mathcal{S}\).
(ii) An object of LNLPoly/S with the universal properties in the second column.
(iii) The categorical structure indicated in the third column.

Proof. Clearly (i)⇒(ii), while (ii)⇔(iii) follows from Section 3. The remaining direction (ii)⇒(i) is similar to the universal characterization of *-autonomous categories in [BZ20]. By ×Θ, ⊗Γ, or ∂Δ we mean the result of combining all the objects in a list with the given binary operation; if the list contains only one object the result is that object (in which case the binary operation doesn't even need to exist), while if the list is empty the result is the corresponding nullary operation 1, 1, or ⊥. Now we construct the five possible types of morphism universal in X or A as follows:

- For \(\psi \in \mathcal{P}(\Theta ;X)\) we take \(X = \times \Theta\).
- For \(\psi \in \mathcal{P}(\Theta, X; Y)\) we take \(X = \times \Theta \to Y\).
- For \(\psi \in \mathcal{P}(\Theta, X \mid \Gamma; \Delta)\) we take \(X = \times \Theta \to (\bigotimes \Gamma \to \mathcal{X} \Delta)\).
- For \(\psi \in \mathcal{P}(\Theta \mid \Gamma ;\Delta ,A)\) we take \(A = \times \Theta \rtimes \bigotimes (\Gamma ,\Delta^{*})\)
- For \(\psi \in \mathcal{P}(\Theta \mid \Gamma, A; \Delta)\) we take \(A = \times \Theta \to \mathcal{X}(\Gamma^{*}, \Delta)\).

We leave it to the reader to check that whenever a particular type of universal morphism exists in one of our subterminals S, the requisite universal operations are among those assumed by (ii) or can be constructed from them. (When S = CBPV, we discussed the restricted universal property of F in Example 4.7.)

Definition 4.13. If Q is a fixed object such as those in Table 2 (or more generally Table 3), we refer to an object  \( P \in LNLPoly/Q \)  as birepresentable if the map  \( \pi : P \to Q \)  is a bifibration.