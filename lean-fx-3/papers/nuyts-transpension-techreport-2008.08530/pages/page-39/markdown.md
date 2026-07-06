Example 4.4.8 (Affine cubes). We instantiate theorem 4.4.7 for the multiplier \(\sqcup * \mathbb{I} : \square^k \to \square^k\) (example 3.3.3). There, \(\partial \mathbb{I}\) is essentially the constant presheaf with \(k\) elements. So \(b_{\partial}\) determines the images of the \(k\) poles of the transpension type. The term \(b\) determines the action on paths (for \(k = 2\), for general \(k\) perhaps 'webs' is a better term), and the paths/webs of the transpension type are essentially the elements of \(A\). The coherence condition says that the image of such paths/webs should always have the endpoints given by \(b_{\partial}\).

Example 4.4.9 (Clocks). We instantiate theorem 4.4.7 for the multiplier \(\sqcup * (i : \odot_k)\) (example 3.3.6), where we adapt the base category to forbid diagonals: a morphism may use every variable of its domain at most once. The boundary \(\partial(i : \odot_k)\) is isomorphic to \(\mathbf{y}(i : \odot_{k-1})\) if \(k > 0\) and to the empty presheaf \(\bot\) if \(k = 0\). So if we want to eliminate an element of the transpension type over \(\mathbf{y}(i : \odot_k)\), which means we have a clock and we don't care about what happens if the time exceeds \(k\), then we need to handle two cases. The first case \(b_{\partial}\) says what happens if we don't even care what happens at timestamp \(k\); in which case the transpension type trivializes. Then, by giving \(b\), we say what happens at timestamp \(k\) and need to make sure that this is consistent with \(b_{\partial}\). The elements of the transpension type at timestamp \(k\) are essentially the elements of \(A\), which are fresh for the clock.

Example 4.4.10 (Embargoes). Recall that the multiplier \(\sqcup \ltimes \mathbf{!}\) sends \(W \in \mathcal{W}\) to \((W, \top) \in \mathcal{W} \times \uparrow\), the Yoneda-embedding of which represents the arrow \(\mathbf{y}W \to \mathbf{y}W\), i.e. \(\mathbf{y}W \mathbf{!}, \top\) under the convention that \(\Psi \mathbf{!}, \Theta\) denotes \((\Psi, \Theta \to \Psi)\). Its left lifting is \(\sqcup \ltimes \mathbf{y} \mathbf{!}: \widehat{\mathcal{W}} \to \widehat{\mathcal{W} \times \uparrow}\), and \(\mathbf{y} \mathbf{!}\) is the terminal object, so that \(\widehat{\mathcal{W} \times \uparrow} / \mathbf{y} \mathbf{!} \cong \widehat{\mathcal{W} \times \uparrow}\). We get 5 adjoint functors, of which we give here the action up to isomorphism:

\[
\begin{array}{c c c c c c c} & & & \Psi & \mapsto & (\bot \to \Psi), \\ & & \exists_ {\mathbf {y} \mathbf {!}} & : & \Psi & \leftrightarrow & (\Psi . \Theta \to \Psi), \\ \sqcup \ltimes \mathbf {y} \mathbf {!} & \text {or} & \exists_ {\mathbf {y} \mathbf {!}} & : & \Psi & \mapsto & (\Psi \to \Psi), \\ \mathbf {y} \mathbf {!} \multimap \sqcup & \text {or} & \forall_ {\mathbf {y} \mathbf {!}} & : & \Psi . \Theta & \leftrightarrow & (\Psi . \Theta \to \Psi), \\ \mathbf {y} \mathbf {!} \vee \sqcup & \text {or} & \Diamond_ {\mathbf {y} \mathbf {!}} & : & \Psi & \mapsto & (\Psi \to \top). \end{array}
\]

The boundary of  \( y! \)  is  \( \partial! \cong y(\top, \bot) \)  which is isomorphic to the arrow  \( \bot \to \top \) . Thus, we see:

\( \exists_{y!} \)  If, for some unknown embargo, we have information partly under that embargo, then we can only extract the unembargoed information,

\( \perp_{y!} \)  If information is fresh for an embargo, then it is unembargoed,

\( \forall_{y!} \)  If, for any embargo, we have information partly under that embargo, then we can extract the information,

\( \Diamond_{y!} \)  If information is transpended over an embargo, then it is completely embargoed.

Perhaps the above is more intuitive if we think of an embargo as a key or a password.

So let us now instantiate theorem 4.4.7, which allows us to eliminate an element of the transpension type, i.e. essentially an element of \( A \to \top \). The boundary case exists over the boundary \( \bot \to \top \) and allows us to consider only the codomain of the arrow, i.e. the part of the context before the embargo, where the transpension type is trivial. The case \( b \) then requires us to say how to act on embargoed data in a coherent way with what we already specified in \( b_{\partial} \). The embargoed data is essentially an element of \( A \), which comes from the mode where the embargo does not apply.

## 5 Prior modalities

Many modalities arise as central or right liftings of functors between base categories [NVD17, ND18, Nuy18, BM20]. The following definition allows us to use such modalities even when part of the context is in front of a pipe.

Definition 5.0.1. A functor \( G: \mathcal{W} \to \mathcal{W}' \) yields a functor \( G'^{\Psi}: \mathcal{W}/\Psi \to \mathcal{W}'/G_{!}\Psi : (W, \psi) \mapsto (GW, G_{!}\psi) \). This in turn yields three adjoint functors between presheaf categories:

\[
G _ {!} ^ {\Psi !} \dashv G ^ {\Psi ! *} \dashv G _ {*} ^ {\Psi !}. \tag {49}
\]

39