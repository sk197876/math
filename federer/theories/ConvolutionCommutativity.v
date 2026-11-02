(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Alternating.
From Federer Require Import Convolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.2: commutative coefficient multiplication gives graded
    anticommutativity, using the signed interchange of 1.3.3. *)
Section Anticommutativity.
Variable K : fieldType.
Variables X W : lmodType K.
Variable G : grading X.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Hypothesis hC : commutative mu.
Variables p q : nat.
Variables (a : Hom_m W G p) (b : Hom_m W G q).
(** Source for [paired_tensor_swap]: Federer (1969), 1.4.2, p. 18, second
    consequence of the diagonal properties. In words: Commutative
    coefficient multiplication gives graded anticommutative alternating
    multiplication. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma paired_tensor_swap x :
  paired_tensor hmu a b (graded_swap G G true x) =
    (-1 : K)^+(p*q) *: paired_tensor hmu b a x.
Proof.
elim/(tensor_homogeneous_induction (GA:=G) (GB:=G)): x => [|x y hx hy|c x hx|r s x y hx hy].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- rewrite (linZ (linearP (graded_swap G G true)) c x).
  rewrite (linZ (linearP (paired_tensor hmu a b)) c (graded_swap G G true x))
    (linZ (linearP (paired_tensor hmu b a)) c x) hx.
  by rewrite !scalerA mulrC.
- rewrite (graded_swapE true hx hy) linearZ !paired_tensorE.
  change ((-1 : K)^+(r*s) *: mu (a y) (b x) =
    (-1 : K)^+(p*q) *: mu (b x) (a y)).
  case hs: (s == p).
  + case hr: (r == q).
    * by rewrite (eqP hs) (eqP hr) mulnC hC.
    * rewrite (hom_m_degree b (negbT hr) hx) (bil0l hmu) (bil0r hmu).
      by rewrite !scaler0.
  + rewrite (hom_m_degree a (negbT hs) hy) (bil0l hmu) (bil0r hmu).
    by rewrite !scaler0.
Qed.
Variable D : {linear X -> tensor_space X X}.
Hypothesis hD : forall x, graded_swap G G true (D x) = D x.
(** Source for [convolution_anticommutative]: Federer (1969), 1.4.2, p. 18,
    second consequence of the diagonal properties. In words: Commutative
    coefficient multiplication gives graded anticommutative alternating
    multiplication. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma convolution_anticommutative x :
  convolution hmu D a b x = (-1 : K)^+(p*q) *: convolution hmu D b a x.
Proof.
rewrite !convolutionE.
apply: eq_trans (congr1 (paired_tensor hmu a b) (esym (hD x))) _.
exact: paired_tensor_swap.
Qed.
End Anticommutativity.
