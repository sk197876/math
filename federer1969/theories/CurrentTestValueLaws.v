(** Federer (1969), 4.1.7, pp. 355–356: the
    original test-form vector operations are pointwise,
    by their actual realization in 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestValueLaws.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation ev := (@current_test_value R h2 n U hU m).

(** Source for [current_test_zero_value]: the zero
    original test form vanishes pointwise, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma current_test_zero_value x:ev 0 x=0.
Proof.
change (smooth_test_values_hom hE 0 x=0);by rewrite linear0.
Qed.

(** Source for [current_test_add_value]: pointwise
    original test addition, supporting Federer
    4.1.7, pp. 355–356. *)
Lemma current_test_add_value phi psi x:ev (phi+psi) x=ev phi x+ev psi x.
Proof.
change (smooth_test_values_hom hE (phi+psi) x=
  smooth_test_values_hom hE phi x+smooth_test_values_hom hE psi x).
by rewrite linearD.
Qed.

(** Source for [current_test_scale_value]: pointwise
    original test scalar multiplication, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma current_test_scale_value c phi x:ev (c*:phi) x=c*:ev phi x.
Proof.
change (smooth_test_values_hom hE (c*:phi) x=c*:smooth_test_values_hom hE phi x).
by rewrite linearZ.
Qed.
End CurrentTestValueLaws.
