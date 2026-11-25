(** Federer (1969), 4.1.12, p. 367: F_K(phi)
    bounds both the actual pointwise comass of phi
    and that of d phi on K. Reuse the exact
    maximum formula and compact zeroth-seminorm bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCoefficientNorms
  SmoothCompactSet SmoothTestSpaces CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative
  CurrentFlatFormSeminormLaws CurrentCompactZerothBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatTestPointBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation inc d := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU d)).

(** Source for [current_flat_test_point_bound]:
    the original F_K(phi) bounds the comass of phi
    at every x in K, Federer 4.1.12, p. 367. *)
Lemma current_flat_test_point_bound (phi:DT) x:smooth_compact_carrier K x->
  @current_form_comass R h2 n m (@current_test_value R h2 n U hU m phi x)<=Flat phi.
Proof.
move=>hx;apply:(le_trans (@current_compact_zeroth_point_bound R h2 n m U hU K (inc m phi) x hx)).
rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula;by rewrite le_max lexx.
Qed.

(** Source for [current_flat_test_derivative_point_bound]:
    the original F_K(phi) also bounds the comass of
    d phi at every x in K, Federer 4.1.12, p. 367. *)
Lemma current_flat_test_derivative_point_bound (phi:DT) x:smooth_compact_carrier K x->
  @current_form_comass R h2 n m.+1 (@current_test_value R h2 n U hU m.+1
    (@current_test_exterior_derivative R h2 n m U hU phi) x)<=Flat phi.
Proof.
move=>hx;apply:(le_trans (@current_compact_zeroth_point_bound R h2 n m.+1 U hU K
  (inc m.+1 (@current_test_exterior_derivative R h2 n m U hU phi)) x hx)).
rewrite current_test_exterior_derivative_inclusion /current_flat_test_seminorm
  current_flat_form_seminorm_formula;by rewrite le_max lexx orbT.
Qed.
End CurrentFlatTestPointBounds.
