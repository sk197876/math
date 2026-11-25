(** Federer (1969), 4.1.12, p. 367: the
    original nu_K^0 is exactly the least nonnegative
    pointwise comass bound on K. These adapters use
    the existing derivative-supremum laws of 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothFunctionSeminormFamily SmoothDerivativeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCompactZerothBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation nu := (smooth_function_derivative_seminorm hD).

(** Source for [current_compact_zeroth_point_bound]:
    nu_K^0 bounds the comass at every point of
    K, the opening formula of Federer 4.1.12,
    p. 367, by the exact order-zero derivative norm. *)
Lemma current_compact_zeroth_point_bound (phi:E) x:
  smooth_compact_carrier K x->NY (ev phi x)<=nu K 0%N phi.
Proof.
move=>hx.
have h:=@smooth_derivative_seminorm_bound R X Y NX NY hNX hNY U E D K 0%N
  (nu K 0%N) (smooth_function_derivative_seminorm_laws hD K 0%N) phi 0%N (leqnn 0%N) x hx.
by rewrite (@smooth_derivative_zero_norm R X Y NX NY hNX hNY U E ev D hD
  phi x (smooth_compact_in_domain K x hx)) in h.
Qed.

(** Source for [current_compact_zeroth_least_bound]:
    every nonnegative pointwise comass bound on K
    bounds nu_K^0, the opening formula of Federer
    4.1.12, p. 367, including empty K. *)
Lemma current_compact_zeroth_least_bound (phi:E) b:
  0<=b->(forall x,smooth_compact_carrier K x->NY (ev phi x)<=b)->nu K 0%N phi<=b.
Proof.
move=>hb hPoint.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K 0%N
  (nu K 0%N) (smooth_function_derivative_seminorm_laws hD K 0%N) phi b hb)=>j hj x hx.
have /eqP->:j==0%N by rewrite -leqn0.
rewrite (@smooth_derivative_zero_norm R X Y NX NY hNX hNY U E ev D hD
  phi x (smooth_compact_in_domain K x hx)).
exact:hPoint x hx.
Qed.
End CurrentCompactZerothBounds.
