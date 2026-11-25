(** Federer (1969), 4.1.17, p. 374: smooth contractions
    have a finite bound in the original same-index flat norm.
    Reuse the actual test-product estimate and the original dual
    flat supremum of 4.1.12, p. 367. This is a bound for the
    already defined contraction on actual currents. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentContraction CurrentTestFormProduct
  CurrentFlatNorm CurrentFlatDualSeminormBasic CurrentSmoothFlatTestProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentFlatSmoothContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Variable gamma:@current_smooth_space R h2 n U hU k.
Local Notation C := (@current_space R h2 n U hU (k+p)).
Local Notation action := (@current_value R h2 n U hU (k+p)).
Local Notation outputAction := (@current_value R h2 n U hU p).
Local Notation FK := (@current_flat_norm R h2 n (k+p) U hU K).
Local Notation FP := (@current_flat_norm R h2 n p U hU K).
Local Notation contract := (@current_contraction R h2 n k p U hU gamma).
Local Notation product := (@current_test_form_product R h2 n k p U hU gamma).

(** Source for [current_smooth_contraction_flat_finite_bound]: a
    fixed smooth coefficient gives one finite same-K flat bound
    for every finite-flat input, supporting Federer 4.1.17,
    p. 374. The constant may be zero. No mass, normality or
    positive-degree hypothesis is imposed on the input current. *)
Theorem current_smooth_contraction_flat_finite_bound:
  exists c:R,0<=c /\forall (T:C) a,
    FK T=a%:E->(FP (contract T)<=(c*a)%:E)%E.
Proof.
have[c [hc hProduct]]:=@current_smooth_flat_test_product_bound R h2 n k p
  U hU K gamma.
exists c;split;first exact:hc.
move=>T a hValue.
have ha:=@current_flat_dual_nonnegative R h2 n (k+p) U hU K (action T).
change (is_true (0<=FK T)%E) in ha.
rewrite hValue lee_fin in ha.
apply:(@current_flat_dual_upper_from_bound R h2 n p U hU K
  (outputAction (contract T)) (c*a) (mulr_ge0 hc ha))=>psi.
rewrite current_contraction_evaluation.
apply:(le_trans (@current_flat_dual_finite_bound R h2 n (k+p) U hU K
  (action T) a hValue (product psi))).
have h:=ler_wpM2l ha (hProduct psi).
by rewrite mulrA [a*c]mulrC in h.
Qed.
End CurrentFlatSmoothContraction.
