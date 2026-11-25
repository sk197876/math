(** Federer (1969), 4.1.14, p. 372: every continuous
    form may be tested in the class-one image identity.
    A compact scalar plateau and the preceding uniform
    test approximation of 4.1.5, pp. 349–350,
    approximate it near the actual compact image support.
    The original form need not have compact support. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity NormCutoffProductClass InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates AlternatingForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  SmoothCompactSet SmoothCompactCutoffUP SmoothCompactCutoffSealed
  CompactSupportFunctionUP CompactUniformApproximationUP
  CompactContinuousTestApproximation SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentContinuousTestApproximation.
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
Variable K:smooth_compact_set hNX U.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).

(** Source for [current_continuous_test_approximation]: the
    actual compact smooth tests approximate every continuous
    form uniformly on the prescribed compact K, supporting
    the last sentence of Federer 4.1.14, p. 372,
    by the compact approximation in 4.1.5, pp. 349–350.
    The source and form retain their original domains. *)
Theorem current_continuous_test_approximation (phi:X->Y):
  norm_class_zero NX NY U phi->
  exists P:R->DT,forall eta:R,0<eta->exists delta:R,0<delta /\
    forall e:R,0<e->e<delta->forall x,smooth_compact_carrier K x->
      NY (value (P e) x-phi x)<eta.
Proof.
move=>hPhi.
pose chi:=@SmoothCompactCutoff.value R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) U K hU.
have hChi:=@SmoothCompactCutoff.laws R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) U K hU.
pose C:=@Build_smooth_compact_set R X NX hNX U
  (@real_function_support R (real_norm_metric_space hNX) chi)
  (smooth_cutoff_support_in_domain hChi) (smooth_cutoff_compact hChi).
pose psi:=fun x=>chi x*:phi x.
have hPhiClass:norm_class hNX hNY U phi 0%N.
  exact:((@norm_class_zeroP R X Y NX NY hNX hNY U phi).2 hPhi).
have hPsiClass:norm_class hNX hNY setT psi 0%N.
  exact:(@norm_class_cutoff_product R X Y NX NY hNX hNY U
    (smooth_compact_carrier C) chi phi 0%N hPhiClass (smooth_cutoff_class hChi 0%N)
    (@real_function_support_closed R (real_norm_metric_space hNX) chi)
    (smooth_compact_in_domain C) (@real_function_zero_off_support R
      (real_norm_metric_space hNX) chi)).
have hOff x:~smooth_compact_carrier C x->psi x=0.
  move=>hx;rewrite /psi (real_function_zero_off_support hx);exact:scale0r.
have[W [hW [hKW hPlateau]]]:=smooth_cutoff_neighbourhood_plateau hChi.
have hAgreement x (hx:smooth_compact_carrier K x):psi x=phi x.
  by rewrite /psi /chi (hPlateau x (hKW x hx)) scale1r.
have[P hP]:=@compact_continuous_test_approximation_exists R n Y NY hNY
  (@current_form_complete R h2 n m) U hU E ev hE C psi
  (norm_class_continuous hPsiClass) hOff.
have[C0 [hC0 [hC0U [radius [hRadius [hSupport hUniform]]]]]]:=hP.
exists P=>eta hEta.
have[delta [hDelta hBound]]:=hUniform eta hEta.
exists delta;split;first exact:hDelta.
move=>e he hSmall x hx.
rewrite -(hAgreement x hx);exact:hBound e he hSmall x.
Qed.

(** Source for [current_continuous_test_approximation_at_scale]:
    an actual compact test achieves any prescribed positive
    uniform error near K, supporting the finite-mass
    extension step in Federer 4.1.14, p. 372.
    Empty K requires no separate inhabitant or exception. *)
Corollary current_continuous_test_approximation_at_scale (phi:X->Y):
  norm_class_zero NX NY U phi->forall eta:R,0<eta->
  exists psi:DT,forall x,smooth_compact_carrier K x->NY (value psi x-phi x)<eta.
Proof.
move=>hPhi eta hEta.
have[P hP]:=current_continuous_test_approximation hPhi.
have[d [hd hBound]]:=hP eta hEta.
have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
have hSmall:d/2<d by lra.
exists (P (d/2))=>x hx;exact:hBound (d/2) hHalf hSmall x hx.
Qed.
End CurrentContinuousTestApproximation.
