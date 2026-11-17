(** Federer (1969), 3.4.12, p. 339: a finite complex
    line polynomial has zero actual higher directional derivatives.
    Expose the normed-target connection in the existing remainder
    proof, using the proved Taylor coefficient comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticLocal
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialLocal
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Lines.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).

(** Source for [norm_analytic_finite_line_high_derivative_zero]: the
    original all-nearby-point remainder condition of 3.4.6(1),
    p. 322, for the complex-valued functions of 3.4.12,
    p. 339. Only actual line values and analyticity are premises. *)
Theorem norm_analytic_finite_line_high_derivative_zero (A:set X) (f:X->Y) k v:
  @norm_analytic R X Y NX NY hNX hNY A f ->
  (forall a,A a ->exists b:nat->Y,forall t:R,f (a+t*:v)=\sum_(i<k) t^+i*:b i) ->
  forall p,(k<=p)%N ->forall a,A a ->forall z:Z p,
    has_norm_higher_differential NX ev ZN setT f p a z ->@ev p [ffun _:'I_p=>v] z=0.
Proof.
move=>hf hLine p hp a ha z hz.
have [c [hc _]]:=@analytic_directional_coefficient_exists R X Y NX NY hNX hNY A f p v hf.
have [b hExact]:=hLine a ha.
have hFinite:=@analytic_directional_polynomial_line_coefficient R X Y NX NY hNX hNY
  A f p v a c k b 1 ha hf hc ltr01 (fun t _=>hExact t).
have hLarge:(p<k)%N=false:=leq_gtF hp.
rewrite hLarge in hFinite.
have hOpen x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have hLocal:=(@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
  p setT A f (fun x _=>Logic.I) hOpen a ha z).1 hz.
have hValue:=hc a ha z hLocal.
rewrite hFinite in hValue.
have hNonzero:((p`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hCancel:=congr1 (fun y:Y=>((p`!)%:R:R)*:y) (esym hValue).
by rewrite scalerA mulfV // scale1r scaler0 in hCancel.
Qed.
End Lines.
