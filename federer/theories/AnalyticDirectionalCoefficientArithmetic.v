(** Federer (1969), 3.4.5, pp. 318–321: actual
    divided coefficient fields commute with finite linear
    operations, by the original higher differential laws
    of 3.1.11, pp. 219–221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialArithmetic
  NormHigherDifferentialFiniteSums NormRegularity NormAnalyticUP NormAnalyticLocal NormSmoothFields
  NormAnalyticHigherJet AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Arithmetic.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Local Notation AN A f:=(@norm_analytic R X Y NX NY hNX hNY A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X Y NX NY hNX hNY).

(** Source for [analytic_directional_coefficient_add]: actual
    divided coefficients add on their original common
    analytic domain, supporting 3.4.5, pp. 318–321. *)
Lemma analytic_directional_coefficient_add (A:set X) (f g:X->Y) k v (c d:X->Y):
  AN A f ->AN A g ->Coefficient A f k v c ->Coefficient A g k v d ->
  Coefficient A (fun x=>f x+g x) k v (fun x=>c x+d x).
Proof.
move=>hf hg hc hd.
have [D [hD hAnalyticD]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY k A f hf.
have [E [hE hAnalyticE]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY k A g hg.
have hSum:=@norm_higher_differential_field_add R X Y NX NY hNX hNY Z ev NZ hZ A k f g D E hD hE.
move=>x hx z hz.
have hEqual:z=D x+E x:=norm_higher_differential_unique hNX hNY hZ hz (hSum x hx).
by rewrite (hc x hx (D x) (hD x hx)) (hd x hx (E x) (hE x hx)) hEqual linearD /= scalerDr.
Qed.

(** Source for [analytic_directional_coefficient_scale]: scalar
    multiplication commutes with actual divided coefficient
    fields, supporting 3.4.5, pp. 318–321. *)
Lemma analytic_directional_coefficient_scale (A:set X) (f:X->Y) k v (c:X->Y) b:
  AN A f ->Coefficient A f k v c ->
  Coefficient A (fun x=>b*:f x) k v (fun x=>b*:c x).
Proof.
move=>hf hc.
have [D [hD hAnalyticD]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY k A f hf.
have hScale:=@norm_higher_differential_field_scale R X Y NX NY hNX hNY Z ev NZ hZ A k f D b hD.
move=>x hx z hz.
have hEqual:z=b*:D x:=norm_higher_differential_unique hNX hNY hZ hz (hScale x hx).
rewrite (hc x hx (D x) (hD x hx)) hEqual !linearZ /= !scalerA.
by rewrite mulrC.
Qed.

(** Source for [analytic_directional_coefficient_finite_sum]:
    finite sums of actual original divided coefficient
    fields give the actual coefficient of the finite
    analytic sum, supporting 3.4.5, pp. 318–321.
    An explicit open-domain law includes the empty family. *)
Theorem analytic_directional_coefficient_finite_sum (A:set X) (I:finType)
    (f:I->X->Y) k v (c:I->X->Y):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,AN A (f i)) ->(forall i,Coefficient A (f i) k v (c i)) ->
  Coefficient A (fun x=>\sum_i f i x) k v (fun x=>\sum_i c i x).
Proof.
move=>hOpen hf hc.
have hex i:exists D:X->Z k,forall x,A x ->has_norm_higher_differential NX ev NZ A (f i) k x (D x).
  have [D [hD hAnalyticD]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY k A (f i) (hf i).
  by exists D.
have [D hD]:=choice hex.
have hSum:=@norm_higher_differential_finite_sum R X Y NX NY hNX hNY Z ev NZ hZ A hOpen
  I f k D hD.
move=>x hx z hz.
have hEqual:z=\sum_i D i x:=norm_higher_differential_unique hNX hNY hZ hz (hSum x hx).
rewrite hEqual linear_sum /= scaler_sumr.
apply:eq_bigr=>i _;exact:(hc i x hx (D i x) (hD i x hx)).
Qed.
End Arithmetic.
