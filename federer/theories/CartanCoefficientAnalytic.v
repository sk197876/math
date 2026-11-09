(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), pp. 97–99: the actual adapted flat coefficient
    is continuous everywhere and analytic off its single
    endpoint. It remains nonnegative and bounded by one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP NormOpenDomainLaws NormRegularity NormRegularityOperations
  NormClassZeroComposition NormClassHigherRestriction NormAnalyticUP NormAnalyticLocal NormAnalyticDomain
  NormAnalyticComposition ScalarAffineAnalytic ContinuousMultilinearUP ContinuousMultilinearSealed
  FlatExponentialSealed FlatExponentialSmooth FlatExponentialAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficient.
Variable R:realType.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).

(** Source for [cartan_coefficient_shift_analytic]: the actual
    affine coordinate 1-z in the adapted coefficient, supporting
    the example cited in 3.4.5, p. 321. *)
Lemma cartan_coefficient_shift_analytic:
  @norm_analytic R R^o R^o N N hN hN setT (fun z=>1-z).
Proof.
move=>a _.
have hAffine:=@scalar_affine_analytic_at R (-1) 1 a.
apply:(norm_analytic_at_domain_agreement _ hAffine)=>z _;ring.
Qed.

(** Source for [cartan_coefficient_off_endpoint_analytic]:
    the actual adapted flat coefficient is analytic on its
    original domain z!=1, supporting 3.4.5, p. 321.
    The flat endpoint is retained as an excluded point. *)
Theorem cartan_coefficient_off_endpoint_analytic:
  @norm_analytic R R^o R^o N N hN hN [set z|z!=1]
    (fun z=>FlatExponential.value (1-z)).
Proof.
have hComp:=@norm_analytic_composition R R^o R^o R^o N N N hN hN hN
  setT (fun t=>t!=0) (fun z=>1-z) (@FlatExponential.value R)
  cartan_coefficient_shift_analytic (@flat_exponential_off_origin_analytic R).
move=>a ha;apply:(@norm_analytic_at_domain_enlargement R R^o R^o N N hN hN
  (fun z=>setT z /\ 1-z!=0) [set z|z!=1] _ a _ (hComp a _)).
- move=>z [_ hz];by move:hz;rewrite subr_eq0 eq_sym.
- split;first exact:Logic.I. by rewrite subr_eq0 eq_sym.
Qed.

(** Source for [cartan_coefficient_continuous]: the actual
    adapted coefficient is continuous even at the flat endpoint,
    supporting closedness of the example cited in 3.4.5, p. 321. *)
Theorem cartan_coefficient_continuous:
  norm_class_zero N N setT (fun z:R^o=>FlatExponential.value (1-z)).
Proof.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose NZ i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have hFlat:=@flat_exponential_class_infinity R Z ev NZ hZ.
have hShift:=norm_class_continuous (norm_analytic_class_all_orders cartan_coefficient_shift_analytic 0%N).
have hComp:=norm_class_zero_composition hShift (norm_class_continuous (hFlat 0%N)).
exact:(norm_class_zero_open_restriction (fun z (_:setT z)=>conj Logic.I Logic.I)
  (fun z (_:setT z)=>norm_full_domain_interior N z) hComp).
Qed.
End Coefficient.
