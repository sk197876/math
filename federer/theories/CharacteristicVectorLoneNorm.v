(** Federer (1969), 4.1.5, p. 350:
    the L1 norm of b_(x,r) y in the
    ball quotient formula. The exact characteristic
    calculation reuses 2.4.5 and the earlier
    L1 integral specification, including zero mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormPower RealPower
  CharacteristicFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureCharacteristicIntegral
  SummableRealFunctionUP SummableRealArithmetic MeasureLpNorm MeasureLoneNormIntegral
  MeasureVectorIntegralUP MeasureVectorCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [characteristic_vector_lone_norm]: the exact
    original first-power norm used in the quotient
    S(b_(x,r)y)/||S|| B(x,r), Federer 4.1.5,
    p. 350. *)
Theorem characteristic_vector_lone_norm (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X) (s:X->R) (b:R) (y:Y):
  is_characteristic_function A s ->measure_measurable mu A ->mu A=b%:E ->
  measure_lp_norm mu NY 1
    (partial_function_total (fun x=>(s x*:y:real_norm_metric_space hNY)))=(NY y*b)%:E.
Proof.
move=>hs hA hMass.
have hMember:=(@measure_vector_characteristic_integral R X Y NY hNY mu hm A s b y hs hA hMass).1.
have hNorm:=@measure_lone_norm_integral R X Y NY hNY mu hm _ hMember.
have hChar:=@measure_characteristic_integral R X mu hm A s hs hA.
rewrite hMass in hChar.
have hScaled:=@real_total_integral_scale R X mu hm s b (NY y) hChar.
have hValues x:real_power (NY (s x*:y)) 1=NY y*s x.
  rewrite real_power_one_exponent; last exact:real_seminorm_nonnegative hNY.1 _.
  case:(pselect (A x))=>hx.
  - by rewrite (characteristic_on_set hs hx) scale1r mulr1.
  - by rewrite (characteristic_off_set hs hx) scale0r (real_seminorm_zero hNY.1) mulr0.
have hGraph x z:partial_function_graph (real_total_integrand (fun x=>NY y*s x)) x z <->
    partial_function_graph (partial_norm_power NY 1
      (partial_function_total (fun x=>(s x*:y:real_norm_metric_space hNY)))) x z.
  rewrite real_total_integrand_graph; split.
  - move=>he; exists (s x*:y); split=>//; by rewrite hValues.
  - move=>[v [hv he]]; by rewrite -(hv:s x*:y=v) hValues in he.
exact:(measure_integral_unique hNorm (measure_integral_graph_equivalent hGraph hScaled)).
Qed.
