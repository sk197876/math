(** Federer (1969), 4.1.1, p. 346: the
    constant identity functional on the scalar
    target supplies ordinary Lebesgue integration
    as a distribution. This supporting dual
    witness uses the original abstract dual laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP RealFunctionalNormUP ContinuousRealFunctional ContinuousDualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_identity_dual_functional_exists]:
    the identity real functional is an actual
    unit-norm member of the scalar continuous
    dual, supporting Federer 4.1.1, p. 346. *)
Theorem scalar_identity_dual_functional_exists (R:realType) (D:lmodType R)
    (ed:Hom D (Hom R^o R^o)) (DN:D->R):
  is_continuous_dual (@scalar_absolute_value_norm R) ed DN ->
  exists a:D,(forall y:R^o,ed a y=y) /\ DN a= 1.
Proof.
move=>hD.
pose L:=hom_of_linear (linear_id R^o).
have hCont:is_continuous_real_functional (@scalar_absolute_value_norm R) (hom_as_linear L).
  apply:(@bounded_real_functional_continuous R R^o (fun y:R^o=>`|y|) (@scalar_absolute_value_norm R)
    (hom_as_linear L) 1 ler01)=>y; by rewrite mul1r.
have [a hEval]:=continuous_dual_surjective hD hCont.
have hValues y:ed a y=y by rewrite hEval.
exists a; split; first exact hValues.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(real_functional_norm_least (continuous_dual_norm_laws hD a) ler01)=>y.
  change (is_true (`|ed a y|<=1*`|y|)).
  by rewrite hValues mul1r.
- have h:=real_functional_norm_bound (continuous_dual_norm_laws hD a) 1.
  change (is_true (`|ed a 1|<=DN a*`|1:R|)) in h.
  by rewrite hValues normr1 mulr1 in h.
Qed.
