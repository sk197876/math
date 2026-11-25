(** Federer (1969), 4.1.5, p. 350:
    weakly convergent distributions have lower
    semicontinuous original scalar-test gauges.
    Each admissible evaluation converges and is
    dominated by the corresponding gauge; the
    already proved liminf laws finish the argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom ExtendedSupremumUP DistributionVariationUP DistributionVariationBasic
  ExtendedLowerLimitUP ExtendedLowerLimit ExtendedLowerLimitMonotone ExtendedConvergentLowerLimit
  RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [distribution_variation_lower_limit]: the
    first liminf inequality of Federer 4.1.5,
    p. 350. The original gauges may
    take the value infinity and need no
    integration representation for this assertion. *)
Theorem distribution_variation_lower_limit (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:nat->Hom E R^o) (T:Hom E R^o) (f:X->R) (G:nat->\bar R) (g: \bar R):
  (forall i,is_distribution_variation_value NY value (S i) f (G i)) ->
  is_distribution_variation_value NY value T f g ->
  (forall phi:E,forall eta:R,0<eta ->exists N,forall i,(N<=i)%N ->`|S i phi-T phi|<eta) ->
  (g<=extended_lower_limit G)%E.
Proof.
move=>hGauge hLimitGauge hWeak.
apply:(@extended_supremum_least R _ g hLimitGauge (extended_lower_limit G))=>r [phi [hBound hValue]].
rewrite -hValue.
have hLimit:=@extended_convergent_lower_limit R (fun i=>(S i phi)%:E) (T phi)%:E
  (@real_error_extended_order_limit R (fun i=>S i phi) (T phi) (hWeak phi)).
have hIdentification:=@extended_lower_limit_unique R (fun i=>(S i phi)%:E)
  (extended_lower_limit (fun i=>(S i phi)%:E)) (T phi)%:E
  (extended_lower_limit_laws _) hLimit.
have hMonotone:=@extended_lower_limit_pointwise_monotone R (fun i=>(S i phi)%:E) G
  (fun i=>@distribution_variation_upper R X Y NY E value (S i) f (G i) (hGauge i) phi hBound).
by rewrite hIdentification in hMonotone.
Qed.
