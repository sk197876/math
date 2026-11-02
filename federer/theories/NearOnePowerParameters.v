(** Federer (1969), 3.2.22, p. 260:
    choose the chart distortion arbitrarily close to one
    at each prescribed positive natural power. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [near_one_positive_power_parameter]: supporting
    the final lambda-to-one passage of Federer 3.2.22,
    p. 260. For positive natural q and t>1,
    the already specified positive real qth root of t
    gives lambda>1 with lambda^q=t. This is a local
    existence statement, with no new selected global sequence. *)
Lemma near_one_positive_power_parameter (R:realType) q (t:R):
  (0<q)%N ->1<t ->exists lambda:R,1<lambda /\ lambda^+q=t.
Proof.
move=>hq ht.
have ht0:0<t:=lt_trans ltr01 ht.
have hqR:0<(q%:R:R) by rewrite ltr0n.
have hqi:0<(q%:R:R)^-1 by rewrite invr_gt0.
pose lambda:=real_power t (q%:R:R)^-1.
have hLambda:1<lambda.
  have hh:=real_power_strict_monotone ler01 ht hqi.
  by rewrite real_power_one_base in hh.
exists lambda; split; first exact hLambda.
rewrite -(real_power_natural_exponent q (ltW (lt_trans ltr01 hLambda))).
rewrite /lambda (@real_power_positive_iterate R t (q%:R:R)^-1 (q%:R:R) (ltW ht0) hqi hqR).
rewrite mulVf ?gt_eqF //; exact:(real_power_one_exponent (ltW ht0)).
Qed.
