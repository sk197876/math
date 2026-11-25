(** Federer (1969), 4.1.5, p. 349: positive scalar
    homogeneity of the original variation gauge gives the
    displayed eta ||S||(g) bound in the Cauchy argument.
    Scaling acts on actual tests; no density or measure
    representation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ExtendedSupremumUP DistributionVariationUP
  DistributionVariationBasic RealValueSupremumScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionVariationScaling.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.

(** Source for [distribution_variation_positive_scaled_values]:
    multiplying a positive majorant by a positive scalar
    multiplies the original admissible evaluation set by that
    scalar, supporting Federer 4.1.5, p. 349. *)
Theorem distribution_variation_positive_scaled_values f a:0<a ->
  distribution_variation_values NY value S (fun x=>a*f x)=
    (fun r:R=>a*r) @` (distribution_variation_values NY value S f).
Proof.
move=>ha.
have hNe:a!=0 by rewrite (gt_eqF ha).
have hInv:0<a^-1 by rewrite invr_gt0.
have hValue (c:R) (phi:E) x:value (c*:phi) x=c*:value phi x.
  exact:(congr1 (fun F:X->Y=>F x) (linearZ_LR (hom_as_linear value) c phi)).
have hScalar (c:R) (phi:E):S (c*:phi)=c*S phi by rewrite linearZ.
apply/seteqP; split.
- move=>r [phi [hNorm hR]].
  exists (S (a^-1*:phi)).
  + exists (a^-1*:phi); split; last reflexivity.
    move=>x; rewrite (@hValue a^-1 phi x) (real_seminorm_scale hNY.1) (ger0_norm (ltW hInv)).
    have hMul:=ler_wpM2l (ltW hInv) (hNorm x).
    by rewrite mulrA mulVf // mul1r in hMul.
  + by rewrite (@hScalar a^-1 phi) mulrA mulfV // mul1r.
- move=>r [s [phi [hNorm hS]] <-].
  exists (a*:phi); split.
  + move=>x; rewrite (@hValue a phi x) (real_seminorm_scale hNY.1) (ger0_norm (ltW ha)).
    exact:(ler_wpM2l (ltW ha) (hNorm x)).
  + by rewrite (@hScalar a phi) hS.
Qed.

(** Source for [distribution_variation_positive_scaled_value]:
    the exact positive homogeneity ||S||(a f)=a ||S||(f)
    used in Federer 4.1.5, p. 349, retains infinite gauge
    values through the original supremum laws. *)
Theorem distribution_variation_positive_scaled_value f c a:
  is_distribution_variation_value NY value S f c ->0<a ->
  is_distribution_variation_value NY value S (fun x=>a*f x) (a%:E*c)%E.
Proof.
move=>hC ha.
change (is_extended_supremum (distribution_variation_values NY value S (fun x=>a*f x)) (a%:E*c)%E).
rewrite (@distribution_variation_positive_scaled_values f a ha).
exact:(@real_value_supremum_positive_scale R (distribution_variation_values NY value S f) c a hC ha).
Qed.

(** Source for [distribution_variation_scaled_absolute_bound]:
    norm(phi)<=a f implies |S(phi)|<=a ||S||(f), the
    original quantitative Cauchy estimate in Federer 4.1.5,
    p. 349, for every positive scalar a. *)
Theorem distribution_variation_scaled_absolute_bound f c a:
  is_distribution_variation_value NY value S f c ->0<a ->forall phi:E,
  (forall x,NY (value phi x)<=a*f x) ->((`|S phi|)%:E<=a%:E*c)%E.
Proof.
move=>hC ha phi hNorm.
exact:(@distribution_variation_absolute_bound R X Y NY hNY E value S (fun x=>a*f x)
  (a%:E*c)%E (@distribution_variation_positive_scaled_value f c a hC ha) phi hNorm).
Qed.
End DistributionVariationScaling.
