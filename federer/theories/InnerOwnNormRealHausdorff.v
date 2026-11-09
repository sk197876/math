(** Federer (1969), 3.4.4, p. 318: identify
    the actual Euclidean and norm-metric Hausdorff measures in real degrees. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness NormMetric
  LipschitzUP RealPower RealHausdorffMeasure RealPowerPositiveLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_own_norm_real_hausdorff]: the real-degree
    Hausdorff measure in 3.4.4, p. 318, uses
    the same actual distance in both existing metric interfaces.
    The two identity maps have Lipschitz constant one; the
    proved real-power image comparison gives exact equality
    with the original Gamma normalization, on every set. *)
Theorem inner_own_norm_real_hausdorff (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) (p:R) (hp:(0<=p)%R) (A:set X):
  @real_hausdorff_measure R (real_norm_metric_space (inner_norm_real_norm hB)) p hp A=
    @real_hausdorff_measure R (inner_metric_space hB) p hp A.
Proof.
pose E:=[the metricType R of inner_metric_space hB].
pose N:=[the metricType R of real_norm_metric_space (inner_norm_real_norm hB)].
have hForward:is_metric_lipschitz_bound setT (fun x:E=>(x:N)) 1%R.
  split;first exact:ler01.
  move=>x y _ _;change (is_true (inner_norm hB (x-y)<=1*inner_norm hB (x-y))%R).
  by rewrite mul1r.
have hBackward:is_metric_lipschitz_bound setT (fun x:N=>(x:E)) 1%R.
  split;first exact:ler01.
  move=>x y _ _;change (is_true (inner_norm hB (x-y)<=1*inner_norm hB (x-y))%R).
  by rewrite mul1r.
have hFirst:=@real_hausdorff_positive_lipschitz R E N (fun x=>x) 1 p hp ltr01 hForward A.
have hSecond:=@real_hausdorff_positive_lipschitz R N E (fun x=>x) 1 p hp ltr01 hBackward A.
rewrite !image_id !real_power_one_base !mul1e in hFirst hSecond.
apply/eqP;rewrite eq_le;apply/andP;split;[exact:hFirst|exact:hSecond].
Qed.
