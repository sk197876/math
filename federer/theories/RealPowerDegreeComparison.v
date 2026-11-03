(** Federer 2.10.2(1), p. 171: compare real Hausdorff degrees at a
    small cutoff. The exact excess power is retained; it need not be an
    integer or at least one. Zero diameters retain the 0^0 convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra ring.
From Federer Require Import RealPower RealPowerSuccessor MetricRealPowerCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_real_power_higher_degree_cost]: Federer 2.10.2(1),
    p. 171; supporting cutoff bound for arbitrary nonnegative real p<q.
    No measurability or positive-diameter premise is added. *)
Lemma metric_real_power_higher_degree_cost (R:realType) (u v p q d delta:R):
  0<u -> 0<v -> 0<=p -> p<q -> 0<=d -> d<=delta ->
  (metric_real_power_cost v q d%:E <=
    (v/u*real_power delta (q-p))%:E*metric_real_power_cost u p d%:E)%E.
Proof.
move=>hu hv hp hpq hd hdd.
rewrite !metric_real_power_cost_finite -EFinM lee_fin.
have hdiff:0<q-p by rewrite subr_gt0.
have hq:0<q:=le_lt_trans hp hpq.
have hdelta:0<=delta:=le_trans hd hdd.
case:(eqVneq d 0)=>[hd0|hdne].
- subst d; rewrite real_power_zero_base ?gt_eqF // mulr0.
  apply:mulr_ge0.
  + apply:mulr_ge0; last exact:real_power_nonnegative.
    apply:divr_ge0; exact:ltW.
  + apply:mulr_ge0; first exact:ltW hu.
    exact:real_power_nonnegative.
have hdp:0<d by rewrite lt_neqAle eq_sym hdne hd.
have hpqsum:p+(q-p)=q by ring.
have hPower:real_power d q=real_power d p*real_power d (q-p).
  have hh:=@real_power_add_exponents_positive R d p (q-p) hdp.
  by rewrite hpqsum in hh.
have hBound:=real_power_monotone hd hdd hdiff.
have hScale:=ler_wpM2l (mulr_ge0 (ltW hv) (real_power_nonnegative d p)) hBound.
rewrite hPower.
have hEq:(v/u*real_power delta (q-p))*(u*real_power d p)=
    (v*real_power d p)*real_power delta (q-p).
  by rewrite mulrACA divfK ?gt_eqF // [real_power delta _*_]mulrC mulrA.
by rewrite hEq mulrA.
Qed.
