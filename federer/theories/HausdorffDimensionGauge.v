(** Federer (1969), 2.10.2(1), p. 171: finite H^m mass forces H^k mass zero
    when m<k. The following supporting bound specializes to integer degrees
    and a cutoff at most one; the extra power is bounded by one factor of
    the cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import HausdorffDiameterCost HausdorffPowerCostLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hausdorff_higher_degree_gauge_bound]: supporting
    small-cutoff cost comparison in Federer 2.10.2(1), p. 171;
    integer-degree consequence of the sharper power formula. The
    normalization ratio is retained exactly. *)
Lemma hausdorff_higher_degree_gauge_bound (R : realType) (m k : nat) (d delta : R) :
  (m<k)%N -> 0<=d -> d<=delta -> delta<=1 ->
  (hausdorff_power_cost k d%:E<=
    (hausdorff_normalisation R k/hausdorff_normalisation R m*delta)%:E*
    hausdorff_power_cost m d%:E)%E.
Proof.
move=> hmk hd hdd hdelta; rewrite !hausdorff_power_cost_finite -EFinM lee_fin.
have hd1 : d<=1 := le_trans hdd hdelta.
have hpow n : d^+n<=1.
  elim: n=> [|n ih]; first by rewrite expr0.
  rewrite exprS; have hh := ler_wpM2l hd ih.
  rewrite mulr1 in hh; exact: le_trans hh hd1.
have hpospow n : (0<n)%N -> d^+n<=delta.
  case: n=> [|n] // _; rewrite exprS.
  apply: le_trans _ hdd; apply: le_trans (ler_wpM2l hd (hpow n)) _; by rewrite mulr1.
have hdiff : (0<k-m)%N by rewrite subn_gt0.
have he : d^+k=d^+m*d^+(k-m) by rewrite -exprD subnKC // ltnW.
have hm0 : hausdorff_normalisation R m!=0 by rewrite gt_eqF //; exact: hausdorff_normalisation_positive.
have hb := ler_wpM2l (mulr_ge0 (ltW (@hausdorff_normalisation_positive R k)) (exprn_ge0 m hd)) (hpospow _ hdiff).
rewrite he.
have hh : (hausdorff_normalisation R k/hausdorff_normalisation R m*delta)*
    (hausdorff_normalisation R m*d^+m)=hausdorff_normalisation R k*d^+m*delta.
  by rewrite mulrACA divfK // [delta*_]mulrC mulrA.
by rewrite hh mulrA.
Qed.
