(** Federer (1969), 2.5.7, p. 99: rescale the full-support density so that
    its product integral lies strictly between zero and the representation
    defect. All membership and support conditions are retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP TotalScalarLpUP TotalScalarLpClosure TotalScalarPairingValue
  TotalLpPairingBound LpConjugatePair PositiveFullSupportPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_lp_pairing_scale_density]: positive rescaling of r in
    Federer 2.5.7, p. 99 The supporting identity in fact holds for every
    real scalar, including zero. *)
Lemma total_lp_pairing_scale_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (g r : X -> R) (c : R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p g -> total_scalar_lp mu q r ->
  total_scalar_pairing mu g (fun x => (c*r x)%R)=(c*total_scalar_pairing mu g r)%R.
Proof.
move=> hpq hg hr.
have hi := (@total_lp_pairing_specification_and_bound R X mu hm q p r g (lp_conjugate_pair_symmetric hpq) hr hg).1.
rewrite [total_scalar_pairing mu g _]total_scalar_pairing_commute
  (@total_scalar_pairing_scale_left R X mu hm r g c (ex_intro _ (total_scalar_pairing mu r g) hi)).
by rewrite [total_scalar_pairing mu r g]total_scalar_pairing_commute.
Qed.

(** Source for [small_positive_full_support_dual_witness]: the complete
    choice of r with 0<integral g*r<d in Federer 2.5.7, p. 99 In the
    representation proof d is the positive defect P(g)-integral g*k. The
    chosen integral here equals d/2. *)
Theorem small_positive_full_support_dual_witness (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (g : X -> R) (d : R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p g -> (forall x, (0 <= g x)%R) ->
  0 < total_scalar_lp_norm mu p g -> (0 < d)%R ->
  exists r : X -> R, total_scalar_lp mu q r /\ (forall x, (0 <= r x)%R) /\
    (forall x, (0 < r x)%R <-> (0 < g x)%R) /\ (0 < total_scalar_pairing mu g r < d)%R.
Proof.
move=> hpq hg hg0 hN hd.
have [r [hr [hr0 [hs ht]]]] := @positive_full_support_dual_witness R X mu hm p q g hpq hg hg0 hN.
pose c := (d/(2*total_scalar_pairing mu g r))%R.
have h2 : (0 < (2 : R))%R by rewrite ltr0n.
have hc : (0 < c)%R by apply: divr_gt0 hd _; exact: mulr_gt0 h2 ht.
exists (fun x => (c*r x)%R); split.
- exact: (@total_scalar_lp_scale R X mu hm q c r hr).
split; first by move=> x; exact: mulr_ge0 (ltW hc) (hr0 x).
split.
- move=> x.
  have he : (0 < c*r x)%R=(0 < r x)%R by rewrite -{1}(mulr0 c) ltr_pM2l.
  by rewrite he; exact: hs.
- rewrite (@total_lp_pairing_scale_density R X mu hm p q g r c hpq hg hr).
  have he : (c*total_scalar_pairing mu g r)%R=(d/2)%R.
    by rewrite /c invfM mulrA divfK ?gt_eqF.
  rewrite he; apply/andP; split; first exact: divr_gt0 hd h2.
  by rewrite ltr_pdivrMr // mulr_natr mulr2n ltrDl.
Qed.
