(** The zero-derivate set in Federer (1969), 2.9.7, p. 155: on a bounded
    target, every positive coefficient bounds psi_phi by that coefficient
    times finite phi measure, hence psi_phi vanishes. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_reference_small_coefficients_zero]: supporting
    vanishing-mass argument for Z in Federer 2.9.7, p. 155 Only the
    reference mass must be finite. The candidate mass may initially be
    infinite. *)
Lemma finite_reference_small_coefficients_zero (R : realType) (a b : \bar R) :
  0<=a -> 0<=b -> b< +oo ->
  (forall c : R, (0<c)%R -> a<=c%:E*b) -> a=0.
Proof.
move=> ha hb hbf hbound; apply/eqP; rewrite eq_le ha andbT.
apply: (@extended_real_reciprocal_upper_bound R a 0%R)=> n.
have hbfin : b \is a fin_num by rewrite (ge0_fin_numE hb).
pose r := fine b.
have heb : b=r%:E by rewrite /r fineK.
have hr0 : (0<=r)%R by move: hb; rewrite heb lee_fin.
have hr1 : (0<r+1)%R.
  apply: le_lt_trans hr0 _; by rewrite ltrDl ltr01.
pose e := ((n.+1%:R : R)^-1)%R.
have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
pose c := (e/(r+1))%R.
have hc : (0<c)%R by rewrite /c divr_gt0.
have hcr : (c*r<e)%R.
  by rewrite /c mulrAC ltr_pdivrMr // mulrDr mulr1 ltrDl.
have h := hbound c hc; rewrite heb -EFinM in h.
rewrite add0r; apply: le_trans h _; rewrite lee_fin; exact: ltW hcr.
Qed.
