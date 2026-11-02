(** Federer (1969), 2.3.2(7), p. 75: consecutive level bands with endpoints
    r+1/i. Natural n represents i=n+1, so the band endpoints are r+1/(n+2)
    and r+1/(n+1). These are supporting scalar and set-theoretic lemmas for
    the printed parity argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [reciprocal_level_endpoint]: direct endpoint
    r+1/i in Federer 2.3.2(7), p. 75, with i=n+1. *)
Definition reciprocal_level_endpoint (R : realType) (r : R) n : R :=
  (r + ((n.+1)%:R)^-1)%R.

(** Source for [reciprocal_level_endpoint_strict_decrease]:
    supporting separation of parity bands in Federer 2.3.2(7),
    p. 75: increasing a positive denominator lowers the endpoint. *)
Lemma reciprocal_level_endpoint_strict_decrease (R : realType) (r : R) n m :
  (n < m)%N -> (reciprocal_level_endpoint r m < reciprocal_level_endpoint r n)%R.
Proof.
move=> hnm; rewrite /reciprocal_level_endpoint ltrD2l ltf_pV2.
- by rewrite ltr_nat ltnS.
- change (0 < (m.+1%:R : R))%R; by rewrite ltr0n.
- change (0 < (n.+1%:R : R))%R; by rewrite ltr0n.
Qed.

(** Source for [reciprocal_level_endpoint_antitone]: supporting
    weak endpoint monotonicity for the bands in Federer 2.3.2(7), p. 75. *)
Lemma reciprocal_level_endpoint_antitone (R : realType) (r : R) n m :
  (n <= m)%N -> (reciprocal_level_endpoint r m <= reciprocal_level_endpoint r n)%R.
Proof.
move=> hnm; case: (eqVneq n m)=> [->|hne]; first exact: lexx.
apply: ltW; apply: reciprocal_level_endpoint_strict_decrease.
by rewrite ltn_neqAle hne hnm.
Qed.

(** Source for [reciprocal_level_band]: the scalar closed band
    in the definition of B_i in Federer 2.3.2(7), p. 75.
    The measure-theory test set is intersected separately. *)
Definition reciprocal_level_band (R : realType) (r : R) n : set (\bar R) :=
  [set y | (reciprocal_level_endpoint r n.+1)%:E <= y /\
           y <= (reciprocal_level_endpoint r n)%:E].

(** Source for [reciprocal_level_tail_crossing]: supporting
    coverage of the thin level strip by the tail of the bands in
    Federer 2.3.2(7), p. 75. Closed endpoints ensure no
    boundary value is lost. The value y is initially extended real. *)
Lemma reciprocal_level_tail_crossing (R : realType) (r : R) N (y : \bar R) :
  r%:E < y -> y <= (reciprocal_level_endpoint r N)%:E ->
  exists n, (N <= n)%N /\ reciprocal_level_band r n y.
Proof.
move=> hry hyN.
have hex : exists k, (reciprocal_level_endpoint r (N + k).+1)%:E <= y.
  apply: contrapT=> hn.
  have hyr : y <= r%:E.
    apply: extended_real_reciprocal_upper_bound=> k.
    have hyk : y < (reciprocal_level_endpoint r (N + k).+1)%:E.
      rewrite ltNge; apply/negP=> hk; apply: hn; by exists k.
    apply: le_trans (ltW hyk) _; rewrite lee_fin.
    apply: reciprocal_level_endpoint_antitone.
    exact: leq_trans (leq_addl N k) (leqnSn (N+k)).
  have hb := lt_le_trans hry hyr; by rewrite ltxx in hb.
have [k hk hmin] := ex_minnP hex.
exists (N + k)%N; split; first exact: leq_addr.
split; first exact hk.
case: k hk hmin=> [|k] hk hmin; first by rewrite addn0.
rewrite leNgt; apply/negP=> hy.
have hp : (reciprocal_level_endpoint r (N + k).+1)%:E <= y.
  apply: ltW; by rewrite addnS in hy.
have hb := hmin k hp; by rewrite leqNgt ltnSn in hb.
Qed.
