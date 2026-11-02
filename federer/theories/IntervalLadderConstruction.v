(** Federer (1969), 2.2.9, p. 65, supporting explicit interval refinement
    with countable loss. The private ladder h*N/(N+n) tends to zero and has
    gaps at most h/N; choosing N large makes every gap small. Source
    editions: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ExtendedRealReciprocalBounds IntervalLadderUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [interval_ladder_reciprocal_step]: local scalar
    identity supporting the small-interval choice in Federer
    2.2.9, p. 65; it is not a separately printed book claim. *)
Lemma interval_ladder_reciprocal_step (R : realType) (a : R) :
  0 < a -> a^-1 - (a+1)^-1 = a^-1 / (a+1).
Proof.
move=> ha.
have ha0 : a != 0 by rewrite (gt_eqF ha).
have hb : a+1 != 0 by rewrite gt_eqF //; exact: addr_gt0 ha ltr01.
apply: (mulIf hb).
by rewrite mulrBl divfK // mulVf // mulrDr mulVf // mulr1 addrAC subrr add0r.
Qed.

(** Source for [small_interval_ladder_exists]: supporting existence
    construction for Federer 2.2.9, p. 65. Reciprocal ladders provide all
    small intervals while losing only their endpoints; later proofs use only
    the abstract ladder laws. *)
Theorem small_interval_ladder_exists (R : realType) (h e : R) :
  0 < h -> 0 < e -> exists d, is_small_interval_ladder h e d.
Proof.
move=> hh he.
have [K hK] := positive_reciprocal_nat_small (divr_gt0 he hh).
pose N := K.+1.
have hN : 0 < (N%:R : R) by rewrite ltr0n.
have hNe : h / N%:R < e.
  by move: hK; rewrite ltr_pdivlMr // mulrC.
pose m := h * N%:R.
have hm : 0 < m := mulr_gt0 hh hN.
pose a n := ((N+n)%:R : R).
have ha n : 0 < a n by rewrite /a /N addSn ltr0n.
have has n : a n.+1 = a n + 1 by rewrite /a addnS natr1.
pose d n := m / a n.
have hdn n : d n <= h.
  rewrite /d ler_pdivrMr // /m; apply: ler_wpM2l; first exact: ltW hh.
  by rewrite /a ler_nat leq_addr.
have hgap n : d n - d n.+1 = d n / a n.+1.
  by rewrite /d has -mulrBr interval_ladder_reciprocal_step // mulrA.
exists d; constructor.
- by rewrite /d /a addn0 /m mulfK // gt_eqF.
- move=> n; exact: divr_gt0 hm (ha n).
- move=> n; by rewrite /d (ltr_pM2l hm) (ltf_pV2 (ha n.+1) (ha n)) /a ltr_nat addnS ltnSn.
- move=> n; rewrite hgap; apply: le_lt_trans _ hNe.
  have hb : d n / a n.+1 <= h / a n.+1.
    apply: ler_wpM2r; first by rewrite invr_ge0; exact: ltW (ha n.+1).
    exact: hdn.
  apply: le_trans hb _.
  apply: ler_wpM2l; first exact: ltW hh.
  by rewrite (lef_pV2 (ha n.+1) hN) /a ler_nat leq_addr.
- move=> r hr; have [k hk] := positive_reciprocal_nat_small (divr_gt0 hr hm).
  have hk' : m * (k.+1%:R)^-1 < r.
    by move: hk; rewrite ltr_pdivlMr // mulrC.
  exists k; apply: le_lt_trans _ hk'.
  rewrite /d; apply: ler_wpM2l; first exact: ltW hm.
  have hkpos : 0 < (k.+1%:R : R) by rewrite ltr0n.
  rewrite (lef_pV2 (ha k) hkpos) /a ler_nat /N addSn /=.
  exact: leq_addl.
Qed.
