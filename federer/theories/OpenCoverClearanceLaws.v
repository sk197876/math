(** Federer (1969), 3.1.13, p. 224:
    positivity, Lipschitz control and subordinate
    balls follow from the abstract supremum
    of capped complement distances. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import TruncatedComplementDistanceUP TruncatedComplementDistanceSealed
  TruncatedComplementDistanceLaws OpenCoverClearanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ClearanceLaws.
Variable R : realType.
Variable X : metricType R.
Variable Phi : set (set X).
Variable rho : X->R.
Hypothesis hrho : is_open_cover_clearance Phi rho.

(** Source for [open_cover_clearance_cap]:
    the unscaled supremum defining h is
    at most one, Federer 3.1.13, p. 224. *)
Lemma open_cover_clearance_cap x : rho x<=1.
Proof.
apply: (open_cover_clearance_least hrho ler01 _)=>T hT.
exact: (truncated_complement_distance_cap (TruncatedComplementDistance.laws T) x).
Qed.

(** Source for [open_cover_clearance_unique]:
    the supremum laws determine the cover
    clearance uniquely, supporting Federer
    3.1.13, p. 224. *)
Lemma open_cover_clearance_unique sigma :
  is_open_cover_clearance Phi sigma -> forall x, rho x=sigma x.
Proof.
move=>hs x; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (open_cover_clearance_least hrho (open_cover_clearance_nonnegative hs x)).
  exact: (open_cover_clearance_upper hs x).
- apply: (open_cover_clearance_least hs (open_cover_clearance_nonnegative hrho x)).
  exact: (open_cover_clearance_upper hrho x).
Qed.

(** Source for [open_cover_clearance_subtract]:
    a supremum of these uniformly one-Lipschitz
    functions has the same one-sided bound,
    supporting Federer 3.1.13, p. 224. *)
Lemma open_cover_clearance_subtract x y : rho x-rho y<=mdist x y.
Proof.
rewrite lerBlDr.
apply: (open_cover_clearance_least hrho _).
- exact: (addr_ge0 (mdist_ge0 x y) (open_cover_clearance_nonnegative hrho y)).
- move=>T hT.
  have hb := truncated_complement_distance_subtract (TruncatedComplementDistance.laws T) x y.
  have hu := open_cover_clearance_upper hrho y hT.
  lra.
Qed.

(** Source for [open_cover_clearance_lipschitz]:
    the Lipschitz constant of the unscaled
    supremum is at most one, giving
    Lip(h)<=1/20 in Federer 3.1.13, p. 224. *)
Theorem open_cover_clearance_lipschitz x y : `|rho x-rho y|<=mdist x y.
Proof.
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (metric_sym x y); exact: open_cover_clearance_subtract.
- exact: open_cover_clearance_subtract.
Qed.

(** Source for [open_cover_clearance_outside]:
    the auxiliary global clearance vanishes
    outside the union of the family,
    supporting the domain convention in
    Federer 3.1.13, p. 224. *)
Lemma open_cover_clearance_outside x :
  ~(exists T, Phi T /\ T x) -> rho x=0.
Proof.
move=>hx; apply/eqP; rewrite eq_le (open_cover_clearance_nonnegative hrho x) andbT.
apply: (open_cover_clearance_least hrho (lexx _) _)=>T hT.
have hn : ~T x by move=>ht; apply: hx; by exists T.
by rewrite (truncated_complement_distance_outside (TruncatedComplementDistance.laws T) hn).
Qed.

(** Source for [open_cover_clearance_positive]:
    h is positive on the union of an
    arbitrary open family, Federer 3.1.13,
    p. 224. The proof selects only
    one original member containing the point. *)
Lemma open_cover_clearance_positive x :
  (forall T, Phi T -> open T) ->
  (exists T, Phi T /\ T x) -> 0<rho x.
Proof.
move=>ho [T [hT hx]].
have hp := truncated_complement_distance_positive
  (TruncatedComplementDistance.laws T) (ho T hT) hx.
exact: (lt_le_trans hp (open_cover_clearance_upper hrho x hT)).
Qed.

(** Source for [open_cover_clearance_approximation]:
    every nonnegative threshold below the
    supremum is exceeded by an original
    cover member's truncated distance, supporting
    subordination in Federer 3.1.13, p. 224. *)
Lemma open_cover_clearance_approximation x r :
  0<=r -> r<rho x ->
  exists T, Phi T /\ r<TruncatedComplementDistance.value T x.
Proof.
move=>hr hlt; apply: contrapT=>hne.
have hb T : Phi T -> TruncatedComplementDistance.value T x<=r.
  move=>hT; rewrite leNgt; apply/negP=>hh; apply: hne; by exists T.
have hh := lt_le_trans hlt (open_cover_clearance_least hrho hr hb).
by rewrite ltxx in hh.
Qed.

(** Source for [open_cover_clearance_subordinate_ball]:
    a closed ball of nonnegative radius
    strictly below the clearance lies in
    some original cover member, supporting
    Federer 3.1.13, pp. 224–225. *)
Theorem open_cover_clearance_subordinate_ball x r :
  0<=r -> r<rho x ->
  exists T, Phi T /\ forall y, mdist x y<=r -> T y.
Proof.
move=>hr hlt; have [T [hT hd]] := open_cover_clearance_approximation hr hlt.
exists T; split=> // y hy.
exact: (truncated_complement_distance_ball_subset
  (TruncatedComplementDistance.laws T) (le_lt_trans hy hd)).
Qed.
End ClearanceLaws.
