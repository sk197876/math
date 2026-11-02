(** Federer (1969), 2.10.21, p. 183: the Hausdorff distance is a metric and
    its absolute profile supremum equals the maximum of the two directed
    distances. Derive these facts solely from the specified
    least-upper-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import CompactSetDistanceProfile MetricSetDistanceBasic HausdorffDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_distance_unique]: supporting
    uniqueness of the supremum defining the distance,
    2.10.21, p. 183. *)
Lemma hausdorff_distance_unique (R : realType) (X : metricType R)
    (d e : compact_metric_set X -> compact_metric_set X -> R) :
  is_hausdorff_distance d -> is_hausdorff_distance e -> d=e.
Proof.
move=> hd he; apply: funext=> C; apply: funext=> D; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (@hausdorff_distance_least_law R X d hd C D (e C D)
    (hausdorff_distance_nonnegative_law he C D) (hausdorff_distance_profile_upper_law he C D)).
- exact: (@hausdorff_distance_least_law R X e he C D (d C D)
    (hausdorff_distance_nonnegative_law hd C D) (hausdorff_distance_profile_upper_law hd C D)).
Qed.

(** Source for [hausdorff_distance_self_law]: supporting
    diagonal metric law in 2.10.21, p. 183. *)
Lemma hausdorff_distance_self_law (R : realType) (X : metricType R)
    (d : compact_metric_set X -> compact_metric_set X -> R) (hd : is_hausdorff_distance d) C :
  d C C=0.
Proof.
apply/eqP; rewrite eq_le (hausdorff_distance_nonnegative_law hd C C) andbT.
apply: (@hausdorff_distance_least_law R X d hd C C 0 (lexx 0))=> x; by rewrite subrr normr0.
Qed.

(** Source for [hausdorff_distance_symmetric_law]: supporting
    symmetry of the distance of 2.10.21, p. 183. *)
Lemma hausdorff_distance_symmetric_law (R : realType) (X : metricType R)
    (d : compact_metric_set X -> compact_metric_set X -> R) (hd : is_hausdorff_distance d) C D :
  d C D=d D C.
Proof.
have hle A B : d A B<=d B A.
  apply: (@hausdorff_distance_least_law R X d hd A B (d B A)
    (hausdorff_distance_nonnegative_law hd B A))=> x.
  rewrite -opprB normrN; exact: hausdorff_distance_profile_upper_law hd B A x.
apply/eqP; by rewrite eq_le (hle C D) (hle D C).
Qed.

(** Source for [hausdorff_distance_separates_law]: supporting
    separation for the metric of 2.10.21, p. 183,
    using the printed injectivity of Omega. *)
Lemma hausdorff_distance_separates_law (R : realType) (X : metricType R)
    (d : compact_metric_set X -> compact_metric_set X -> R) (hd : is_hausdorff_distance d) C D :
  d C D=0 -> C=D.
Proof.
move=> hz; apply: compact_set_distance_profile_injective; apply: funext=> x.
have hh := hausdorff_distance_profile_upper_law hd C D x.
rewrite hz in hh.
have he : compact_set_distance_profile D x-compact_set_distance_profile C x=0.
  apply/eqP; rewrite -normr_eq0; apply/eqP; apply/eqP; by rewrite eq_le hh normr_ge0.
move/eqP: he; by rewrite subr_eq0=> /eqP ->.
Qed.

(** Source for [hausdorff_distance_triangle_law]: supporting
    triangle inequality for 2.10.21, p. 183,
    obtained from the absolute profile differences. *)
Lemma hausdorff_distance_triangle_law (R : realType) (X : metricType R)
    (d : compact_metric_set X -> compact_metric_set X -> R) (hd : is_hausdorff_distance d) D C E :
  d C E<=d C D+d D E.
Proof.
apply: (@hausdorff_distance_least_law R X d hd C E (d C D+d D E)).
- exact: addr_ge0 (hausdorff_distance_nonnegative_law hd C D) (hausdorff_distance_nonnegative_law hd D E).
- move=> x.
  have -> : compact_set_distance_profile E x-compact_set_distance_profile C x=
    (compact_set_distance_profile D x-compact_set_distance_profile C x)+
    (compact_set_distance_profile E x-compact_set_distance_profile D x) by lra.
  apply: le_trans (ler_normD _ _) _.
  exact: lerD (hausdorff_distance_profile_upper_law hd C D x) (hausdorff_distance_profile_upper_law hd D E x).
Qed.

(** Source for [hausdorff_distance_directed_bound]: direct
    second displayed supremum identity of 2.10.21,
    p. 183, in equivalent upper-bound form. The
    two directed families determine the same real number. *)
Theorem hausdorff_distance_directed_bound (R : realType) (X : metricType R)
    (d : compact_metric_set X -> compact_metric_set X -> R) (hd : is_hausdorff_distance d) C D b :
  0<=b ->
  (d C D<=b <->
   (forall x, val C x -> compact_set_distance_profile D x<=b) /\
   (forall x, val D x -> compact_set_distance_profile C x<=b)).
Proof.
move=> hb; split.
- move=> h; split=> x hx.
  + have hz := (proj2 (compact_set_distance_profile_zero C x) hx).
    have hh := le_trans (hausdorff_distance_profile_upper_law hd C D x) h.
    rewrite hz subr0 in hh; exact: le_trans (ler_norm _) hh.
  + have hz := (proj2 (compact_set_distance_profile_zero D x) hx).
    have hh := le_trans (hausdorff_distance_profile_upper_law hd C D x) h.
    rewrite hz sub0r normrN in hh; exact: le_trans (ler_norm _) hh.
- move=> [hC hD]; apply: (@hausdorff_distance_least_law R X d hd C D b hb)=> x.
  have hc := (proj2 (compact_distance_profile_signed_bound C D b) hC) x.
  have he := (proj2 (compact_distance_profile_signed_bound D C b) hD) x.
  rewrite ler_norml; apply/andP; split; lra.
Qed.
