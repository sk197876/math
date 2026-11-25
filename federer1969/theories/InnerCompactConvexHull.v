(** Compact reduction supporting Federer (1969), 2.10.36, p. 198. Replace a
    convex source by a compact convex subset containing the finitely many
    endpoints, before applying the proved compact Steiner volume theorem.
    The final source need not be closed, bounded or measurable. Hulls are
    used only through their sealed least-convex-superset laws. Neither
    passage states the endpoint-volume inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric InnerConvex
  RealNormUP NormMetric LinearBasis FiniteNormCompactHull ConvexHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_compact_convex_hull]: supporting
    finite-dimensional compact-hull fact for
    the reduction in 2.10.36, p. 198.
    The norm and inner-product metric presentations
    have the same distance and topology. *)
Lemma inner_compact_convex_hull (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (d : nat) (e : 'I_d -> V) (C : set (inner_metric_space hB)) :
  is_basis e -> compact C -> C !=set0 ->
  compact (@convex_hull R V C : set (inner_metric_space hB)).
Proof.
move=> he hc hne.
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
exact: (@finite_norm_compact_convex_hull R V (inner_norm hB) hN d e C he hc hne).
Qed.

(** Source for [compact_convex_finite_endpoint_subset]: supporting
    compact reduction of 2.10.36, p. 198.
    Adjoin one source point so empty endpoint
    families are also covered. The hull
    remains inside the original convex source. *)
Theorem compact_convex_finite_endpoint_subset (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (d : nat) (e : 'I_d -> V) (J : finType)
    (S : set (inner_metric_space hB)) (a b : J -> inner_metric_space hB) :
  is_basis e -> is_inner_convex S -> S !=set0 ->
  (forall i, S (a i)) -> (forall i, S (b i)) ->
  exists K : set (inner_metric_space hB),
    compact K /\ is_inner_convex K /\ K `<=` S /\
    (forall i, K (a i)) /\ (forall i, K (b i)) /\ K !=set0.
Proof.
move=> he hS [x hx] ha hb.
pose C : set (inner_metric_space hB) := (a @` setT) `|` (b @` setT) `|` [set x].
have hfin : finite_set C.
  rewrite /C !finite_setU; split; last exact: finite_set1.
  split; exact: finite_image _ finite_finset.
have hne : C !=set0 by exists x; right.
have hCS : C `<=` S.
  move=> y [[[i iS <-]|[i iS <-]]|->]; [exact: ha|exact: hb|exact: hx].
exists (@convex_hull R V C); split.
- exact: (@inner_compact_convex_hull R V B hB d e C he (finite_compact hfin) hne).
split; first exact: (@convex_hull_convex R V C).
split; first exact: (@convex_hull_least R V C S hCS hS).
split.
- move=> i; apply: (@convex_hull_includes R V C); left; left; by exists i.
split.
- move=> i; apply: (@convex_hull_includes R V C); left; right; by exists i.
- exists x; apply: (@convex_hull_includes R V C); by right.
Qed.
