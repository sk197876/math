(** Federer (1969), 2.10.26, pp. 189–190: the compact-source part of the
    fibre-measurability proof. On p. 190 the sets V_j are defined by finite
    open covers of the fibre, with diameter at most 1/j and total gauge cost
    less than t+1/j. Prove the asserted openness from compactness of the
    residual source set and continuity of its image. This supporting
    argument applies to arbitrary cutoffs and budgets, and permits empty
    fibres and covers. The cover is specified by its laws, not by a selected
    implementation. No fibre-measurability conclusion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation MetricRealPowerCost CompactFibreOpenCovers MetricDiameter HausdorffDiameterCost NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_real_finite_open_fibre_cover]: direct
    defining laws of the finite open family in
    2.10.26, p. 190. The strict gauge budget
    is retained; the source scan prints t+1/j.
    Actual generators are nonempty, as in 2.10.2. *)
Definition is_real_finite_open_fibre_cover (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (delta b : \bar R)
    (y : Y) (G : set (set X)) : Prop :=
  finite_set G /\
  (forall S, G S -> open S /\ S!=set0 /\ extended_metric_diameter S<=delta) /\
  (A `&` f @^-1` [set y]) `<=` \bigcup_(S in G) S /\
  nonnegative_sum G (fun S=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k S)<b.

(** Source for [real_fibre_open_cover_locus]: direct
    locus V_j in 2.10.26, p. 190, with
    arbitrary cutoff delta and strict budget b.
    This is a predicate of admissible covers;
    no unproved witness or measurability is assumed. *)
Definition real_fibre_open_cover_locus (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (delta b : \bar R) : set Y :=
  [set y | exists G, is_real_finite_open_fibre_cover f A hk delta b y G].

(** Source for [compact_real_fibre_open_cover_locus_open]:
    direct assertion that each V_j is open in
    2.10.26, p. 190. Union over admissible finite
    open families of the preceding fibre-containment
    neighbourhoods proves it, including an empty A. *)
Theorem compact_real_fibre_open_cover_locus_open (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (delta b : \bar R) :
  continuous f -> compact A -> open (real_fibre_open_cover_locus f A hk delta b).
Proof.
move=> hf hA.
pose D : set (set (set X)) := [set G | finite_set G /\
  (forall S, G S -> open S /\ S!=set0 /\ extended_metric_diameter S<=delta) /\
  nonnegative_sum G (fun S=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k S)<b].
have he : real_fibre_open_cover_locus f A hk delta b=
    \bigcup_(G in D) [set y | (A `&` f @^-1` [set y]) `<=` \bigcup_(S in G) S].
  apply/seteqP; split.
  - move=> y [G [hG [hS [hcover hcost]]]]; exists G=> //; by split=> //; split.
  - move=> y [G [hG [hS hcost]] hcover]; exists G; split=> //; split=> //; by split.
rewrite he; apply: bigcup_open=> G [hG [hS hcost]].
apply: compact_fibre_containment_open hf hA _.
apply: bigcup_open=> S hGS; exact: (hS S hGS).1.
Qed.
