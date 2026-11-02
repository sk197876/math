(** Federer (1969), 2.10.26, pp. 189–190: the compact-source part of the
    fibre-measurability proof. On p. 190 the sets V_j are defined by finite
    open covers of the fibre, with diameter at most 1/j and total gauge cost
    less than t+1/j. Prove the asserted openness from compactness of the
    residual source set and continuity of its image. This supporting
    argument applies to arbitrary cutoffs and budgets, and permits empty
    fibres and covers. The cover is specified by its laws, not by a selected
    implementation. no identical fibre-measurability assertion was found. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameter HausdorffDiameterCost NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_fibre_containment_open]: supporting
    openness of V_j in 2.10.26, p. 190.
    Fibres of a compact set lie in a given open
    source set precisely off the closed image of
    the residual compact set. Lipschitz continuity is
    weakened here to ordinary continuity. *)
Lemma compact_fibre_containment_open (R : realType) (X Y : metricType R)
    (f : X -> Y) (A U : set X) :
  continuous f -> compact A -> open U ->
  open [set y | (A `&` f @^-1` [set y]) `<=` U].
Proof.
move=> hf hA hU.
have hK : compact (A `&` ~` U) := compact_closedI hA (open_closedC hU).
have him : compact (f @` (A `&` ~` U)).
  exact: continuous_compact (continuous_subspaceT hf) hK.
have he : [set y | (A `&` f @^-1` [set y]) `<=` U]=~` (f @` (A `&` ~` U)).
  apply/seteqP; split.
  - move=> y hy [x [hxA hxU] hxy]; apply: hxU; apply: hy; split=> //; exact hxy.
  - move=> y hy x [hxA hxy]; apply: contrapT=> hxU; apply: hy; exists x; first by split.
    exact hxy.
rewrite he openC; exact: compact_closed (@metric_hausdorff R Y) him.
Qed.

(** Source for [is_finite_open_fibre_cover]: direct
    defining laws of the finite open family in
    2.10.26, p. 190. The strict gauge budget
    is retained; the source scan prints t+1/j.
    Actual generators are nonempty, as in 2.10.2. *)
Definition is_finite_open_fibre_cover (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : nat) (delta b : \bar R)
    (y : Y) (G : set (set X)) : Prop :=
  finite_set G /\
  (forall S, G S -> open S /\ S!=set0 /\ extended_metric_diameter S<=delta) /\
  (A `&` f @^-1` [set y]) `<=` \bigcup_(S in G) S /\
  nonnegative_sum G (fun S=>hausdorff_diameter_cost k S)<b.

(** Source for [fibre_open_cover_locus]: direct
    locus V_j in 2.10.26, p. 190, with
    arbitrary cutoff delta and strict budget b.
    This is a predicate of admissible covers;
    no unproved witness or measurability is assumed. *)
Definition fibre_open_cover_locus (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : nat) (delta b : \bar R) : set Y :=
  [set y | exists G, is_finite_open_fibre_cover f A k delta b y G].

(** Source for [compact_fibre_open_cover_locus_open]:
    direct assertion that each V_j is open in
    2.10.26, p. 190. Union over admissible finite
    open families of the preceding fibre-containment
    neighbourhoods proves it, including an empty A. *)
Theorem compact_fibre_open_cover_locus_open (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : nat) (delta b : \bar R) :
  continuous f -> compact A -> open (fibre_open_cover_locus f A k delta b).
Proof.
move=> hf hA.
pose D : set (set (set X)) := [set G | finite_set G /\
  (forall S, G S -> open S /\ S!=set0 /\ extended_metric_diameter S<=delta) /\
  nonnegative_sum G (fun S=>hausdorff_diameter_cost k S)<b].
have he : fibre_open_cover_locus f A k delta b=
    \bigcup_(G in D) [set y | (A `&` f @^-1` [set y]) `<=` \bigcup_(S in G) S].
  apply/seteqP; split.
  - move=> y [G [hG [hS [hcover hcost]]]]; exists G=> //; by split=> //; split.
  - move=> y [G [hG [hS hcost]] hcover]; exists G; split=> //; split=> //; by split.
rewrite he; apply: bigcup_open=> G [hG [hS hcost]].
apply: compact_fibre_containment_open hf hA _.
apply: bigcup_open=> S hGS; exact: (hS S hGS).1.
Qed.
