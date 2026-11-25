(** Federer (1969), 2.10.5, p. 172, measurability paragraph: for a Suslin S
    the set of (y,p) with y in p(S) is Suslin. Use the equivalent direct
    continuous image of S times O*(n,m), retaining the book's actual
    incidence set and topologies. Completeness and separability of that
    source justify 2.2.10, p. 65; no projection-volume measurability is
    assumed. Projection conventions: EuclideanProjectionSpace.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  MetricProductBackground MetricProductCompleteness MetricProductSeparability
  CompleteMetricUP SuslinSetUP SuslinPreimages BorelImageMeasurability TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [projection_incidence]: direct set
    {(y,p): y in p(S)} in Federer 2.10.5,
    p. 172, with actual linear orthogonal projections. *)
Definition projection_incidence (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
    set (inner_metric_space (@euclidean_inner_productP R m) *
      orthogonal_projection_metric_space R n m) :=
  [set z | exists x, S x /\ z.1 = euclidean_projection_linear z.2 x].

(** Source for [projection_incidence_horizontal_section]:
    supporting identification of each horizontal section
    of the incidence set in Federer 2.10.5, p. 172,
    with the actual image p(S). *)
Lemma projection_incidence_horizontal_section (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
  [set y | projection_incidence S (y,p)] = euclidean_projection_linear p @` S.
Proof.
apply/seteqP; split.
- move=> y [x [hx he]]; exists x=> //; exact: esym he.
- by move=> y [x hx <-]; exists x.
Qed.

(** Source for [projection_incidence_suslin]: direct
    Suslin conclusion of Federer 2.10.5, p. 172.
    The continuous image is (x,p) mapping to (p(x),p).
    Neither boundedness nor measurability of S is
    substituted for its printed Suslin hypothesis. *)
Theorem projection_incidence_suslin (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> is_suslin_set R (projection_incidence (m:=m) S).
Proof.
move=> hS.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
pose T := [the metricType R of metric_product E P].
pose W := [the metricType R of metric_product Y P].
pose F (z : T) : W := (euclidean_projection_linear z.2 z.1,z.2).
have hf : continuous F.
  apply: topological_pair_continuous; last exact: second_projection_continuous.
  have hs : continuous (fun z : T => (z.2,z.1)).
    apply: topological_pair_continuous.
    - exact: second_projection_continuous.
    - exact: first_projection_continuous.
  move=> z; exact: continuous_comp (hs z)
    (@euclidean_projection_evaluation_continuous R n m (z.2,z.1)).
have hT : is_complete_metric_space T.
  exact (@complete_metric_product R E P (@euclidean_metric_complete R n)
    (@orthogonal_projection_metric_complete R n m)).
have hsep : exists D : set T, countable D /\ dense D.
  exact: (@separable_metric_product R E P (euclidean_metric_separable R n)
    (orthogonal_projection_metric_separable R n m)).
have hpre : is_suslin_set R ((@fst E P) @^-1` S).
  exact: (@continuous_preimage_suslin R T E (@fst E P) S
    (@first_projection_continuous E P) hS).
have himg : F @` ((@fst E P) @^-1` S) = projection_incidence (m:=m) S.
  apply/seteqP; split.
  - by move=> [y p] [[x q] hx <-]; exists x.
  - move=> [y p] [x [hx he]]; exists (x,p)=> //.
    have he' : y=euclidean_projection_linear p x := he.
    change ((euclidean_projection_linear p x,p)=(y,p)).
    by rewrite he'.
rewrite -himg.
exact: (@continuous_suslin_image R T W F _ hT hsep
  (@metric_hausdorff R W) hf hpre).
Qed.
