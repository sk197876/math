(** Federer (1969), 3.2.35, p. 272:
    the actual boundary projection multiplicity
    is two at every point of the original
    projected open convex body. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionLineNormalUP ProjectionLineNormalExistence
  ProjectionLineFibre ProjectionLineSection ProjectionLineBoundary MappingMultiplicity CountingPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_boundary_projection_multiplicity]:
    N(p restricted to Bdry S,y)=2 for y in p(S),
    Federer 3.2.35, p. 272. Proved local
    unit normal existence and actual line endpoints
    discharge the entire fibre description. Their
    strict scalar order and line injectivity prove
    distinctness; the sealed counting measure assigns
    two to that actual pair. No chosen normal,
    endpoint field or finite-to-one premise is added. *)
Theorem convex_boundary_projection_multiplicity (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k)
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) y:
  open S ->is_inner_convex S ->metric_set_bounded S ->
  (euclidean_projection_linear p @` S) y ->
  @mapping_multiplicity R _ _ (euclidean_projection_linear p) (closure S `\` interior S) y=(2:R)%:E.
Proof.
move=>hOpen hConvex hBound [a ha <-].
have [w hW]:=@projection_line_normal_exists R k p.
pose A:=[set t|S (a+t*:w)].
have hFibre:=@projection_line_boundary_fibre R k p w a S hW ha hOpen hConvex hBound.
have [hl [hu _]]:=@projection_open_convex_line_interval R k p w a S hW ha hOpen hConvex hBound.
rewrite /mapping_multiplicity /mapping_fibre hFibre.
apply:counting_measure_distinct_pair; apply/eqP=>he.
have hEqual:=@projection_line_parameter_injective R k p w a hW (inf A) (sup A) he.
have hlt:=lt_trans hl hu; by rewrite hEqual ltxx in hlt.
Qed.
