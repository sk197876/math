(** Federer (1969), 3.3.5, p. 292: global projection sections
    and countable rectifiability of the original cone-avoiding set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace StructureConeAvoidance StructureGraphSectionUP
  StructureConeSectionExistence StructureLocalSectionsRectifiable MetricDiameter RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_avoiding_section_exists]: the first
    assertion of Federer 3.3.5, p. 292, for the original dimensions
    and projection. Every original subset of diameter less than r is
    contained in an actual global s inverse Lipschitz section of p.
    The coordinate dimension decomposition is local and adds no premise. *)
Theorem structure_cone_avoiding_section_exists (R:realType) n m (hmn:(m<=n)%N)
    (E S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (r: \bar R) (s:R):
  0<s<1 ->is_structure_cone_avoiding hmn E p r s ->S `<=` E ->
  (extended_metric_diameter S<r)%E ->
  exists f,is_structure_projection_section S p s f.
Proof.
pose k:=(n-m)%N.
have hDim:(k+m)%N=n by rewrite /k subnK.
move:E S p r s hmn; rewrite -hDim=>E S p r s hmn hs hAvoid hSE hDiameter.
exact:(@structure_cone_avoiding_section_exists_blocks R k m hmn E S p r s hs hAvoid hSE hDiameter).
Qed.

(** Source for [federer_3_3_5]: complete Federer 3.3.5, p. 292.
    Original cone avoidance yields the asserted actual global sections
    for every original small subset and countable m rectifiability of
    E. Neither source measurability nor a measure hypothesis is added;
    empty sets and both dimension endpoints remain. *)
Theorem federer_3_3_5 (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (r: \bar R) (s:R):
  (0<r)%E ->0<s<1 ->is_structure_cone_avoiding hmn E p r s ->
  (forall S,S `<=` E ->(extended_metric_diameter S<r)%E ->
    exists f,is_structure_projection_section S p s f) /\is_countably_m_rectifiable m E.
Proof.
move=>hr hs hAvoid.
have hSections S hSE hDiameter:=@structure_cone_avoiding_section_exists R n m hmn E S p r s hs hAvoid hSE hDiameter.
split; first exact:hSections.
exact:(@structure_small_sections_countably_rectifiable R n m E p r s hr hSections).
Qed.
