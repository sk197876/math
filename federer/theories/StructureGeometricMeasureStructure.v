(** Federer (1969), 3.3.16, p. 299: complete actual
    spherical, exterior-diameter, Gross and Q_t replacements. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP
  HausdorffMeasure ExteriorMeasure ProjectionMeasure IntegralGeometricMeasure
  StructureReplacementMeasureUP StructureReplacementMeasureInstances StructureReplacementStructure
  StructureReplacementPureDecomposition StructureReplacementRectifiableMass TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_geometric_measure_conclusion]: the
    COMPLETE conclusion of 3.3.13, pp. 297–298, with the
    replacement required by Federer 3.3.16, p. 299. The SAME
    Borel countably rectifiable part works for every final
    exponent, the original remainder is pure and null for each
    actual I_t, and the literal mass identity and both directions
    of equality iff rectifiability are retained. This predicate
    states the conclusion; it supplies no mathematical axiom. *)
Definition structure_geometric_measure_conclusion (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  (exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable phi m (E `\` B) /\
    forall t: \bar R,1<=t ->
      @integral_geometric_measure R n m hmn t (E `\` B)=0 /\
      phi E=@integral_geometric_measure R n m hmn t E+phi (E `\` B)) /\
  forall t: \bar R,1<=t ->
    (phi E=@integral_geometric_measure R n m hmn t E <->is_measure_m_rectifiable phi m E).

(** Source for [structure_replacement_complete]: the common
    modified proof in Federer 3.3.16, p. 299, applied only to
    the independently stated replacement-measure laws. The
    SAME original Borel part works for every final exponent. *)
Lemma structure_replacement_complete (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_replacement_measure m phi ->phi E< +oo ->
  structure_geometric_measure_conclusion hmn phi E.
Proof.
move=>hLaws hFinite; split.
- have [B [hB [hRect [hPure hNull]]]]:=@structure_replacement_pure_decomposition R n m hmn phi E hLaws hFinite.
  exists B; split; first exact:hB.
  split; first exact:hRect.
  split; first exact:hPure.
  move=>t ht; split; first exact:hNull t ht.
  exact:(@structure_replacement_rectifiable_mass_split R n m hmn phi E B t hLaws hFinite ht hB hRect (hNull t ht)).
- move=>t ht; exact:(@structure_replacement_structure_theorem R n m hmn phi E t hLaws hFinite ht).2.
Qed.

(** Source for [federer_3_3_16_spherical]: the COMPLETE actual
    spherical replacement in Federer 3.3.16, p. 299. Original
    S^m(E)<infinity is the only original mass premise; actual
    measure comparisons and bounded-image agreement are proved. *)
Theorem federer_3_3_16_spherical (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m E< +oo ->
  structure_geometric_measure_conclusion hmn
    (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) E.
Proof. exact:(@structure_replacement_complete R n m hmn _ E (@spherical_structure_replacement_laws R n m hmn)). Qed.

(** Source for [federer_3_3_16_exterior]: the COMPLETE actual
    exterior-diameter replacement in Federer 3.3.16, p. 299.
    Original T^m(E)<infinity is the only original mass premise;
    no finite original Hausdorff mass or measurability is added. *)
Theorem federer_3_3_16_exterior (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  @exterior_diameter_measure R n m E< +oo ->
  structure_geometric_measure_conclusion hmn (@exterior_diameter_measure R n m) E.
Proof. exact:(@structure_replacement_complete R n m hmn _ E (@exterior_structure_replacement_laws R n m hmn)). Qed.

(** Source for [federer_3_3_16_gross]: the COMPLETE actual
    Gross replacement in Federer 3.3.16, p. 299. Original
    G^m(E)<infinity is the only mass premise. Every original
    source, every final exponent and the original pure remainder
    remain; no false universal H^m<=constant*G^m is asserted. *)
Theorem federer_3_3_16_gross (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  @gross_measure R n m E< +oo ->
  structure_geometric_measure_conclusion hmn (@gross_measure R n m) E.
Proof. exact:(@structure_replacement_complete R n m hmn _ E (@gross_structure_replacement_laws R n m hmn)). Qed.

(** Source for [federer_3_3_16_convex_integral]: the COMPLETE
    actual Q_u replacement in Federer 3.3.16, p. 299. Retain
    EVERY replacement exponent 1<=u<=infinity, independently of
    every final exponent 1<=t<=infinity. Positive m<=n is the
    original convention for Q_u in 2.10.5, p. 173. No finite
    original Hausdorff mass or source measurability is added. *)
Theorem federer_3_3_16_convex_integral (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) (u: \bar R):
  (0<m)%N ->1<=u ->@convex_integral_geometric_measure R n m hmn u E< +oo ->
  structure_geometric_measure_conclusion hmn (@convex_integral_geometric_measure R n m hmn u) E.
Proof.
move=>hm hu; exact:(@structure_replacement_complete R n m hmn _ E (@convex_integral_structure_replacement_laws R n m hmn u hm hu)).
Qed.
