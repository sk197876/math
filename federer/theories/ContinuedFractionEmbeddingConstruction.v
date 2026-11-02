(** Private existence proof for the classical continued-fraction
    homeomorphism in Federer (1969), 2.2.9, p. 65. The already sealed
    abstract tree map is applied to verified four-digit cylinders.
    Regrouping then gives ordinary digits, the cylinder image is the
    ordinary irrational unit interval, and all ordinary convergents have the
    required limit. The witness will be hidden behind the limit-map
    specification. Bell2016, section 1 and Theorem 2, pp. 1 and 5, supports
    the scalar/cylinder interpretation *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceTreePrefixes RealMetricBackground
  RealMetricCompleteness RealOpenIntervals NaturalQuadruplingUP NaturalQuadruplingSealed
  SequenceFourBlocks SequenceFourBlockTopology OpenEmbeddingMapUP OpenEmbeddingMapSealed
  OpenEmbeddingInjectivity OpenEmbeddingMapContinuous OpenEmbeddingImageEquality
  OpenEmbeddingOpenness HomeomorphismOnto RationalRealUP ContinuedFractionTreeConstruction
  ContinuedFractionTreeImageConstruction ContinuedFractionLimitUP ContinuedFractionCylinderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continued_fraction_homeomorphism_exists]: direct
    existence assertion in the final comparison of Federer 2.2.9,
    p. 65. The same map is both the limit of
    the literal ordinary continued fractions and a homeomorphism
    onto the ordinary irrational points of (0,1). *)
Theorem continued_fraction_homeomorphism_exists (R : realType) :
  exists f : positive_sequence_space R -> real_line_metric R,
    is_continued_fraction_map f /\ is_homeomorphism_onto (@irrational_unit_interval R : set (real_line_metric R)) f.
Proof.
pose d := NaturalQuadrupling.decode.
have hd : injective d := can_inj (natural_quadrupling_decodeK NaturalQuadrupling.laws).
have hs q : exists j, d j = q.
  exists (NaturalQuadrupling.encode q); exact (natural_quadrupling_encodeK NaturalQuadrupling.laws q).
pose U := @continued_fraction_tree R d.
have hU := @continued_fraction_tree_laws R d hd.
pose T := [the metricType R of real_line_metric R].
pose g := @OpenEmbeddingMap.value R T (@real_line_metric_complete R) U hU.
have hg : is_open_embedding_map U g :=
  @OpenEmbeddingMap.laws R T (@real_line_metric_complete R) U hU.
pose f (n : positive_sequence_space R) : real_line_metric R := g (sequence_group_four n).
have hf : is_continued_fraction_map f.
  apply: continued_fraction_cylinders_give_limit=> n k hk.
  have hcl := hg (sequence_group_four n) k.
  case he : (sequence_tree_prefix (sequence_group_four n) k)=> [|j s].
  - have hsize := sequence_tree_prefix_size (sequence_group_four n) k.
    rewrite he /= in hsize; by move: hk; rewrite -hsize.
  - rewrite he in hcl; exact: real_open_interval_closure_bounds hcl.
have hi : g @` setT = irrational_unit_interval.
  rewrite (@open_embedding_map_image R T U hU g hg).
  exact: continued_fraction_tree_image hs.
have himage : f @` setT = g @` setT.
  apply/seteqP; split.
  - move=> y [n _ <-]; by exists (sequence_group_four n).
  - move=> y [n _ <-]; exists (sequence_ungroup_four n); first exact Logic.I.
    by rewrite /f sequence_ungroup_fourK.
exists f; split=> //; constructor.
- move=> n m he; apply: (can_inj (@sequence_group_fourK R)).
  exact: (@open_embedding_map_injective R T U hU g hg _ _ he).
- by rewrite himage hi.
- move=> n; apply: continuous_comp (@sequence_group_four_continuous R n) _.
  exact: (@open_embedding_map_continuous R T U hU g hg).
- move=> O hO.
  have [V [hV he]] := @open_embedding_map_open R T U hU g hg
    (sequence_group_four @` O) (sequence_group_four_open hO).
  exists V; split=> //.
  have he' : f @` O = g @` (sequence_group_four @` O).
    apply/seteqP; split.
    + move=> y [n hn <-]; exists (sequence_group_four n); last by [].
      by exists n.
    + move=> y [z [n hn <-] <-]; by exists n.
  rewrite he' he; congr (_ `&` V).
  by rewrite -(@open_embedding_map_image R T U hU g hg) hi.
Qed.
