(** Federer (1969), 3.2.21, p. 257: a countable
    dense family of the orthogonal source maps suffices to detect
    positive restricted exterior powers. Hereditary metric separability
    supplies the family; no averaging theorem is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps
  RealNormUP NormMetric HomSpaceNormTopology EuclideanHomOperator FiniteNormMetricPolish
  MetricSubsetBackground MetricSubsetSeparability SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_orthogonal_approximation]: supporting
    countable selection of orthogonal coordinates in Federer
    3.2.21, p. 257. Positivity of a restricted exterior
    power is open in the coordinate map, so a dense countable
    family detects the same positive-rank points. Existence uses
    finite-dimensional metric separability already proved in the project. *)
Theorem countable_orthogonal_approximation (R : realType) m :
  exists S : set (Hom (R_n R m) (R_n R m)),countable S /\
    (forall s,S s -> is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R m) (hom_as_linear s)) /\
    forall g : Hom (R_n R m) (R_n R m),
      is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) (hom_as_linear g) ->
      forall r : R,0<r -> exists s,S s /\ euclidean_operator_norm (s-g)<r.
Proof.
pose X := R_n R m.
pose B := @euclidean_inner_product R m.
pose N := @euclidean_operator_norm R m m.
pose hN := @euclidean_operator_norm_is_norm R m m.
pose H := real_norm_metric_space hN.
pose O : set H := fun s=>is_orthogonal_map B B (hom_as_linear (s:Hom X X)).
have [q [b hb]] := @hom_space_finite_basis R X X m (@coordinate_basis R m) (@coordinate_basisP R m)
  m (@coordinate_basis R m) (@coordinate_basisP R m).
have hSep := @finite_norm_metric_separable R (Hom X X) N hN q b hb.
have [D [hD hDense]] := @metric_subset_separable R H O hSep.
pose S : set (Hom X X) := (fun t:metric_subset O=>(val t:Hom X X)) @` D.
exists S; split.
- exact: (sub_countable (card_image_le _ D) hD).
- split.
  + move=> s [t ht <-]; exact: (set_valP t).
  + move=> g hg r hr.
    pose gg : metric_subset O := @exist H (fun s=>s \in O) g (mem_set hg).
    have [t [ht hNear]] := @metric_dense_point_near R (metric_subset O) D hDense gg r hr.
    exists (val t); split; first by exists t.
    move: hNear; rewrite metric_subset_distanceE real_norm_metric_distanceE.
    change (is_true (N (g-val t)<r) -> is_true (N (val t-g)<r)).
    have hSwap : N (g-val t)=N (val t-g) := real_seminorm_subtract hN.1 g (val t).
    by rewrite hSwap.
Qed.
