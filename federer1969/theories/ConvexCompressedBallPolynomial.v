(** Exact anisotropic Steiner polynomials for Federer
    (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps EuclideanPrefixStretch EuclideanPrefixInverseSum ScalarConvexLength VectorSetSum
  CompactSetDistanceProfile CompactMetricBounded EuclideanLebesgueDimensions EuclideanLebesgueDeterminant
  IntegralGeometricGauge EuclideanBallVolume CompactConvexClosedTubePolynomial SteinerTubePolynomial SteinerTubeScalarPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_compressed_ball_volume_polynomial]: supporting
    actual anisotropic tube coefficients in Federer
    3.2.45, pp. 279–280. Apply the exact
    first-block diagonal change of variables to the
    actual tube of the inverse-stretched K. Its
    determinant is h^m. The proved closed-tube
    Steiner formula and finite scalar representatives
    give each displayed coefficient. The original K
    may be thin; both empty blocks and every
    positive h and radius r are retained. *)
Theorem convex_compressed_ball_volume_polynomial (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) (h r : R) :
  K !=set0 -> compact K -> is_inner_convex K -> 0<h -> 0<r ->
  @euclidean_lebesgue_measure R (m+n)
    (vector_set_sum K ((@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then h else 1)) @`
      [set x | inner_norm (@euclidean_inner_productP R (m+n)) x<=r]))=
  (\sum_(i : 'I_(m+n).+1)
    ((h^+m)*fine (@integral_geometric_gauge R (m+n) i (steiner_dimension_guard i) 1
      ((@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then h^-1 else 1)) @` K)))*
    (euclidean_unit_ball_volume R (m+n-i)*r^+(m+n-i)))%:E.
Proof.
move=> hNonempty hCompact hConvex hh hr.
pose N := (m+n)%N.
pose X := inner_metric_space (@euclidean_inner_productP R N).
pose Dh := @euclidean_diagonal_map R N (fun j => if (j<m)%N then h else 1).
pose Di := @euclidean_diagonal_map R N (fun j => if (j<m)%N then h^-1 else 1).
pose B : set X := [set x | inner_norm (@euclidean_inner_productP R N) x<=r].
have hINonempty : Di @` K !=set0.
  have [a ha] := hNonempty; exists (Di a); by exists a.
have hICompact : @compact X (Di @` K).
  exact: continuous_compact (continuous_subspaceT (@euclidean_linear_continuous R N Di)) hCompact.
have hIConvex : is_inner_convex (Di @` K) := linear_image_inner_convex hConvex.
pose C : compact_metric_set X := exist _ (Di @` K) (mem_set (conj hICompact hINonempty)).
have hIClosed : @closed X (Di @` K) := compact_closed (@metric_hausdorff R X) hICompact.
have hTube : euclidean_lebesgue_measure N (vector_set_sum (Di @` K) B)=
    steiner_tube_polynomial (Di @` K) r.
  rewrite -(@euclidean_closed_ball_vector_sum_tube R N (Di @` K)
    (compact_set_distance_profile C) r hIClosed hINonempty (compact_set_distance_profile_specification C)).
  exact: (@compact_convex_closed_tube_polynomial R N C r hIConvex hr).
have hImage := @euclidean_prefix_inverse_sum_image R N m h K B (lt0r_neq0 hh).
have hVolume := @euclidean_lebesgue_linear_image R N Dh (vector_set_sum (Di @` K) B).
rewrite hImage /Dh (@euclidean_prefix_stretch_determinant R m n h)
  normrX (ger0_norm (ltW hh)) hTube in hVolume.
rewrite (@steiner_tube_polynomial_scalar_value R N (Di @` K) r hINonempty hIConvex
  (compact_metric_diameter_finite C)) -EFinM in hVolume.
rewrite hVolume; congr (_%:E).
rewrite mulr_sumr; apply: eq_bigr=> i _; exact: mulrA.
Qed.
