(** Federer (1969), 2.10.38, printed pp. 198–199: the perpendicular slabs of
    successive maximal chords enclose the source in a rectangular box.
    Derive existence from the public frame and box specifications. The
    chosen origin is only a local existence witness, not a public definition
    of boxes. Source context and the coordinate-box background:
    EuclideanBoxUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerMetric Bilinear OrthonormalFamilies EuclideanLinearMaps
  GreedyChordFrameUP GreedyChordFrameLaws GreedyChordCoordinateBounds EuclideanBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [greedy_chord_enclosing_box]: supporting
    enclosing box in 2.10.38, p. 199,
    for any family satisfying the abstract maximal-chord
    laws. Its side lengths are the specified chord
    lengths; no convexity premise is imposed on S. *)
Theorem greedy_chord_enclosing_box (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (D : greedy_chord_frame_data R n) (hD : is_greedy_chord_frame S D) :
  exists origin Q, is_euclidean_rectangular_box origin (greedy_chord_axis D)
    (greedy_chord_length D) Q /\ S `<=` Q.
Proof.
pose e := greedy_chord_axis D.
pose c := greedy_chord_length D.
pose b := greedy_chord_second D.
pose z : R_n R n := [ffun i=>euclidean_inner_product (b i) (e i)].
pose origin := euclidean_frame_map e z.
pose Q := [set x : inner_metric_space (@euclidean_inner_productP R n) |
  forall i, 0<=euclidean_inner_product (x-origin) (e i)<=c i].
exists origin,Q; split.
- constructor.
  + exact: greedy_chord_orthonormal_law hD.
  + exact: greedy_chord_length_nonnegative hD.
  + by move=> x; split.
- move=> x hx i.
  have /andP [hlo hhi] := @greedy_chord_coordinate_slabs R n S D hD i x hx.
  have hlo' : euclidean_inner_product (b i) (e i)<=euclidean_inner_product x (e i) := hlo.
  have hhi' : euclidean_inner_product x (e i)<=euclidean_inner_product (b i) (e i)+c i := hhi.
  have ho : euclidean_inner_product origin (e i)=euclidean_inner_product (b i) (e i).
    rewrite /origin /euclidean_frame_map /= (euclidean_frame_inner (greedy_chord_orthonormal_law hD)).
    exact: ffunE.
  rewrite (bilBl (inner_bilinear (@euclidean_inner_productP R n))) ho.
  apply/andP; split; lra.
Qed.
