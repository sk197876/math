(** Federer (1969), 2.10.38, printed p. 199: supporting coordinate slabs of
    the enclosing box. A maximal projected chord bounds both end slabs for
    every source point; convexity of the source is not required. These
    results use only the abstract frame laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric InnerNormalization Bilinear OrthonormalFamilies
  UnitNormalGeometry GreedyChordFrameUP GreedyChordFrameLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Bounds.
Variable R : realType.
Variable n : nat.
Variable S : set (inner_metric_space (@euclidean_inner_productP R n)).
Variable D : greedy_chord_frame_data R n.
Hypothesis hD : is_greedy_chord_frame S D.
Local Notation e := (greedy_chord_axis D).
Local Notation a := (greedy_chord_first D).
Local Notation b := (greedy_chord_second D).
Local Notation c := (greedy_chord_length D).
Local Notation P := (greedy_chord_residual D).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).

(** Source for [greedy_chord_diagonal_coordinate]: supporting
    width of the selected chord along its own
    unit axis in 2.10.38, p. 199.
    Earlier projections preserve that coordinate. *)
Lemma greedy_chord_diagonal_coordinate (i : 'I_n) : B (a i-b i) (e i)=c i.
Proof.
rewrite -(greedy_chord_coordinate_preserved hD (a i-b i) (lexx i))
  (greedy_chord_selected_law hD) (bilZl (inner_bilinear hB)).
change (c i*B (e i) (e i)=c i).
by rewrite (greedy_chord_orthonormal_law hD) eqxx mulr1.
Qed.

(** Source for [greedy_chord_coordinate_difference_bound]: supporting
    coordinate bound for arbitrary source endpoints in
    2.10.38, p. 199. Cauchy's inequality and
    the maximality law apply also to zero widths. *)
Lemma greedy_chord_coordinate_difference_bound (i : 'I_n) x y :
  S x -> S y -> `|B (x-y) (e i)|<=c i.
Proof.
move=> hx hy.
have hu : B (e i) (e i)= 1 by rewrite (greedy_chord_orthonormal_law hD) eqxx.
have hh := @normal_coordinate_bound R (R_n R n) _ hB (e i) hu (P i (x-y)).
rewrite inner_coordinateE (greedy_chord_coordinate_preserved hD (x-y) (lexx i)) in hh.
exact (le_trans hh (@greedy_chord_maximal_law R n S D hD i x y hx hy)).
Qed.

(** Source for [greedy_chord_coordinate_slabs]: supporting
    containing slabs in 2.10.38, p. 199.
    Every point lies between the two perpendicular
    hyperplanes through the selected endpoints. No
    convexity, interior or positive-width premise is added. *)
Theorem greedy_chord_coordinate_slabs (i : 'I_n) x : S x ->
  B (b i) (e i)<=B x (e i)<=B (b i) (e i)+c i.
Proof.
move=> hx.
have [ha hb] := greedy_chord_endpoints_law hD i.
have hab := greedy_chord_diagonal_coordinate i.
rewrite (bilBl (inner_bilinear hB)) in hab.
have hxb := greedy_chord_coordinate_difference_bound i hx hb.
have hax := greedy_chord_coordinate_difference_bound i ha hx.
move: hxb; rewrite (bilBl (inner_bilinear hB)) ler_norml=> /andP [_ hxb].
move: hax; rewrite (bilBl (inner_bilinear hB)) ler_norml=> /andP [_ hax].
apply/andP; split; lra.
Qed.
End Bounds.
