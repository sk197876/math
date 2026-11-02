(** Federer (1969), 3.2.3, pp. 243–244: the
    finite Borel reductions exhaust every measurable source
    by the already proved sigma-finiteness of L^m.
    No finiteness or Borelness of A is imposed in the result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  MeasureUP MeasureAlmostBasic CountablyMeasurableUP CountablyMeasurableSubsets
  TopologicalBorel JacobianDensityMeasure InjectiveDifferentialPieceUP LipschitzUP
  HausdorffMeasure AreaBorelReductionUP FiniteAreaBorelReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_injective_area_subset]: the
    reductions preceding and completing Federer 3.2.3(1),
    pp. 243–244. The countable union of the finite
    Borel subsets retains zero discarded Jacobian mass
    and a null discarded image. *)
Theorem measurable_injective_area_subset (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists C,is_borel_injective_area_subset f A C.
Proof.
move=>hLip hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hn:=euclidean_jacobian_measure_is_measure hLip.
pose beta:=@hausdorff_measure R Y m.
pose hb:=@hausdorff_measure_is_measure R Y m.
have hCount:=@measurable_subset_countably_measurable R X mu hm A setT hA (fun x _=>Logic.I)
  (euclidean_lebesgue_countably_measurable R m).
have [F [hF [hUnion hFinite]]]:=hCount.
have hex B:exists C:set X,F B -> is_borel_injective_area_subset f B C.
  case:(pselect (F B))=>hB.
  - have [C hC]:=finite_measurable_injective_area_subset hLip (hFinite B hB).1 (hFinite B hB).2.
    by exists C.
  - exists set0=>h; by exfalso; exact:hB h.
have [C hC]:=choice hex.
pose D:set X:=\bigcup_(B in F) C B.
have hDB:@borel_set [the topologicalType of X] D.
  apply:borel_set_countable_union; first exact hF.
  move=>B hB; exact (hC B hB).1.
have hDA:D `<=` A.
  move=>x [B hB hx]; rewrite hUnion; exists B=>//.
  exact ((hC B hB).2.1 x hx).
have hDLocus:D `<=` injective_differential_locus f.
  move=>x [B hB hx]; exact ((hC B hB).2.2.1 x hx).
have hExcess:A `\` D `<=` \bigcup_(B in F) (B `\` C B).
  move=>x [hx hnD].
  rewrite hUnion in hx; have [B hB hxB]:=hx.
  exists B=>//; split; first exact hxB.
  move=>hCx; apply:hnD; by exists B.
have hNu:nu (A `\` D)=0.
  apply:(measure_null_subset hn hExcess).
  apply:(measure_null_countable_union hn hF)=>B hB.
  exact (hC B hB).2.2.2.1.
have hImageCover:f @` (A `\` D) `<=` \bigcup_(B in F) (f @` (B `\` C B)).
  move=>y [x hx <-]; have [B hB hxB]:=hExcess x hx.
  exists B=>//; by exists x.
have hImage:beta (f @` (A `\` D))=0.
  apply:(measure_null_subset hb hImageCover).
  apply:(measure_null_countable_union hb hF)=>B hB.
  exact (hC B hB).2.2.2.2.
exists D; split; first exact hDB.
split; first exact hDA.
split; first exact hDLocus.
by split.
Qed.
