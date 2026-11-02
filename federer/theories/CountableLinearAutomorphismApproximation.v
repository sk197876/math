(** Federer (1969), 3.2.2, p. 242: choose a countable dense
    subset of GL(m,R). Hereditary metric separability supplies only
    actual automorphisms, in every dimension including zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  RealNormUP NormMetric HomSpaceNormTopology EuclideanHomOperator FiniteNormMetricPolish
  MetricSubsetBackground MetricSubsetSeparability SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_linear_automorphism_approximation]: the
    countable dense set S in GL(m,R), Federer 3.2.2, p. 242.
    All elements of S are injective endomorphisms, hence actual
    finite-dimensional automorphisms; every automorphism can be
    approximated in operator norm. The existence statement follows
    from proved metric separability and assumes no dense family. *)
Theorem countable_linear_automorphism_approximation (R:realType) m :
  exists S:set (Hom (R_n R m) (R_n R m)),countable S /\
    (forall s,S s -> injective s) /\
    forall g:Hom (R_n R m) (R_n R m),injective g ->
      forall r:R,0<r -> exists s,S s /\ euclidean_operator_norm (s-g)<r.
Proof.
pose X:=R_n R m.
pose N:=@euclidean_operator_norm R m m.
pose hN:=@euclidean_operator_norm_is_norm R m m.
pose H:=real_norm_metric_space hN.
pose GL:set H:=fun s=>injective (s:Hom X X).
have [q [b hb]]:=@hom_space_finite_basis R X X m (@coordinate_basis R m) (@coordinate_basisP R m)
  m (@coordinate_basis R m) (@coordinate_basisP R m).
have hs:=@finite_norm_metric_separable R (Hom X X) N hN q b hb.
have [D [hD hDense]]:=@metric_subset_separable R H GL hs.
pose S:set (Hom X X):=(fun t:metric_subset GL=>(val t:Hom X X)) @` D.
exists S; split.
- exact (sub_countable (card_image_le _ D) hD).
split.
- move=>s [t ht <-]; exact (set_valP t).
- move=>g hg r hr.
  pose gg:metric_subset GL:=@exist H (fun s=>s \in GL) g (mem_set hg).
  have [t [ht hNear]]:=@metric_dense_point_near R (metric_subset GL) D hDense gg r hr.
  exists (val t); split; first by exists t.
  move:hNear; rewrite metric_subset_distanceE real_norm_metric_distanceE.
  change (is_true (N (g-val t)<r) -> is_true (N (val t-g)<r)).
  have hswap:N (g-val t)=N (val t-g):=real_seminorm_subtract hN.1 g (val t).
  by rewrite hswap.
Qed.
