(** Federer (1969), 4.1.23, p. 380:
    every compact convex transverse box admits
    the printed positive atomic approximation.
    Its common finite partition has actual
    tags in its cells, exact mass,
    and arbitrarily small flat error. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDiracDensity
  CurrentCharacteristicDensity CurrentMassSealed CurrentFlatNorm SmoothCompactSet
  TopologicalBorel EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  FiniteTaggedBorelPartitionUP FiniteTaggedBorelPartitionExistence
  FiniteTaggedPartitionDiameter FiniteTaggedPartitionNonempty
  TransverseAtomicPartition PositiveAtomicZeroCurrentMass MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [transverse_atomic_flat_mass_approximation_exists]:
    choose the B_k, b_k and Q
    in Federer 4.1.23, p. 380,
    with diam(B_k)<=d, M(Q)=M(S)
    and F_B(S-Q)<=d Lebesgue(B).
    Empty B and the one-point R^0
    case require no separate choice of
    a point or division by its measure. *)
Theorem transverse_atomic_flat_mass_approximation_exists (R : realType)
    (h2 : (1+1:R)!=0) n
    (B : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n))
      (fun _ : R_n R n => True))
    (hConvex : is_inner_convex (smooth_compact_carrier B)) (d : R) (hD : 0<d) :
  let X := R_n R n in
  let NX := inner_norm (@euclidean_inner_productP R n) in
  let hFull := fun (x : X) (_ : True) => norm_full_domain_interior NX x in
  let Leb := @euclidean_lebesgue_measure R n in
  let hLeb := euclidean_lebesgue_is_measure R n in
  let hB := @euclidean_distribution_measure_borel R n (smooth_compact_carrier B)
    (closed_borel_set (compact_closed (@metric_hausdorff R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))))
      (smooth_compact_is_compact B))) in
  let S := @current_characteristic_density R h2 n 0%N Leb hLeb
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) (smooth_compact_carrier B) hB
    (@current_scalar_multivector_unit R n) in
  exists (I : finType) (A : I -> set X) (tag : I -> X),
    @is_finite_tagged_borel_partition R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (smooth_compact_carrier B) (d/2) I A tag /\
    (forall i, A i (tag i)) /\
    (forall i, (@extended_metric_diameter R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) (A i)<=d%:E)%E) /\
    let Q := @positive_atomic_zero_current R h2 n I tag (fun i => fine (Leb (A i))) in
    @CurrentMass.value R h2 n 0%N (fun _ => True) hFull Q=
      @CurrentMass.value R h2 n 0%N (fun _ => True) hFull S /\
    (@current_flat_norm R h2 n 0%N (fun _ => True) hFull B (S-Q)<=
      (d*fine (Leb (smooth_compact_carrier B)))%:E)%E.
Proof.
move=> X NX hFull Leb hLeb hB S.
pose XT := real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
have hHalf : 0<d/2 by rewrite divr_gt0 // ltr0n.
have [q [A0 [tag0 hP0]]] := @finite_tagged_compact_borel_partition_exists R n
  (smooth_compact_carrier B) (d/2) (smooth_compact_is_compact B) hHalf.
have [I [A [tag [hP hTags]]]] := @finite_tagged_partition_remove_empty R XT
  (smooth_compact_carrier B) (d/2) [the finType of 'I_q] A0 tag0 hP0.
have hDiam i : (@extended_metric_diameter R XT (A i)<=d%:E)%E.
  apply: (metric_diameter_least (@extended_metric_diameter_specification R XT (A i))).
  - by rewrite lee_fin; exact: ltW hD.
  - move=> x y hx hy; rewrite lee_fin.
    have h := @finite_tagged_partition_pair_distance R XT (smooth_compact_carrier B)
      (d/2) I A tag hP i x y hx hy.
    have hTwo : (2:R)!=0 by rewrite pnatr_eq0.
    by rewrite mulrC divfK // in h.
have [_ [hMass [hError hDiameterSum]]] := @transverse_partition_atomic_estimate R h2 n
  B hConvex I A tag (d/2) d hP hTags hDiam.
exists I,A,tag; split; first exact: hP.
split; first exact: hTags.
split; first exact: hDiam.
split; first exact: hMass.
apply: (le_trans hError); by rewrite lee_fin.
Qed.
