(** Federer (1969), 4.1.20, p. 378: each projected
    m-dimensional flat current in R^m with Lebesgue-null
    support is zero. This is the exact top-degree application
    of 4.1.18, p. 376, in the printed proof. Its original
    density representation is a conclusion of flatness. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces FlatCurrentsUP
  CurrentTopFlatDensity CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorLinear
  EuclideanLebesgueDimensions EuclideanOpenDomainMeasure OpenSubspaceMeasure
  CurrentDensityNullSupport MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_top_flat_null_support]: an original
    top-degree flat current on any open subset of R^n vanishes
    when its actual support is n-dimensional Lebesgue null,
    the use of 4.1.18 in Federer 4.1.20, p. 378. No density
    representation or finite-mass hypothesis is imposed. *)
Theorem current_top_flat_null_support (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU n):
  @is_flat_current R h2 n n U hU T->
  @euclidean_lebesgue_measure R n (@current_support R h2 n U hU n T)=0->
  T=0.
Proof.
move=>hFlat hNull.
have[xi hValue]:=(@current_top_flat_density R h2 n U hU T).1 hFlat.
change (T=@compact_summable_multivector_current R h2 n n U hU xi) in hValue.
rewrite hValue in hNull *.
apply:(@current_density_null_support R h2 n n U hU
  (@euclidean_open_domain_measure R n U)
  (@euclidean_open_domain_measure_laws R n U hU).1
  (@euclidean_open_domain_measure_laws R n U hU).2
  (@compact_summable_multivector_value R h2 n n U hU xi)
  (@compact_summable_multivector_density_integrable R h2 n n U hU xi)).
change (@euclidean_lebesgue_measure R n (set_val @` [set x:current_domain R n U|
  @current_support R h2 n U hU n
    (@compact_summable_multivector_current R h2 n n U hU xi) (set_val x)])=0).
apply:(@measure_null_subset R (R_n R n) (@euclidean_lebesgue_measure R n)
  (@euclidean_lebesgue_is_measure R n) _ _ _ hNull).
by move=>x [y hy <-].
Qed.
