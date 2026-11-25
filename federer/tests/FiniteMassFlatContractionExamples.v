(** Actual-space boundary checks for Federer (1969), 4.1.17,
    p. 374. The nonzero point in R^0 belongs to the normal
    mass closure with its singleton index, but not with the
    empty index. Its scalar unit contraction remains the same
    nonzero flat current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  CurrentDirac CurrentMassSealed CurrentConstantFields CurrentContraction
  CurrentScalarSupportPlateau SmoothCompactSet FlatCurrentsUP FlatCurrentFinite
  CurrentFlatNorm CurrentNormalMassClosure FlatMassContractions.
From FedererTests Require Import FlatCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteMassFlatContractionExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 0%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation U:=(fun _:X=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation P:=(@dirac_current R h2 0%N U hU (0:X)).
Local Notation K:=(@flat_point_singleton_index R).

(** Source for [point_current_normal_mass_closure]: the actual
    nonzero degree-zero point satisfies the complete mass-closure
    assertion, including the R^0 endpoint, Federer 4.1.17, p. 374. *)
Example point_current_normal_mass_closure:
  @is_normal_current_mass_closure R h2 0%N 0%N U hU K P.
Proof.
apply:(@federer_4_1_17_mass_closure R h2 0%N 0%N U hU K P).1.
split;first exact:(@zero_dimensional_point_flat R h2).
by rewrite (@zero_dimensional_point_mass_one R h2) ltry.
Qed.

(** Source for [point_current_not_empty_mass_closure]: finite
    point mass alone does not give mass closure with an empty
    compact index, checking the exact K in Federer 4.1.17, p. 374. *)
Example point_current_not_empty_mass_closure:
  ~@is_normal_current_mass_closure R h2 0%N 0%N U hU
    (@smooth_compact_empty R X NX hNX U) P.
Proof.
move=>hClosure.
have[hFlat _]:=(@federer_4_1_17_mass_closure R h2 0%N 0%N U hU
  (@smooth_compact_empty R X NX hNX U) P).2 hClosure.
have hFinite:=@flat_current_supported_finite R h2 0%N 0%N U hU
  (@smooth_compact_empty R X NX hNX U) P hFlat.
by rewrite (@empty_index_point_flat_value_infinite R h2) ltxx in hFinite.
Qed.

(** Source for [point_current_scalar_unit_contraction]: smooth
    degree-zero contraction preserves the actual nonzero point
    and its singleton flat index, checking both zero degrees of
    the approximation argument in Federer 4.1.17, p. 374. *)
Example point_current_scalar_unit_contraction:
  let gamma:=@current_constant_form R h2 0%N U hU 0%N
    (@zero_form R X R^o 1) in
  @current_contraction R h2 0%N 0%N 0%N U hU gamma P = P /\
  @is_flat_current_supported_in R h2 0%N 0%N U hU K
    (@current_contraction R h2 0%N 0%N 0%N U hU gamma P).
Proof.
move=>gamma;split.
- apply:esym.
  apply:(@current_scalar_support_plateau R h2 0%N 0%N U hU P gamma U).
  + exact:openT.
  + by move=>x hx.
  + by move=>x hx.
  + move=>x hx;exact:(@current_constant_form_values R h2 0%N U hU
      0%N (@zero_form R X R^o 1) x hx).
- exact:(@flat_current_smooth_contraction_supported R h2 0%N 0%N 0%N
    U hU K gamma P (@zero_dimensional_point_flat R h2)).
Qed.
End FiniteMassFlatContractionExamples.
