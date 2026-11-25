(** Actual-space endpoint checks for Federer (1969), 4.1.18,
    pp. 374–376: smoothing fixes the nonzero R^0 point current,
    the top-degree representation has its literal unit L1 mass,
    and the quantitative pair representation retains the printed
    cost allowance while its next-degree coefficient vanishes. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentDirac CurrentMassSealed
  FlatCurrentsUP CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAboveDimension CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairCost CurrentFlatNorm
  FlatCurrentRepresentation SmoothingKernelSealed SmoothingDilationSealed.
From FedererTests Require Import FlatCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatRepresentationEndpoints.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 0%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation U:=(fun _:X=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation P:=(@dirac_current R h2 0%N U hU (0:X)).
Local Notation K:=(@flat_point_singleton_index R).
Local Notation W:=(@compact_summable_multivector_space R h2 0%N 0%N U hU).
Local Notation D:=(@compact_summable_multivector_current R h2 0%N 0%N U hU).
Local Notation size:=(@compact_summable_multivector_size R h2 0%N 0%N U hU).
Local Notation phi:=(@SmoothingKernel.value R 0%N).
Local Notation family:=(@SmoothingDilation.value R 0%N phi).

(** Source for [point_current_smoothing_identity]: the actual
    nonzero R^0 point satisfies the original ambient-zero
    smoothing identity, Federer 4.1.18, p. 374. *)
Example point_current_smoothing_identity:
  @current_smoothing R h2 0%N 0%N phi family
    (@SmoothingKernel.laws R 0%N) (@SmoothingDilation.laws R 0%N phi) P 1= P.
Proof.
exact:(@current_smoothing_zero_dimension R h2 0%N phi family
  (@SmoothingKernel.laws R 0%N) (@SmoothingDilation.laws R 0%N phi) 1 (@ltr01 R) P).
Qed.

(** Source for [point_current_top_density_unit_mass]: the
    original top-degree characterization gives a genuine
    coefficient of L1 mass exactly one for the actual
    R^0 Dirac current, Federer 4.1.18, p. 376. *)
Example point_current_top_density_unit_mass:
  exists xi:W,D xi= P /\size xi= 1.
Proof.
have hFlat:@is_flat_current R h2 0%N 0%N U hU P.
  exists K;exact:(@zero_dimensional_point_flat R h2).
have[xi hXi]:=(@current_top_flat_density R h2 0%N U hU P).1 hFlat.
change (P=D xi) in hXi.
exists xi;split;first exact:esym hXi.
have hMass:=@compact_summable_multivector_current_mass R h2 0%N 0%N U hU xi.
rewrite -hXi (@zero_dimensional_point_mass_one R h2) in hMass.
exact:esym (EFin_inj hMass).
Qed.

(** Source for [point_current_quantitative_pair]: the original
    radius-one and price-one allowances give an actual pair
    with J<=2; the next-degree field is literally zero,
    Federer 4.1.18, pp. 375–376. *)
Example point_current_quantitative_pair:
  exists v:@current_lone_pair_space R h2 0%N 0%N U hU,
    @CurrentLonePair.map R h2 0%N 0%N U hU v= P /\v.2=0 /\
    @current_lone_pair_cost R h2 0%N 0%N U hU v<=2.
Proof.
have[v [hValue [_ [_ hCost]]]]:=@current_flat_lone_pair_representation R h2 0%N 0%N U hU
  K P 1 (@zero_dimensional_point_flat R h2) (@ltr01 R) (fun _ _=>Logic.I).
have hNext:=@compact_summable_multivector_above_dimension R h2 0%N 1%N
  (ltnSn 0) U hU v.2.
rewrite (@zero_dimensional_point_flat_norm_one R h2) -EFinD lee_fin in hCost.
exists v;split;first exact:hValue.
split;first exact:hNext.
exact:hCost.
Qed.
End FlatRepresentationEndpoints.
