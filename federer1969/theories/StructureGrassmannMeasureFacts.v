(** Federer (1969), 3.3.10, p. 296: the original actual
    Grassmann probability has the measure and Borel laws needed for Fubini. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom HomInner HomSpaceTopology GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct InnerMetric FiniteCoordinates GrassmannHomogeneousSpace
  EuclideanGrassmannProbability EuclideanGrassmannProbabilityUP EuclideanOrthogonalInvariantMeasures
  CompactGroupHomogeneousMeasures CovariantIntegralUP MeasureUP BorelRegularMeasureUP
  OrthogonalGroupTopology LinearGroupSealed LinearGroupTopology IsotropyGroupTopology
  HomogeneousCovariantMeasureRadon SubtypeCompactHausdorff RadonBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.

(** Source for [structure_grassmann_probability_facts]: the
    original gamma_(n,k) of 2.7.16(6), p. 139, used in Federer
    3.3.10, p. 296. Derive the actual measure law, total one
    and Borel regularity from the sealed invariant-probability
    specification. The actual compact homogeneous space and
    nonzero total mass discharge the corrected Radon theorem
    2.7.15, p. 133; no selected Haar integral or plane is global. *)
Theorem structure_grassmann_probability_facts (R:realType) n k (hkn:(k<=n)%N):
  is_measure (@euclidean_grassmann_probability R n k hkn) /\
  @euclidean_grassmann_probability R n k hkn setT= 1%E /\
  is_borel_regular_measure (@euclidean_grassmann_probability R n k hkn).
Proof.
pose hN:=@euclidean_inner_productP R n.
pose hK:=@euclidean_inner_productP R k.
pose hbN:=@coordinate_basisP R n.
pose hbK:=@coordinate_basisP R k.
pose gamma:=@euclidean_grassmann_probability R n k hkn.
have hSpec:=@euclidean_grassmann_probability_specification R n k hkn.
have [J [hMonotone hInvariant hMeasure hRepresentation hRegular]]:=hSpec.1.
split; first exact:hMeasure.
split; first exact:hSpec.2.
have [mulS [invS [eS hS]]]:=orthogonal_group_restriction_exists hN hbN.
have hHomogeneous:=grassmann_space_homogeneous hK hbK hS.
have hCompact:compact (@setT (grassmann_space hK hN hbK hbN)).
  exact:grassmann_space_compact hS.
have hHausdorff:=@grassmann_space_hausdorff R (R_n R k) (R_n R n)
  (@euclidean_inner_product R k) (@euclidean_inner_product R n) hK hN
  k (@coordinate_basis R k) n (@coordinate_basis R n) hbK hbN.
apply:radon_borel_regular hMeasure _.
apply:(homogeneous_covariant_measure_radon (orthogonal_group_lch hS)
  hHomogeneous hHausdorff (compact_space_locally_compact hCompact) hSpec.1).
left; exists setT; split; first exact:hCompact.
by rewrite hSpec.2; exact/eqP/oner_neq0.
Qed.
