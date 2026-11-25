(** Federer (1969), 4.1.21, p. 378: every
    integral-geometric null subset of U is null for the
    variation of a positive-degree flat current of finite
    mass. Follow the printed compact-restriction proof, spelling
    out the Borel-hull reduction needed for arbitrary E.
    Use the preceding null-support theorem of 4.1.20. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  InnerOwnNormTopology CurrentDomain CurrentSpaces CurrentSupportGeometry
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentMassSealed
  CurrentMassRepresentation CurrentMassFiniteAlgebra CurrentFiniteMassRepresentation
  CurrentMeasurableRestriction CurrentMeasurableRestrictionVariation
  CurrentFlatCompactMeasurableRestriction CurrentCompactMeasurableRestrictionSupport
  FlatCurrentsUP CurrentFlatIntegralGeometricNull
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  IntegralGeometricMeasure MeasureUP MeasureBasic MeasureAlmostBasic
  RadonMeasureUP RadonBorelRegularity RadonFiniteInnerRegularity
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatNullVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT:=(current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Local Notation IG:=(@integral_geometric_measure R n m hMN 1%E).
Local Notation hIG:=(@integral_geometric_measure_is_measure R n m hMN 1%E (lexx _)).

(** Source for [current_flat_integral_geometric_null_variation_for_representation]:
    the complete second corollary of 4.1.21, p. 378,
    for every witness of the actual original normalized
    variation. Borel regularity of I_1^m gives a Borel
    null hull of the arbitrary set E. Radon inner
    regularity is then applied to that measurable hull,
    rather than incorrectly to E itself. Every compact
    restriction is flat by 4.1.17 and has null support;
    4.1.20 makes it zero. Its exact mass is ||T||(K). *)
Theorem current_flat_integral_geometric_null_variation_for_representation
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (E:set X):
  (0<m)%N->@is_flat_current R h2 n m U hU T->
  (@CurrentMass.value R h2 n m U hU T< +oo)%E->
  E `<=` U->IG E=0%E->
  @NormalisedCurrent.measure R h2 n m U hU T hT
    [set x:UT|E (set_val x)]=0%E.
Proof.
move=>hPositive hFlat hFinite hEU hNull.
pose mu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
pose hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT).
pose hm:=distribution_representation_measure hBase.
pose hr:=distribution_representation_radon hBase.
have[B [hEB [hB hMassB]]]:=borel_regular_cover
  (@integral_geometric_measure_borel_regular R n m hMN 1%E (lexx _)) E.
have hBNull:IG B=0%E by rewrite -hMassB.
have hBNorm:@borel_set XT B.
  exact:(@inner_own_norm_borel_iff R X (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) B).1 hB.
pose A:set UT:=[set x:UT|B (set_val x)].
have hABorel:borel_set A.
  exact:(@continuous_borel_preimage UT XT set_val
    (@set_type_val_continuous XT U) B hBNorm).
have hAMeasurable:measure_measurable mu A.
  exact:(@borel_regular_borel_measurable R UT mu hm
    (radon_borel_regular hm hr) A hABorel).
have hTotalFinite:(mu setT< +oo)%E.
  by rewrite /mu -(@current_represented_mass_total R h2 n m U hU T hT).
have hAFinite:(mu A< +oo)%E.
  exact:(le_lt_trans (@measure_mono R UT mu hm A setT (subsetT _)) hTotalFinite).
have hAZero:mu A=0%E.
  apply/eqP;rewrite eq_le (measure_nonnegative hm A) andbT.
  apply:(@radon_finite_measurable_inner_least R UT mu hm hr A 0%E
    hAMeasurable hAFinite)=>K hK hKA.
  pose hKMeasurable:=@radon_compact_measurable R UT mu hm hr K hK.
  pose S:=@current_measurable_restriction R h2 n m U hU T hT K hKMeasurable.
  have hSFlat:@is_flat_current R h2 n m U hU S.
    exact:(@current_flat_compact_measurable_restriction R h2 n m U hU
      T hT K hK hKMeasurable hFlat).
  have hSSupport:=@current_compact_measurable_restriction_support
    R h2 n m U hU T hT K hK hKMeasurable.
  have hImageB:(set_val @` K) `<=` B.
    move=>x [y hy <-];exact:hKA y hy.
  have hSNull:IG (@current_support R h2 n U hU m S)=0%E.
    apply:(measure_null_subset hIG _ hBNull).
    move=>x hx;exact:(@hImageB x (@hSSupport x hx)).
  have hSZero:=@current_flat_integral_geometric_null R h2 n m hMN U hU
    S hPositive hSFlat hSNull.
  have hRestrictionMass:=@current_measurable_restriction_mass
    R h2 n m U hU T hT K hKMeasurable.
  change (@CurrentMass.value R h2 n m U hU S=mu K) in hRestrictionMass.
  rewrite hSZero current_mass_zero in hRestrictionMass.
  by rewrite -hRestrictionMass.
apply:(@measure_null_subset R UT mu hm [set x:UT|E (set_val x)] A _ hAZero).
move=>x hx;exact:hEB (set_val x) hx.
Qed.

(** Source for [current_flat_integral_geometric_null_variation]:
    the original second corollary of 4.1.21, p. 378,
    with representation evidence derived solely from finite
    mass. E remains an arbitrary subset of U: no
    Borel, measurable, relatively closed or compact premise
    is imposed on it. All currents and their variation
    remain on the original open U. *)
Theorem current_flat_integral_geometric_null_variation
    (hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E)
    (E:set X):
  (0<m)%N->@is_flat_current R h2 n m U hU T->
  E `<=` U->IG E=0%E->
  let hT:=@current_finite_mass_representation R h2 n m U hU T hFinite in
  @NormalisedCurrent.measure R h2 n m U hU T hT
    [set x:UT|E (set_val x)]=0%E.
Proof.
move=>hPositive hFlat hEU hNull.
exact:(@current_flat_integral_geometric_null_variation_for_representation
  (@current_finite_mass_representation R h2 n m U hU T hFinite)
  E hPositive hFlat hFinite hEU hNull).
Qed.
End CurrentFlatNullVariation.
