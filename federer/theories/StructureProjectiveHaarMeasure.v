(** Federer (1969), 3.3.4, p. 290: the
    actual projective Hausdorff reference is its
    total mass times the actual normalized Haar
    orbit image. The Haar measure and base
    point remain local; the geometric invariance
    and homogeneous-space hypotheses are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  StructureProjectiveSpace StructureProjectiveMeasure StructureProjectiveActionLaws
  StructureProjectiveMeasureInvariant CompactMetricInvariantOrbitMeasure
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP HomogeneousSpaceUP CompactGroupHaarNormalisation
  MeasureUP MeasurePushforward MeasureScaleIntegral MeasureDerivationContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Identity.
Variable R:realType.
Variable m:nat.
Local Notation hB:=(@euclidean_inner_productP R m.+1).
Local Notation hb:=(@coordinate_basisP R m.+1).
Local Notation O:=(euclidean_orthogonal_group R m.+1).
Local Notation M:=(structure_projective_space R m).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb)
  (linear_group_inv hB hb) (linear_group_unit hB hb) O mulS invS eS.
Variable theta:set (set_type O)->\bar R.

(** Source for [structure_projective_haar_measure]:
    the displayed identity H^m restricted to
    T(U) equals H^m[T(U)] F#beta,
    Federer 3.3.4, p. 290. Both measures
    are actual, the equality holds on all
    subsets and the base point is arbitrary. *)
Theorem structure_projective_haar_measure (x:M):
  @is_normalised_haar_measure R [the topologicalType of set_type O] mulS theta ->forall B:set M,
  structure_projective_measure B=structure_projective_measure (@setT M)*
    measure_pushforward (orbit_map (@structure_projective_action R m) x) theta B.
Proof.
move=>hTheta B.
pose mu:=@structure_projective_measure R m.
have hBounds:=@structure_projective_measure_positive_finite R m.
have hFinite:mu setT \is a fin_num.
  rewrite (ge0_fin_numE (ltW (andP hBounds).1)); exact:(andP hBounds).2.
pose C:=fine (mu setT).
have hMass:mu setT=C%:E by rewrite /C fineK.
have hC:(0<C)%R.
  have hp:(0<mu setT)%E:=(andP hBounds).1.
  by move:hp; rewrite hMass lte_fin.
have hD:=@structure_projective_derivation_measure R m.
have hIdentity:=@compact_metric_finite_invariant_orbit_measure R
  [the topologicalType of set_type O] M mulS invS eS (@structure_projective_action R m)
  (orthogonal_group_lch hS) (structure_projective_homogeneous hS)
  mu theta C x
  (@orthogonal_group_compact_space R (R_n R m.+1) (@euclidean_inner_product R m.+1)
    hB m.+1 (@coordinate_basis R m.+1) hb)
  (derivation_measure_law hD) (derivation_measure_borel_regular hD) hC hMass
  (@structure_projective_measure_invariant R m mulS invS eS hS) hTheta.
have h:=congr1 (fun nu=>nu B) hIdentity.
change (mu B=mu setT*measure_pushforward (orbit_map (@structure_projective_action R m) x) theta B).
by rewrite hMass; exact:h.
Qed.
End Identity.
