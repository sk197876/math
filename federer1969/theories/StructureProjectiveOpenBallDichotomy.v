(** Federer (1969), 3.3.4, p. 291:
    the actual projective reference almost everywhere
    gives the original zero/infinite open-ball
    alternatives or membership in the original
    Suslin support image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  StructureProjectiveSpace StructureProjectiveMeasure StructureProjectiveDensity
  StructureProjectiveDerivation StructureProjectiveSuslinDichotomy
  StructureOpenBallGrowth StructureOpenBallRatioLimits
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureDerivationContext
  SuslinSetUP PositiveRightOrderLimit PositiveRadiusLimits StrictFivefoldGrowth
  OrthogonalGroupTopology EuclideanOrthogonalInvariantMeasures UpperBallRatioDichotomy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_open_ball_dichotomy]:
    the displayed null-exception conclusion for
    P_v union Q_v union R_v in Federer
    3.3.4, p. 291. The original Suslin
    support, actual reference measure, ordinary
    zero limit and infinite upper limit all
    remain. No numerator regularity or local
    finiteness premise is added. *)
Theorem structure_projective_open_ball_dichotomy (R:realType) m
    (psi:set (structure_projective_space R m)->\bar R)
    (S:set (structure_projective_space R m)):
  is_measure psi ->is_suslin_set R S ->psi (~` S)=0%E ->
  measure_almost_everywhere (@structure_projective_measure R m)
    [set x|S x \/
      positive_right_extended_order_limit (structure_open_ball_growth m psi x) 0%E \/
      positive_radius_upper_limit (structure_open_ball_growth m psi x)=+oo%E].
Proof.
move=>hPsi hS hNull.
have hRef:=@structure_projective_derivation_measure R m.
have hMu:=derivation_measure_law hRef.
have hAlmost:=structure_projective_original_support_dichotomy hPsi hS hNull.
have [d [hd [hLambda [hGrowth _]]]]:=@structure_projective_derivation_context R m.
have hNo:=strict_fivefold_growth_no_null_balls hMu hd hGrowth.
have [mulS [invS [eS hOps]]]:=@orthogonal_group_restriction_exists R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1).
rewrite /measure_almost_everywhere in hAlmost *.
apply:(measure_null_subset hMu _ hAlmost)=>x hBad hGood; apply:hBad.
have hDensity:=@structure_projective_ball_density_limit R m mulS invS eS hOps x.
case:hGood=>hGood; first by left.
right; case:hGood=>hGood.
- left; exact:structure_zero_ratio_open_ball_limit hRef hPsi (hNo x) hDensity hGood.
- right; exact:structure_infinite_ratio_open_ball_upper_limit hRef hPsi (hNo x) hDensity hGood.
Qed.
