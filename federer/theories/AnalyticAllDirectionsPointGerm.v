(** Federer (1969), 3.4.8(11), p. 333:
    the simultaneous original B_j witnesses
    isolate the zero-dimensional common variety germ.
    Representatives and scalar radii remain local
    existence witnesses; all coordinate maps retain
    their sealed original laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws
  CommutativeIdealUP SetGermUP SetGermOrder GermVanishingSealed AnalyticRotatedGermIdeal
  WeierstrassRegularUP AnalyticReductionActual AnalyticReductionCoordinateRegularWitness AnalyticRegularLineIsolatedZero
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  TriangularGermPointContainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AllDirections.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variables (I:set G) (g:@orthogonal_group R X B hB n e he).
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Variable sigma:@set_germ_space T 0.
Local Notation P:=(fun j:'I_n=>@AnalyticPrefixCoordinates.projection R X n omega (j:nat).+1 (ltn_ord j)).

(** Source for [analytic_all_directions_point_germ]:
    every original coordinate of the common
    variety vanishes near zero in the
    m=0 argument of 3.4.8(11), p. 333.
    The original ideal and all B_j
    hypotheses supply the actual regular equations. *)
Theorem analytic_all_directions_point_germ:
  is_commutative_ideal I ->~I 1 ->
  (forall j,@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  Ig `<=` @AnalyticSetIdeal.value R X NX hNX 0 sigma ->
  set_germ_subset sigma (@set_germ T 0 [set 0]).
Proof.
move=>hI hProper hAllB hVanishing.
have hData (j:'I_n):exists f:@analytic_representative_type R X NX hNX 0,
    exists F:R_n R (j:nat).+1->R^o,exists d:R,
      0<d /\ (forall t,0<`|t|<d ->F (t*:@coordinate_basis R (j:nat).+1 ord_max)<>0) /\
      (forall x,analytic_representative_value f x = F (P j x)) /\ Ig (analytic_germ f).
  have [beta [hBeta [k hRegular]]]:=@analytic_reduction_coordinate_regular_witness R X B hB n e he omega hDual
    I j g hI hProper (hAllB j).
  pose Y:=R_n R (j:nat).+1.
  pose NY:=inner_norm (@euclidean_inner_productP R (j:nat).+1).
  pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R (j:nat).+1).
  have [F hF]:=@analytic_germ_has_representative R Y NY hNY 0 beta.
  have hRegularF:is_weierstrass_regular_germ (analytic_germ F) k (@coordinate_basis R (j:nat).+1 ord_max).
    by rewrite hF.
  have [d [hd hLine]]:=@analytic_regular_line_isolated_zero R Y NY hNY F k
    (@coordinate_basis R (j:nat).+1 ord_max) hRegularF.
  have [f [hGerm hValues]]:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega
    (j:nat).+1 (ltn_ord j) F.
  exists f,(analytic_representative_value F),d;split;first exact:hd.
  split;first exact:hLine.
  split;first exact:hValues.
  rewrite -hGerm hF;exact:hBeta.
pose f:=fun j:'I_n=>projT1 (cid (hData j)).
pose F:=fun j:'I_n=>projT1 (cid (projT2 (cid (hData j)))).
pose d:=fun j:'I_n=>projT1 (cid (projT2 (cid (projT2 (cid (hData j)))))).
have hLaws j:=projT2 (cid (projT2 (cid (projT2 (cid (hData j)))))).
apply:(@triangular_germ_point_containment R X NX hNX n e he omega hDual P f F d sigma).
- move=>j;exact:AnalyticPrefixCoordinates.projection_laws.
- move=>j;exact:(hLaws j).1.
- move=>j;exact:(hLaws j).2.1.
- move=>j;exact:(hLaws j).2.2.1.
- move=>j;exact:hVanishing _ (hLaws j).2.2.2.
Qed.
End AllDirections.
