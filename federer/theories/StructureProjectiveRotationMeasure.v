(** Federer (1969), 3.3.4, p. 290: actual
    Hausdorff measure restricted to T(U) is invariant
    under the orthogonal action. Prove the identity
    on every subset using the actual two inverse
    isometries; no ambient lower-degree Radon assertion
    or measurable-hull difference is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric SymmetricGrading InnerSymmetricPositivity StructureProjectiveSphere
  StructureProjectiveRotation EuclideanOrthogonalInvariantMeasures
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed MeasureUP MeasureRestriction
  MeasurePushforward HausdorffMeasure HausdorffRestrictedLipschitz LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Invariance.
Variable R:realType.
Variable m:nat.
Local Notation hB:=(@euclidean_inner_productP R m.+1).
Local Notation hb:=(@coordinate_basisP R m.+1).
Local Notation O:=(euclidean_orthogonal_group R m.+1).
Local Notation Y:=(inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) hB 2)).
Local Notation M:=(@structure_projective_sphere R m).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb)
  (linear_group_inv hB hb) (linear_group_unit hB hb) O mulS invS eS.

(** Source for [structure_projective_rotation_hausdorff]:
    the Hausdorff invariance used before 2.7.11(2)
    in Federer 3.3.4, p. 290, on each actual
    subset of T(U). The supporting statement holds
    for every natural Hausdorff degree and all
    subsets, including nonmeasurable ones. *)
Theorem structure_projective_rotation_hausdorff (g:O) q (B:set Y):
  B `<=` M ->@hausdorff_measure R Y q (structure_projective_rotation g @` B)=
    @hausdorff_measure R Y q B.
Proof.
move=>hBset.
pose f:=fun z:Y=>(structure_projective_rotation g z:Y).
pose j:=fun z:Y=>(structure_projective_rotation (invS g) z:Y).
have [hLeft hRight]:=structure_projective_rotation_cancel hS g.
have hLip (h:O):is_metric_lipschitz_bound M (fun z:Y=>(structure_projective_rotation h z:Y)) 1%R.
  split; first exact:ler01.
  move=>x y hx hy; rewrite mul1r.
  rewrite (structure_projective_rotation_isometry h hx hy); exact:lexx.
have hForward:=@hausdorff_lipschitz_on_bound R Y Y M f 1%R q B (hLip g) hBset.
have hImage:f @` B `<=` M.
  move=>z [x hx <-]; exact:structure_projective_rotation_member (hBset x hx).
have hBackward:=@hausdorff_lipschitz_on_bound R Y Y M j 1%R q (f @` B)
  (hLip (invS g)) hImage.
have hCancel:j @` (f @` B)=B.
  apply/seteqP; split=>z.
  - move=>[w [x hx <-] <-]; by rewrite /j /f hLeft.
  - move=>hz; exists (f z); last exact:hLeft z.
    by exists z.
rewrite hCancel expr1n mul1e in hBackward.
rewrite expr1n mul1e in hForward.
by apply/eqP; rewrite eq_le hForward hBackward.
Qed.

(** Source for [structure_projective_restricted_hausdorff_invariant]:
    the displayed invariant measure H^m restricted
    to T(U), Federer 3.3.4, p. 290. The
    image identity holds for all test subsets;
    no finite-mass premise is used for invariance. *)
Theorem structure_projective_restricted_hausdorff_invariant (g:O) q:
  measure_pushforward (fun z:Y=>(structure_projective_rotation g z:Y))
    (measure_restrict (@hausdorff_measure R Y q) M)=
    measure_restrict (@hausdorff_measure R Y q) M.
Proof.
pose f:=fun z:Y=>(structure_projective_rotation g z:Y).
pose j:=fun z:Y=>(structure_projective_rotation (invS g) z:Y).
have [hLeft hRight]:=structure_projective_rotation_cancel hS g.
apply:funext=>B.
have hImage:f @` (M `&` f @^-1` B)=M `&` B.
  apply/seteqP; split=>z.
  - move=>[x [hx hfx] <-]; split=>//; exact:structure_projective_rotation_member hx.
  - move=>[hz hBz]; exists (j z).
    + split; first exact:structure_projective_rotation_member hz.
      change (B (f (j z))); by rewrite /f /j hRight.
    + exact:hRight z.
change (@hausdorff_measure R Y q (M `&` f @^-1` B)=
  @hausdorff_measure R Y q (M `&` B)).
rewrite -hImage; symmetry; apply:structure_projective_rotation_hausdorff.
by move=>x [hx _].
Qed.
End Invariance.
