(** Federer (1969), 3.4.8(9), p. 330:
    the original intersection of the required
    B_j sets is constant on right Q_m
    cosets. Apply the proved original quotient
    integrality and directional witnesses, then
    use the original inverse for the reverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology TopologicalGroupUP TopologicalGroupLaws
  AnalyticGermRing AnalyticScalarsSealed AnalyticRotatedGermIdeal AnalyticReductionActual
  AnalyticReductionFieldInputs AnalyticIntegralRotationDirections
  CommutativeIdealUP CommutativeQuotientSealed OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SuffixCosets.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable m:'I_n.
Local Notation H:=(@analytic_suffix_rotation_group R X B hB n e he m).
Local Notation Bj:=(@analytic_reduction_actual_B R X B hB n e he omega I).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_reduction_suffix_B_stable]: the
    original intersection of B_j is preserved
    by every original Q_m rotation, supporting
    the coset argument of 3.4.8(9), p. 330.
    This deduction needs only a proper
    original ideal; primeness is not required. *)
Theorem analytic_reduction_suffix_B_stable (g:O) (q:H):
  (forall j:'I_n,(m<=j)%N ->Bj j g) ->
  forall j:'I_n,(m<=j)%N ->Bj j (mulO g (set_val q)).
Proof.
move=>hAllB.
pose hMN:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
have hIdeal:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI.
have hProperRot:=@analytic_rotated_germ_ideal_proper R X B hB n e he I g hProper.
pose realG:=@AnalyticScalars.map R X NX hNX 0.
pose C:=@CommutativeIdealQuotient.space R G realG Ig hIdeal hProperRot.
pose pi:=@CommutativeIdealQuotient.projection R G realG Ig hIdeal hProperRot.
have hPi:=@CommutativeIdealQuotient.laws R G realG Ig hIdeal hProperRot.
have hIntegral:=@analytic_reduction_quotient_integral R X B hB n e he hON omega hDual
  I hI hProper g C pi hPi m hMN hAllB.
exact:(@analytic_integral_suffix_rotation_B R X B hB n e he hON omega hDual I g C pi hPi
  m hMN hIntegral mulO invO unitO hO mulH invH unitH hH q).
Qed.

(** Source for [analytic_reduction_B_suffix_coset]: the
    exact right-coset equivalence used when
    integrating the original B_j intersection
    minus C_m, 3.4.8(9), p. 330.
    The selected inverse returns the
    original g and all original indices. *)
Theorem analytic_reduction_B_suffix_coset (g:O) (q:H):
  (forall j:'I_n,(m<=j)%N ->Bj j (mulO g (set_val q))) <->
  (forall j:'I_n,(m<=j)%N ->Bj j g).
Proof.
split.
- move=>hAllB.
  have hRestored:=@analytic_reduction_suffix_B_stable (mulO g (set_val q)) (invH q) hAllB.
  have hGroup:=topological_group_laws (lch_group_topological
    (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO)).
  by rewrite (subgroup_restriction_inv hH) (@group_mulgK O mulO invO unitO hGroup (set_val q) g) in hRestored.
- exact:(@analytic_reduction_suffix_B_stable g q).
Qed.
End SuffixCosets.
