(** Federer (1969), 3.4.8(6),(7), p. 329:
    nullity does not depend on the normalization
    of the original Haar measure. Prove the
    positive-factor identity from 2.7.7, p. 125,
    and the project's regular-representation uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import TopologicalGroupUP HaarIntegralUP HaarIntegralUniqueness
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeRegularityUP
  FunctionLatticeRegularUniqueness RealIntegralFunctionalUP MeasureUP MeasureScaleIntegral MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [left_haar_measures_positive_multiple]: the
    positive-multiple theorem of 2.7.7, p. 125,
    applied to the actual regular measures used
    in 3.4.8(6),(7), p. 329. *)
Theorem left_haar_measures_positive_multiple (R:realType) (G:topologicalType)
  (mul:G->G->G) (inv:G->G) (unit:G)
  (hG:is_locally_compact_hausdorff_group mul inv unit) (mu nu:set G->\bar R):
  is_left_haar_measure mul mu ->is_left_haar_measure mul nu ->
  exists c:R,0<c /\mu = measure_scale c nu.
Proof.
move=>[lambda [hLambda hMu hRepMu hRegularMu]] [eta [hEta hNu hRepNu hRegularNu]].
have [c hPositive hMultiple]:=left_haar_integral_unique hG hLambda hEta.
exists c;split;first exact:hPositive.
have hScaledMeasure:=measure_scale_is_measure hNu hPositive.
have hScaledRep:=measure_scale_represents hNu hPositive hRepNu.
have hScaledRegular:=measure_scale_regular hNu hPositive hRegularNu.
have hRepMu':is_real_integral_functional mu (@compactly_supported_continuous_functions R G) (fun u=>c*eta u).
  move=>u hu;rewrite -(hMultiple u hu);exact:hRepMu.
apply:funext=>E.
exact:(function_lattice_regular_representation_unique
  (@compactly_supported_continuous_functions_lattice R G) hMu hScaledMeasure
  hRepMu' hScaledRep hRegularMu hScaledRegular E).
Qed.

(** Source for [left_haar_measures_same_null_sets]: Haar
    normalization does not change the exceptional
    null sets in 3.4.8(6),(7), p. 329.
    All subsets are retained. *)
Lemma left_haar_measures_same_null_sets (R:realType) (G:topologicalType)
  (mul:G->G->G) (inv:G->G) (unit:G)
  (hG:is_locally_compact_hausdorff_group mul inv unit) (mu nu:set G->\bar R):
  is_left_haar_measure mul mu ->is_left_haar_measure mul nu ->
  forall E,mu E = 0%E <->nu E = 0%E.
Proof.
move=>hMu hNu E.
have [c [hPositive hEqual]]:=left_haar_measures_positive_multiple hG hMu hNu.
split.
- move=>hZero.
  have hInverse:=congr1 (fun rho:set G->\bar R=>rho E) (measure_scale_inverse nu hPositive).
  by rewrite -hEqual /measure_scale hZero mule0 in hInverse;exact:esym hInverse.
- move=>hZero;by rewrite hEqual /measure_scale hZero mule0.
Qed.
