(** Federer (1969), 4.1.1, pp. 344–345: compact cutoff
    replacement proves density of D in E. This supporting
    assertion supplies the uniqueness in the printed dual
    monomorphism, retaining the original seminorm topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP DirectedSeminormFamilyUP SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothCutoffReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestDensity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).

(** Source for [smooth_test_dense_in_smooth]: every nonempty
    E-open set contains an actual test function, supporting
    the dual monomorphism of Federer 4.1.1, p. 345.
    Empty domains and zero source or target are retained. *)
Theorem smooth_test_dense_in_smooth (A:set E):
  EO A ->(exists f,A f) ->exists g:DT,A (inc g).
Proof.
move=>hA [f hf].
have [[i K] [r [hr hbA]]]:=((smooth_function_topology_laws hD).2 A).1 hA f hf.
pose g:=@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K f.
exists g; apply:hbA.
have he:=@smooth_cutoff_replacement_seminorm_difference R X Y NX NY hNX hNY n b hb U hU
  E ev hE D hD K i f.
by rewrite he.
Qed.
End TestDensity.
