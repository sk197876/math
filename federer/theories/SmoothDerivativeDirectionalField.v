(** Federer (1969), 4.1.1, p. 346: the
    directional differential of D^j phi equals
    D^j(D_v phi). The proof reuses exact field
    differentiation, grouping and symmetry from
    3.1.11, pp. 218–220. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialFields MultilinearArguments MultilinearSuccessorArguments
  MultilinearEvaluationDegreeTransport NormHigherFirstLastExchange SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP SmoothDirectionalHigherFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section DerivativeDirectionalField.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.

(** Source for [smooth_derivative_directional_differential]:
    differentiating the jth differential in v
    gives the jth differential of D_v phi,
    supporting the Taylor limit in Federer
    4.1.1, p. 346. *)
Theorem smooth_derivative_directional_differential j f x:
  U x ->exists L:Hom X (Z j),
    has_norm_differential NX (@ZN j) U (fun y=>@D j y f) x L /\
    L v=@D j x (P f).
Proof.
move=>hx.
have hNext:=@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD j.+1 f x hx.
have [L [hL hLE]]:=@norm_higher_differential_field_step_elim R X Y NX hNX Z evZ ZN
  U (ev f) j (fun y=>@D j y f) x (@D j.+1 x f)
  (fun y hy=>@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD j f y hy) hNext.
exists L; split; first exact hL.
apply:(continuous_multilinear_extensional (hZ j))=>u.
rewrite hLE.
have hFormula:=@smooth_directional_higher_derivative_formula R X Y NX NY hNX hNY U hU E ev D hD v P hP j f x hx u.
have hTransport:=@multilinear_evaluation_degree_transport R X Y Z evZ (fun k=>@D k x f)
  (1+j)%N j.+1 (add1n j) (multilinear_arguments_join [ffun _: 'I_1=>v] u).
rewrite hTransport in hFormula.
have hExchange:=@norm_higher_first_last_exchange R j X Y NX NY hNX hNY Z evZ ZN hZ
  U (ev f) x (@D j.+1 x f) hNext u v.
by rewrite hExchange in hFormula.
Qed.
End DerivativeDirectionalField.
