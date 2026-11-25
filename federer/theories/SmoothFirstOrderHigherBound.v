(** Federer (1969), 4.1.7, p. 356: control
    the original exterior derivative by one additional
    derivative of its input. Reuse the isometric
    grouping and bounded target-composition laws from
    3.1.11, pp. 219–221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearPostcompose
  NormHigherDifferentialUP NormHigherDifferentialPostcompose NormHigherDifferentialUnique SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFirstDerivativeGrouping SmoothFirstOrderUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothFirstOrderHigherBound.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:X->Prop.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation eJ := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation Q := (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ).
Local Notation eQ := (fun j=>@ContinuousMultilinear.evaluation R j X Z NX NZ hNX hNZ).
Local Notation QN := (fun j=>@ContinuousMultilinear.norm R j X Z NX NZ hNX hNZ).
Local Notation hQ := (fun j=>@ContinuousMultilinear.laws R j X Z NX NZ hNX hNZ).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hJ 1%N)).
Local Notation W := (fun j=>@ContinuousMultilinear.space R j X (J 1%N) NX (@JN 1%N) hNX hN1).
Local Notation eW := (fun j=>@ContinuousMultilinear.evaluation R j X (J 1%N) NX (@JN 1%N) hNX hN1).
Local Notation WN := (fun j=>@ContinuousMultilinear.norm R j X (J 1%N) NX (@JN 1%N) hNX hN1).
Local Notation hW := (fun j=>@ContinuousMultilinear.laws R j X (J 1%N) NX (@JN 1%N) hNX hN1).
Variable D:forall j,X->Hom E (J j).
Variable G:forall j,X->Hom F (Q j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X Z NX NZ hNX hNZ U F fv G.
Variable M:Hom (J 1%N) Z.
Hypothesis hM:norm_bounded_linear (@JN 1%N) NZ M.
Variable P:Hom E F.
Hypothesis hP:is_smooth_first_order_operator U fv D M P.

(** Source for [smooth_first_order_total_values]: exact
    equality of the zero-normalized representatives,
    supporting Federer 4.1.7, p. 356. *)
Lemma smooth_first_order_total_values f:
  fv (P f)=(fun x=>M (@D 1%N x f)).
Proof.
apply:funext=>x; case:(pselect (U x))=>[hx|hx]; first exact:hP.
by rewrite (smooth_function_evaluation_outside hF _ hx)
  (smooth_derivative_outside hD 1%N f hx) linear0.
Qed.

(** Source for [smooth_first_order_higher_bound]: each
    output derivative has a finite bound by the
    next input derivative, supporting the original
    operator continuity in Federer 4.1.7, p. 356. *)
Theorem smooth_first_order_higher_bound j:
  exists C:R,0<=C /\forall f x,U x->
    @QN j (@G j x (P f))<=C * @JN j.+1 (@D j.+1 x f).
Proof.
have [T [hTN hT]]:=smooth_first_derivative_grouping_exists hD.
have [A [hA hAb]]:=@continuous_multilinear_postcompose_family_exists R X (J 1%N) Z
  NX (@JN 1%N) NZ W Q eW WN eQ QN hW hQ M hM.
have [C [hC hb]]:=hAb j.
exists C; split=>// f x hx.
have hField y hy:
    has_norm_higher_differential NX eW WN U (fun t=>@D 1%N t f) j y
      (T j (@D (1+j)%N y f)):=hT j f y hy.
have hTarget:=@norm_higher_differential_field_postcompose R X (J 1%N) Z
  NX (@JN 1%N) NZ hNX hN1 hNZ W Q eW WN eQ QN hW hQ M A hA hAb U
  (fun y=>@D 1%N y f) j (fun y=>T j (@D (1+j)%N y f)) hField x hx.
have hActual:=smooth_derivative_exact hG j (P f) hx.
rewrite smooth_first_order_total_values in hActual.
have hSame:=norm_higher_differential_unique hNX hNZ hQ hActual hTarget.
rewrite hSame.
have hEst:=hb (T j (@D (1+j)%N x f)).
have hNext:@JN (1+j)%N (@D (1+j)%N x f)=@JN j.+1 (@D j.+1 x f).
  by rewrite add1n.
rewrite hTN hNext in hEst; exact:hEst.
Qed.
End SmoothFirstOrderHigherBound.
