(** Federer (1969), 4.1.7, pp. 355–356: continuous
    linear coefficient operations commute with all smooth
    derivatives. The proof uses the actual higher
    differential and its uniqueness from 3.1.11,
    pp. 219–220. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearPostcompose
  NormHigherDifferentialPostcompose NormHigherDifferentialUnique
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTargetOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothTargetDerivatives.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:X->Prop.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation Pjet := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation Qjet := (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ).
Local Notation ep := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation eq := (fun j=>@ContinuousMultilinear.evaluation R j X Z NX NZ hNX hNZ).
Local Notation PN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation QN := (fun j=>@ContinuousMultilinear.norm R j X Z NX NZ hNX hNZ).
Local Notation hPjet := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hQjet := (fun j=>@ContinuousMultilinear.laws R j X Z NX NZ hNX hNZ).
Variable D:forall j,X->Hom E (Pjet j).
Variable G:forall j,X->Hom F (Qjet j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X Z NX NZ hNX hNZ U F fv G.
Variable L:Hom Y Z.
Hypothesis hL:norm_bounded_linear NY NZ L.
Variable P:Hom E F.
Hypothesis hP:is_smooth_target_operator U ev fv L P.

(** Source for [smooth_target_operator_total_values]:
    equality of the actual zero-normalized representatives,
    supporting the original coefficient action in
    Federer 4.1.7, pp. 355–356. *)
Lemma smooth_target_operator_total_values f:
  fv (P f)=(fun x=>L (ev f x)).
Proof.
apply:funext=>x; case:(pselect (U x))=>[hx|hx]; first exact:hP.
by rewrite (smooth_function_evaluation_outside hF _ hx)
  (smooth_function_evaluation_outside hE _ hx) linear0.
Qed.

(** Source for [smooth_target_derivative_family_exists]:
    every original derivative commutes with the same
    bounded coefficient map, supporting continuity of
    the current operations in Federer 4.1.7,
    pp. 355–356. The multilinear lifts and their bounds
    are proved to exist, not assumed. *)
Theorem smooth_target_derivative_family_exists:
  exists K:forall j,Hom (Pjet j) (Qjet j),
    (forall j z u,@eq j u (K j z)=L (@ep j u z)) /\
    (forall j,norm_bounded_linear (@PN j) (@QN j) (K j)) /\
    forall j f x,U x->@G j x (P f)=K j (@D j x f).
Proof.
have [K [hK hKb]]:=@continuous_multilinear_postcompose_family_exists R X Y Z NX NY NZ
  Pjet Qjet ep PN eq QN hPjet hQjet L hL.
exists K; split=>//; split=>// j f x hx.
apply:(@norm_higher_differential_unique R X Z NX NZ hNX hNZ Qjet eq QN hQjet
  U (fun x=>L (ev f x)) j x).
- have h:=smooth_derivative_exact hG j (P f) hx.
  by rewrite smooth_target_operator_total_values in h.
- exact:(@norm_higher_differential_field_postcompose R X Y Z NX NY NZ hNX hNY hNZ
    Pjet Qjet ep PN eq QN hPjet hQjet L K hK hKb U (ev f) j
    (fun t=>@D j t f) (fun t ht=>smooth_derivative_exact hD j f ht) x hx).
Qed.
End SmoothTargetDerivatives.
