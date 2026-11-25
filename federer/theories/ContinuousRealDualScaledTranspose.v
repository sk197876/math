(** Federer (1969), 4.1.1, p. 346: the real signs in
    distributional differentiation preserve weak continuity.
    This supporting theorem scales the already proved actual
    continuous transpose. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom OpenFamilyTopologyUP ContinuousRealDual ContinuousRealDualTranspose
  WeakLinearEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ScaledTranspose.
Variable R:realType.
Variables E F:lmodType R.
Variables (O:set (set E)) (P:set (set F)).
Hypothesis hO:is_open_family_topology O.
Hypothesis hP:is_open_family_topology P.
Variable L:Hom E F.
Hypothesis hL:open_family_continuous O P L.
Variable c:R.
Local Notation DE := (@continuous_real_dual_space R E O hO).
Local Notation DF := (@continuous_real_dual_space R F P hP).
Local Notation eE := (@continuous_real_dual_evaluation R E O hO).
Local Notation eF := (@continuous_real_dual_evaluation R F P hP).
Local Notation OE := (@continuous_real_dual_weak_opens R E O hO).
Local Notation OF := (@continuous_real_dual_weak_opens R F P hP).
Local Notation tr := (@continuous_real_dual_transpose R E F O P hO hP L hL).

(** Source for [continuous_real_dual_scaled_transpose]: scalar
    multiple of the original transpose, supporting the factors
    -1 and (-1)^i in Federer 4.1.1, p. 346. *)
Definition continuous_real_dual_scaled_transpose:Hom DF DE:=c*:tr.

(** Source for [continuous_real_dual_scaled_transpose_evaluation]:
    the exact evaluation c T(L phi), supporting the signed
    derivative definition in Federer 4.1.1, p. 346. *)
Theorem continuous_real_dual_scaled_transpose_evaluation T x:
  eE (continuous_real_dual_scaled_transpose T) x=c*:eF T (L x).
Proof.
change (eE (c*:tr T) x=c*:eF T (L x)).
have hs:eE (c*:tr T)=c*:eE (tr T) by rewrite linearZ.
have hScale:eE (c*:tr T) x=c*:eE (tr T) x:=congr1 (fun f:Hom E R^o=>f x) hs.
have hEval:=@continuous_real_dual_transpose_evaluation R E F O P hO hP L hL T x.
exact (eq_trans hScale (congr1 (fun y=>c*:y) hEval)).
Qed.

(** Source for [continuous_real_dual_scaled_transpose_weak_continuous]:
    the scaled transpose is weakly continuous, supporting every
    partial differential operator on D' in Federer 4.1.1,
    p. 346. The final source topology is never assumed linear. *)
Theorem continuous_real_dual_scaled_transpose_weak_continuous:
  open_family_continuous OF OE continuous_real_dual_scaled_transpose.
Proof.
change (open_family_continuous OF OE (fun T=>c*:tr T)).
exact:(open_family_continuous_compose
  (@continuous_real_dual_transpose_weak_continuous R E F O P hO hP L hL)
  (weak_linear_evaluation_scaling_continuous (@continuous_real_dual_weak_laws R E O hO) c)).
Qed.
End ScaledTranspose.
