(** Federer (1969), 3.4.8(5), p. 328:
    derivative evaluation is jointly continuous in its
    actual multilinear form and all of its arguments.
    Repeated bounded bilinear contraction proves the assertion
    through the public multilinear interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearEvaluationBound
  ContinuousMultilinearSuccessorContraction MultilinearArguments MultilinearSuccessorArguments
  NormBoundedLinearTopology BoundedBilinearContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [multilinear_evaluation_continuous_factors]:
    the actual finite derivative evaluations used for joint
    pullback continuity in 3.4.8(5), p. 328.
    The form and every argument vary with an arbitrary
    topological parameter. The empty tuple remains. *)
Theorem multilinear_evaluation_continuous_factors (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall k,{ffun 'I_k->X}->Hom (Z k) Y)
    (ZN:forall k,Z k->R)
    (hZ:forall k,is_continuous_multilinear_space NX NY (@ev k) (@ZN k))
    (P:topologicalType) k (D:P->Z k) (u:P->{ffun 'I_k->X}):
  continuous (fun p:P=>(D p:real_norm_metric_space (continuous_multilinear_norm_is_norm hNY (hZ k)))) ->
  (forall i:'I_k,continuous (fun p:P=>(u p i:real_norm_metric_space hNX))) ->
  continuous (fun p:P=>(ev k (u p) (D p):real_norm_metric_space hNY)).
Proof.
elim:k D u=>[D u hD hU|k ih D u hD hU].
- pose u0:=[ffun _:'I_0=>(0:X)].
  have hBound:=continuous_multilinear_evaluation_bounded hNX (hZ 0%N) u0.
  have hEval:=@norm_bounded_linear_continuous R (Z 0%N) Y (ZN 0%N) NY
    (continuous_multilinear_norm_is_norm hNY (hZ 0%N)) hNY (ev 0%N u0) hBound.
  have hSame:forall p,u p=u0 by move=>p;apply/ffunP=>i;by case:i.
  have ->:(fun p:P=>(ev 0%N (u p) (D p):real_norm_metric_space hNY))=
      (fun p:P=>(ev 0%N u0 (D p):real_norm_metric_space hNY)).
    by apply:funext=>p;rewrite hSame.
  move=>p;exact:(continuous_comp (hD p) (hEval (D p))).
- have [C [hC hCE]]:=continuous_multilinear_successor_contraction_exists hNX (hZ k) (hZ k.+1).
  pose v p:=multilinear_arguments_cast (esym (addn1 k)) (u p).
  pose w p:=@multilinear_arguments_left X k 1 (v p).
  pose x p:=@multilinear_arguments_right X k 1 (v p) ord0.
  have hX:continuous (fun p:P=>(x p:real_norm_metric_space hNX)).
    have hEq:(fun p:P=>x p)=
        (fun p:P=>u p (cast_ord (esym (esym (addn1 k))) (rshift k ord0))).
      by apply:funext=>p;rewrite /x /v /multilinear_arguments_right
        /multilinear_arguments_cast !ffunE.
    rewrite hEq;exact:hU.
  have hCMap:continuous (fun p:P=>(C (D p) (x p):
      real_norm_metric_space (continuous_multilinear_norm_is_norm hNY (hZ k)))).
    exact:(@bounded_bilinear_continuous_factors R (Z k.+1) X (Z k)
      (ZN k.+1) NX (ZN k) (continuous_multilinear_norm_is_norm hNY (hZ k.+1))
      hNX (continuous_multilinear_norm_is_norm hNY (hZ k)) C hC P D x hD hX).
  have hW i:continuous (fun p:P=>(w p i:real_norm_metric_space hNX)).
    have hEq:(fun p:P=>w p i)=
        (fun p:P=>u p (cast_ord (esym (esym (addn1 k))) (lshift 1 i))).
      by apply:funext=>p;rewrite /w /v /multilinear_arguments_left
        /multilinear_arguments_cast !ffunE.
    rewrite hEq;exact:hU.
  have hSmaller:=ih (fun p=>C (D p) (x p)) w hCMap hW.
  have hArguments p:multilinear_successor_arguments (w p) (x p)=u p.
    rewrite /multilinear_successor_arguments /w /x.
    have hOne:[ffun _:'I_1=>multilinear_arguments_right (v p) ord0]=
        multilinear_arguments_right (v p).
      by apply/ffunP=>i;rewrite ffunE (ord1 i).
    rewrite hOne multilinear_arguments_join_split /v.
    apply/ffunP=>i;rewrite /multilinear_arguments_cast !ffunE.
    congr (u p _);exact:val_inj.
  have hSame:(fun p:P=>(ev k (w p) (C (D p) (x p)):real_norm_metric_space hNY))=
      (fun p:P=>(ev k.+1 (u p) (D p):real_norm_metric_space hNY)).
    by apply:funext=>p;rewrite hCE hArguments.
  by rewrite -hSame.
Qed.
