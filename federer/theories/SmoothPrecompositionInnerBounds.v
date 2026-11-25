(** Federer (1969), 4.1.7, p. 359:
    one finite bound controls the original
    inner derivatives on a compact source
    index. Reuse smooth-field existence and
    the original compact derivative bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ContinuousMultilinearNorm Hom RealNormUP NormDifferentialUP NormRegularity NormSmoothFields
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  SmoothCompactSet NormCompactFunctionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothPrecompositionInnerBounds.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable A:X->Prop.
Variable f:X->Y.
Hypothesis hf:norm_class_all_orders hNX hNY A f.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).

(** Source for [smooth_precomposition_inner_compact_bound]:
    the actual original differential fields
    of the fixed inner map have
    a finite common compact bound, supporting
    precomposition continuity in Federer 4.1.7,
    p. 359. No derivative bound
    is assumed as a numbered conclusion. *)
Theorem smooth_precomposition_inner_compact_bound (K:smooth_compact_set hNX A) p:
  exists df:forall j,X->Z j,
    (forall j x,A x->has_norm_higher_differential NX ez ZN A f j x (df j x)) /\
    exists C:R,0<=C /\forall j,(j<=p)%N->forall x,smooth_compact_carrier K x->
      @ZN j (df j x)<=C.
Proof.
have [df hdf]:=norm_smooth_fields_exist hf.
exists df;split;first by move=>j x hx;exact:(hdf j).1 x hx.
have hChoice (j:'I_p.+1):exists C:R,0<C /\forall x,smooth_compact_carrier K x->
    @ZN j (df j x)<=C.
  exact:(@norm_class_zero_compact_bounded R X (Z j) NX (@ZN j) hNX
    (continuous_multilinear_norm_is_norm hNY (@ContinuousMultilinear.laws R j X Y NX NY hNX hNY))
    A (smooth_compact_carrier K) (df j) (smooth_compact_is_compact K)
    (smooth_compact_in_domain K) (hdf j).2).
have [c hc]:=choice hChoice.
pose C:=\sum_(j:'I_p.+1) c j.
have hC:0<=C by apply:sumr_ge0=>j _;exact:ltW (hc j).1.
exists C;split=>// j hj x hx.
have hj':(j<p.+1)%N by rewrite ltnS.
pose index:'I_p.+1:=Ordinal hj'.
apply:le_trans ((hc index).2 x hx) _.
rewrite /C (bigD1 index) //= lerDl.
apply:sumr_ge0=>k _;exact:ltW (hc k).1.
Qed.
End SmoothPrecompositionInnerBounds.
