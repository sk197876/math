(** Federer (1969), 3.1.21, p. 234: evaluation of the
    derivative in a varying tangent vector preserves the common
    differentiability class. The first-order space is abstract. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearOne NormOperatorNormUP NormBoundedBilinearUP NormRegularity NormRegularityBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Evaluation.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Variable ev:{ffun 'I_1->X}->Hom Z Y.
Variable ZN:Z->R.
Hypothesis hZ:is_continuous_multilinear_space NX NY ev ZN.
Local Notation op := (@continuous_multilinear_one_operator R X Y Z NX NY ev ZN hZ).

(** Source for [norm_first_evaluation_bounded_bilinear]:
    supporting the map (a,v) -> Df(a)v in the tangent-bundle
    assertion of Federer 3.1.21, p. 234. Evaluation is
    bilinear and bounded by the product of the operator and
    vector norms, by the laws of the supplied operator space. *)
Lemma norm_first_evaluation_bounded_bilinear :
  norm_bounded_bilinear ZN NX NY (fun z x=>op z x).
Proof.
split.
- split.
  + move=>x c z w.
    change (ev [ffun i=>x] (c*:z+w)=c*:ev [ffun i=>x] z+ev [ffun i=>x] w).
    exact: linearP.
  + move=>z c x y; exact: linearP.
- exists 1; split; first exact: ler01.
  move=>z x; rewrite mul1r.
  exact (@norm_operator_bound R X Y NX NY (op z) (ZN z)
    (@continuous_multilinear_one_norm_laws R X Y Z NX NY ev ZN hZ z) x).
Qed.

(** Source for [norm_class_first_evaluation]: the class-(k-1)
    regularity of the derivative evaluation in bundle charts,
    Federer 3.1.21, p. 234. Both arguments may vary; no
    construction of the operator space is unfolded. *)
Lemma norm_class_first_evaluation (P:lmodType R) (NP:P->R)
    (hNP:is_real_norm NP) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:P->Prop) (F:P->Z) (V:P->X) k :
  norm_class hNP (continuous_multilinear_norm_is_norm hNY hZ) A F k ->
  norm_class hNP hNX A V k ->
  norm_class hNP hNY A (fun x=>op (F x) (V x)) k.
Proof.
move=>hF hV.
exact: norm_class_bilinear norm_first_evaluation_bounded_bilinear hF hV.
Qed.
End Evaluation.
