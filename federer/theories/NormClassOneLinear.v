(** Federer (1969), 3.1.1(3), p. 210: bounded linear maps have
    constant differentials. Supporting the coordinate and constant-map
    regression cases of the normal-form theorem in 3.1.18, pp. 229–230. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormClassOneUP NormClassOneLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_linear_field]: the constant actual
    differential of a bounded linear map, Federer 3.1.1(3), p. 210,
    supporting the coordinate-map case of 3.1.18, p. 229. *)
Lemma norm_class_one_linear_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (L:Hom X Y) :
  (forall x, A x -> norm_domain_interior NX A x) -> norm_bounded_linear NX NY L ->
  is_norm_class_one_field NX NY A L (fun _=>L).
Proof.
move=>hA hL.
have hd x (hx:A x):has_norm_differential NX NY A L x L.
  exact (@norm_differential_linear R X Y NX NY hNX hNY A x L (hA x hx) hL).
constructor=>//.
- exact (@norm_everywhere_differentiable_class_zero R X Y NX NY hNY A L (fun _=>L) hd).
- move=>x hx e he; exists 1; split; first exact: ltr01.
  move=>h hh hs v; rewrite subrr hom_zeroE (real_seminorm_zero hNY.1).
  apply: mulr_ge0; first exact: ltW he.
  exact (real_seminorm_nonnegative hNX.1 v).
Qed.

(** Source for [norm_class_one_constant_field]: constant maps have
    zero actual differential, supporting the rank-zero case of
    Federer 3.1.18, p. 229, by 3.1.1's differential definition. *)
Lemma norm_class_one_constant_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) c :
  (forall x, A x -> norm_domain_interior NX A x) ->
  is_norm_class_one_field NX NY A (fun _=>c) (fun _=>0).
Proof.
move=>hA.
have hd x (hx:A x):has_norm_differential NX NY A (fun _=>c) x 0.
  exact (@norm_differential_constant R X Y NX NY hNX hNY A x c (hA x hx)).
constructor=>//.
- exact (@norm_everywhere_differentiable_class_zero R X Y NX NY hNY A (fun _=>c) (fun _=>0) hd).
- move=>x hx e he; exists 1; split; first exact: ltr01.
  move=>h hh hs v; rewrite subrr hom_zeroE (real_seminorm_zero hNY.1).
  apply: mulr_ge0; first exact: ltW he.
  exact (real_seminorm_nonnegative hNX.1 v).
Qed.
