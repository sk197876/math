(** Federer (1969), 3.1.24, p. 238: each
    Taylor coefficient is a continuous homogeneous polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialSymmetricForm HomogeneousPolynomialFunctions
  PolynomialDiagonalNorm NormRegularity NormRegularityOperations NormClassInfinityMultilinearDiagonal
  NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_taylor_homogeneous_coefficient]: the
    implication (3) to (4) in Federer 3.1.24,
    p. 238. The actual mth differential is a
    bounded symmetric form; its normalized diagonal is a homogeneous
    polynomial and is smooth on the whole normed source space.
    Degree zero and arbitrary-dimensional spaces are retained. *)
Theorem norm_taylor_homogeneous_coefficient (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (f:X->Y) m a
    (z:@ContinuousMultilinear.space R m X Y NX NY hNX hNY) :
  has_norm_higher_differential NX
    (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
    (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY) U f m a z ->
  @is_homogeneous_polynomial R X Y m
    (fun v=>(m`!)%:R^-1 *: @ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY [ffun i=>v] z) /\
  norm_class_all_orders hNX hNY (fun _=>True)
    (fun v=>(m`!)%:R^-1 *: @ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY [ffun i=>v] z).
Proof.
move=>hz.
pose Z:=fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY.
pose ev:=fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY.
have [phi [he hnorm]]:=@norm_higher_differential_symmetric_form_exists R m X Y NX NY hNX hNY
  Z ev ZN hZ U f a z hz.
split.
- exists phi=>v; rewrite sform_polynomial_diagonal_value he.
  congr (_*:@ev m _ z); apply/ffunP=>i; by rewrite !ffunE tnth_mktuple.
- move=>k.
  have hd:=@norm_class_infinity_multilinear_diagonal R X Y NX NY hNX hNY Z ev ZN hZ
    (fun _=>True) (fun x _=>norm_full_domain_interior NX x) m z k.
  exact (norm_class_scale ((m`!)%:R)^-1 hd).
Qed.
