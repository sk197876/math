(** Supporting finite linear calculus for Federer (1969), 3.1.1(5),
    p. 210, and the coordinate formulas on p. 211. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp functions lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_postcompose]: linear scalarisation
    and reconstruction used in Federer 3.1.1(5), p. 210. A bounded linear
    map can be applied to the value and the differential on the same domain. *)
Lemma norm_differential_postcompose (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) (M : Hom Y Z) :
  has_norm_differential NX NY A f a L -> norm_bounded_linear NY NZ M ->
  has_norm_differential NX NZ A (fun x => M (f x)) a (hom_comp M L).
Proof.
move=> hf hM; constructor; first exact: norm_differential_interior hf.
- exact: (norm_bounded_linear_compose (norm_differential_bounded hf) hM).
- move=> e he; have [C [hC hbound]] := hM.
  have hden : 0 < C+1 by lra.
  have hp : 0 < e/(C+1) by rewrite divr_gt0.
  have [d [hd hb]] := norm_differential_remainder hf hp.
  exists d; split=> // h ha hh.
  rewrite hom_compE -!linearB.
  apply: le_trans (hbound _) _.
  apply: le_trans (ler_wpM2l hC (hb h ha hh)) _.
  have hn := real_seminorm_nonnegative hNX.1 h.
  have heq : e/(C+1)*(C+1) = e by rewrite divfK // gt_eqF.
  have hp0 := ltW hp.
  have hc : C*(e/(C+1)) <= e by nra.
  rewrite mulrA; apply: ler_wpM2r=> //; exact hc.
Qed.

(** Source for [norm_differential_finite_sum]: finite addition of
    differentials in the coordinate argument of Federer 3.1.1(5), p. 210.
    An explicit interior condition handles an empty indexing family. *)
Lemma norm_differential_finite_sum (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (a : X)
    (I : finType) (P : pred I) (f : I -> X -> Y) (L : I -> Hom X Y) :
  norm_domain_interior NX A a ->
  (forall i, P i -> has_norm_differential NX NY A (f i) a (L i)) ->
  has_norm_differential NX NY A (\sum_(i | P i) f i) a (\sum_(i | P i) L i).
Proof.
move=> ha hf; elim/big_rec2: _=> [|i g M hi hg].
- exact: (@norm_differential_constant R X Y NX NY hNX hNY A a (0:Y) ha).
- exact: (norm_differential_add hNY (hf i hi) hg).
Qed.

(** Source for [norm_differentiable_finite_sum]: existence form of
    the finite-sum rule used in Federer 3.1.1(5), p. 210. *)
Lemma norm_differentiable_finite_sum (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (a : X)
    (I : finType) (f : I -> X -> Y) :
  norm_domain_interior NX A a ->
  (forall i, norm_differentiable_at NX NY A (f i) a) ->
  norm_differentiable_at NX NY A (\sum_i f i) a.
Proof.
move=> ha hf.
pose L := fun i => sval (constructive_indefinite_description (hf i)).
exists (\sum_i L i); apply: (norm_differential_finite_sum hNX hNY ha)=> i _.
exact: (svalP (constructive_indefinite_description (hf i))).
Qed.
