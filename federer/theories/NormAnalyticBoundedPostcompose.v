(** Federer (1969), 3.4.12, pp. 338–339:
    scalar coordinates of a complex analytic map remain
    real analytic. This missing interface connection applies
    the existing bounded linear and composition theorems of
    3.1.24, pp. 239–240, without repeating their proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormAnalyticUP
  NormOpenDomainLaws NormAnalyticLinear NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_analytic_bounded_postcompose]: compose
    an actual analytic function with a bounded linear
    coordinate map, 3.1.24, pp. 239–240,
    as used in 3.4.12, pp. 338–339.
    The original source domain and normed targets remain. *)
Theorem norm_analytic_bounded_postcompose (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (f:X->Y) (L:Hom Y Z):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  norm_bounded_linear NY NZ L ->
  @norm_analytic R X Z NX NZ hNX hNZ A (fun x=>L (f x)).
Proof.
move=>hf hL.
have hLinear:=norm_bounded_linear_analytic hNY hNZ
  (fun y (_:True)=>norm_full_domain_interior NY y) hL.
exact:(norm_analytic_compose_on (fun x _=>I) hf hLinear).
Qed.
