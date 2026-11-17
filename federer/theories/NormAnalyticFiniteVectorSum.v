(** Federer (1969), 3.4.12, p. 339: finite complex
    coefficient sums use the vector-valued analytic addition
    and constant laws already proved in 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets functions.
From Federer Require Import RealNormUP NormDifferentialUP NormAnalyticUP
  NormAnalyticOperations NormAnalyticConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_finite_vector_sum]: finite sums
    preserve analyticity in the original normed target, supporting
    the complex double-coefficient product in 3.4.12, p. 339.
    The open-domain premise includes an empty family. *)
Lemma norm_analytic_finite_vector_sum (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (I:finType) (f:I->X->Y):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,@norm_analytic R X Y NX NY hNX hNY A (f i)) ->
  @norm_analytic R X Y NX NY hNX hNY A (fun x=>\sum_i f i x).
Proof.
move=>hOpen hf.
have hSum:@norm_analytic R X Y NX NY hNX hNY A (\sum_i f i).
  elim/big_ind:_=>[|g h hg hh|i _].
  - exact:(@norm_constant_analytic R X Y NX NY hNX hNY A hOpen 0).
  - exact:norm_analytic_add hg hh.
  - exact:hf.
apply:(@norm_analytic_domain_agreement R X Y NX NY hNX hNY A
  (\sum_i f i) (fun x=>\sum_i f i x) _ hSum)=>x hx.
by elim/big_rec2:_=>[|i y F _ <-].
Qed.
