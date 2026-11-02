(** Federer (1969), 3.1.24, pp. 237–238: analytic
    operator bounds imply the factorial-normalized diagonal bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormAnalyticUP NormMultilinearUnitBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_diagonal]: the implication (1)
    to (2) of Federer 3.1.24, pp. 237–238,
    using exactly the same neighbourhood and finite constant.
    No completeness hypothesis is needed for this implication. *)
Theorem norm_analytic_diagonal (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_diagonal_analytic_at R X Y NX NY hNX hNY A f a.
Proof.
move=>[U [c [ha [hUA [hf hb]]]]].
exists U,c; split; first exact ha.
split; first exact hUA.
split; first exact hf.
move=>m hm x hx z hz v hv.
have hu i:NX ([ffun j:'I_m=>v] i)<=1 by rewrite ffunE.
exact (@norm_multilinear_normalized_unit_bound R m X Y
  (@ContinuousMultilinear.space R m X Y NX NY hNX hNY) NX NY hNX hNY
  (@ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY)
  (@ContinuousMultilinear.norm R m X Y NX NY hNX hNY)
  (@ContinuousMultilinear.laws R m X Y NX NY hNX hNY) z [ffun i=>v] (c^+m)
  hu (hb m hm x hx z hz)).
Qed.
