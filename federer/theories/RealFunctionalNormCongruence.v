(** Federer (1969), 4.1.7, p. 357: the
    original pairing identification preserves its dual
    norm. This supporting congruence uses only the
    independent functional norm laws of 2.4.12, p. 87. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [real_functional_norm_pointwise]: equal
    evaluations have the same specified norm, supporting
    the dual identification in Federer 4.1.7, p. 357. *)
Lemma real_functional_norm_pointwise (R:realType) (V:lmodType R)
    (N:V->R) (a b:{linear V->R^o}) c:
  (forall y,a y=b y) ->is_real_functional_norm N a c ->
  is_real_functional_norm N b c.
Proof.
move=>he h; constructor.
- exact:(real_functional_norm_nonnegative h).
- move=>y; rewrite -he; exact:(real_functional_norm_bound h y).
- move=>d hd hb; apply:(real_functional_norm_least h hd)=>y.
  rewrite he; exact:hb.
Qed.
