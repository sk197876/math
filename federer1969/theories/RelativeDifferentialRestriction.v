(** Federer (1969), 3.1.22, p. 235: a relative
    differential is a partial function on exactly the tangent cone. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom PartialFunctionUP TangentConeUP RelativeDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [tangent_differential_restriction_exists]: supporting
    the restriction Dg(a)|Tan(S,a) in Federer 3.1.22,
    p. 235. The existence proof supplies a single-valued
    partial graph and introduces no value outside the cone. *)
Lemma tangent_differential_restriction_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (S:set X) a (D:Hom X Y) :
  exists L:partial_function X Y,is_tangent_differential_restriction NX S a D L.
Proof.
have hu v y z:(norm_tangent_cone NX S a v /\ D v=y) ->
    (norm_tangent_cone NX S a v /\ D v=z) -> y=z.
  move=>[_ hy] [_ hz]; exact (eq_trans (esym hy) hz).
exists (@Build_partial_function X Y (fun v y=>norm_tangent_cone NX S a v /\ D v=y) hu).
by move=>v y.
Qed.

(** Source for [tangent_differential_restriction_domain]: the
    exact domain Tan(S,a) of the relative differential in
    Federer 3.1.22, p. 235. *)
Lemma tangent_differential_restriction_domain (R:realType) (X Y:lmodType R)
    (NX:X->R) (S:set X) a (D:Hom X Y) (L:partial_function X Y) :
  is_tangent_differential_restriction NX S a D L ->
  partial_function_domain L=norm_tangent_cone NX S a.
Proof.
move=>hL; apply/seteqP; split=>v.
- move=>[y hy]; exact ((hL v y).1 hy).1.
- move=>hv; exists (D v); apply: (hL v (D v)).2; by split.
Qed.
