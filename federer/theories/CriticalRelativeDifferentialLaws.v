(** Federer (1969), 3.4.2(4), (6)–(7), pp. 311–313: relative
    differential values and positive scaling of tangent tests. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP TangentConeUP TangentConeBasic RelativeDifferentialUP
  RelativeDifferential RelativeDifferentialRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_relative_differential_from_extension]: supporting
    the chain formula and derivative tests of 3.4.2(6)–(7), pp. 312–313.
    An actual ambient differential of an extension restricts to the
    original relative differential on precisely Tan(S,a), by 3.1.22.
    The partial map is a local witness, not a new global choice. *)
Theorem critical_relative_differential_from_extension (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U S:set X) (F f:X->Y) a (D:Hom X Y):
  S a ->(forall x,S x ->U x ->f x=F x) ->
  has_norm_differential NX NY U F a D ->
  exists L:partial_function X Y,
    partial_function_graph (relative_norm_differential hNX hNY S S f) a L /\
    forall z y,partial_function_graph L z y <->norm_tangent_cone NX S a z /\D z=y.
Proof.
move=>ha hAgree hD.
have [L hL]:=tangent_differential_restriction_exists NX S a D.
exists L;split;last exact:hL.
apply:(@relative_norm_differential_graph R X Y NX NY hNX hNY S S f a L).2.
split;first exact:(@subset_closure (real_norm_metric_space hNX) S a ha).
exists U,F,D;split;first exact:hD.
split;last exact:hL.
move=>x hx hxU;split;[exact:hx|exact:hAgree x hx hxU].
Qed.

(** Source for [critical_relative_differential_positive_scale]: the
    normalization of tangent test vectors in ζ, 3.4.2(4), p. 311,
    and the chain estimate in (6), p. 312. Positive scaling stays in
    the tangent cone and scales the actual relative derivative value. *)
Lemma critical_relative_differential_positive_scale (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (S:set X) (f:X->Y) a (L:partial_function X Y) z y (c:R):
  partial_function_graph (relative_norm_differential hNX hNY S S f) a L ->
  partial_function_graph L z y ->0<=c ->partial_function_graph L (c*:z) (c*:y).
Proof.
move=>hOuter hInner hc.
have [_ [U [F [D [hD [hAgree hL]]]]]]:=
  (@relative_norm_differential_graph R X Y NX NY hNX hNY S S f a L).1 hOuter.
have [hTan hValue]:=(hL z y).1 hInner.
apply:(hL (c*:z) (c*:y)).2;split.
- exact:(@norm_tangent_nonnegative_scale R X NX hNX S a z c hTan hc).
- exact:(eq_trans (linZ (hom_linear D) c z)
    (congr1 (fun w=>c*:w) hValue)).
Qed.

(** Source for [critical_relative_differential_zero_value]: supporting
    the zero tangent-vector case in the normalization used for
    3.4.2(6), p. 312. Every actual relative derivative value at zero
    is zero, because its ambient extension is linear. *)
Lemma critical_relative_differential_zero_value (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (S:set X) (f:X->Y) a (L:partial_function X Y) y:
  partial_function_graph (relative_norm_differential hNX hNY S S f) a L ->
  partial_function_graph L 0 y ->y=0.
Proof.
move=>hOuter hInner.
have [_ [U [F [D [hD [hAgree hL]]]]]]:=
  (@relative_norm_differential_graph R X Y NX NY hNX hNY S S f a L).1 hOuter.
have hValue:=(hL 0 y).1 hInner.
by rewrite linear0 in hValue;exact:esym hValue.2.
Qed.
