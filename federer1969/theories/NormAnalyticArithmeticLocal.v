(** Federer (1969), 3.1.24, p. 240: analytic
    arithmetic on a common actual domain, used for the
    explicit quadratic expression for the inverse majorant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticDomain NormAnalyticArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_at_common_domain_add]: supporting
    the sum in the inverse expression in Federer 3.1.24,
    p. 240. Analyticity of both summands on A gives
    analyticity of their sum on A, identifying A intersect A. *)
Lemma norm_analytic_at_common_domain_add (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f g:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY A g a ->
  @norm_analytic_at R X Y NX NY hNX hNY A (fun x=>f x+g x) a.
Proof.
move=>hf hg.
exact (@norm_analytic_at_domain_enlargement R X Y NX NY hNX hNY (fun x=>A x /\ A x) A
  (fun x=>f x+g x) a (fun x hx=>hx.1)
  (@norm_analytic_at_add R X Y NX NY hNX hNY A A f g a hf hg)).
Qed.

(** Source for [norm_analytic_at_negate]: changing the sign
    of an analytic function preserves analyticity, supporting
    the square-root subtraction in Federer 3.1.24, p. 240. *)
Lemma norm_analytic_at_negate (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY A (fun x=> -f x) a.
Proof.
move=>hf.
have hh:=@norm_analytic_at_scale R X Y NX NY hNX hNY A f a (-1) hf.
have he:(fun x=> -1*:f x)=(fun x=> -f x).
  apply:funext=>x; exact: scaleN1r.
by rewrite he in hh.
Qed.

(** Source for [norm_analytic_at_subtract]: subtraction on a
    common actual domain, supporting the quadratic scalar inverse
    in Federer 3.1.24, p. 240. *)
Lemma norm_analytic_at_subtract (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f g:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY A g a ->
  @norm_analytic_at R X Y NX NY hNX hNY A (fun x=>f x-g x) a.
Proof.
move=>hf hg.
exact (@norm_analytic_at_common_domain_add R X Y NX NY hNX hNY A f (fun x=> -g x) a hf
  (@norm_analytic_at_negate R X Y NX NY hNX hNY A g a hg)).
Qed.
