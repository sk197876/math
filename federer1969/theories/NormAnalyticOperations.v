(** Federer (1969), 3.1.24, pp. 239–240: analytic calculus
    on prescribed actual domains, supporting the analytic chart assertions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticDomain
  NormAnalyticComposition NormAnalyticArithmeticLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_analytic_open_restriction]: restriction to an
    open subdomain in the analytic chart assertions of 3.1.24, p. 240. *)
Lemma norm_analytic_open_restriction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A U:X->Prop) (f:X->Y) :
  (forall x,U x -> A x) -> (forall x,U x -> norm_domain_interior NX U x) ->
  @norm_analytic R X Y NX NY hNX hNY A f -> @norm_analytic R X Y NX NY hNX hNY U f.
Proof.
move=>hUA hU hf a ha.
exact (@norm_analytic_at_domain_enlargement R X Y NX NY hNX hNY (fun x=>A x /\ U x) U f a
  (fun x hx=>hx.2) (@norm_analytic_at_open_restriction R X Y NX NY hNX hNY A U f a ha hU (hf a (hUA a ha)))).
Qed.

(** Source for [norm_analytic_compose_on]: analytic composition
    on an open prescribed source domain, 3.1.24, pp. 239–240. *)
Lemma norm_analytic_compose_on (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->Z) :
  (forall x,A x -> B (f x)) ->
  @norm_analytic R X Y NX NY hNX hNY A f -> @norm_analytic R Y Z NY NZ hNY hNZ B g ->
  @norm_analytic R X Z NX NZ hNX hNZ A (fun x=>g (f x)).
Proof.
move=>hAB hf hg a ha.
exact (@norm_analytic_at_domain_enlargement R X Z NX NZ hNX hNZ (fun x=>A x /\ B (f x)) A
  (fun x=>g (f x)) a (fun x hx=>hx.1)
  (@norm_analytic_at_composition R X Y Z NX NY NZ hNX hNY hNZ A B f g a (hf a ha) (hg (f a) (hAB a ha)))).
Qed.

(** Source for [norm_analytic_add]: analytic sums on a common
    domain, supporting the coordinate formulas of 3.1.24, p. 240. *)
Lemma norm_analytic_add (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f g:X->Y) :
  @norm_analytic R X Y NX NY hNX hNY A f -> @norm_analytic R X Y NX NY hNX hNY A g ->
  @norm_analytic R X Y NX NY hNX hNY A (fun x=>f x+g x).
Proof. move=>hf hg a ha; exact (norm_analytic_at_common_domain_add (hf a ha) (hg a ha)). Qed.

(** Source for [norm_analytic_subtract]: analytic differences
    in the coordinate formulas of 3.1.24, p. 240. *)
Lemma norm_analytic_subtract (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f g:X->Y) :
  @norm_analytic R X Y NX NY hNX hNY A f -> @norm_analytic R X Y NX NY hNX hNY A g ->
  @norm_analytic R X Y NX NY hNX hNY A (fun x=>f x-g x).
Proof. move=>hf hg a ha; exact (norm_analytic_at_subtract (hf a ha) (hg a ha)). Qed.

(** Source for [norm_analytic_domain_agreement]: actual-domain
    agreement preserves analyticity in 3.1.24, pp. 239–240. *)
Lemma norm_analytic_domain_agreement (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f g:X->Y) :
  (forall x,A x -> f x=g x) -> @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R X Y NX NY hNX hNY A g.
Proof. move=>he hf a ha; exact (norm_analytic_at_domain_agreement he (hf a ha)). Qed.
