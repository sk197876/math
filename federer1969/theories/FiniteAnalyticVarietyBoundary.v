(** Federer (1969), 3.4.5, pp. 320–321:
    the empty set and whole open domain are actual finite
    analytic varieties, and every original variety stays
    inside its original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticConstant FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Boundary.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable U:set X.
Hypothesis hU:@open (real_norm_metric_space hNX) U.
Local Notation VAR S:=(@is_finite_analytic_variety R X NX hNX U S).

(** Source for [finite_analytic_variety_domain_inside]: the
    original domain condition in var(U,F), 3.4.5, p. 320. *)
Lemma finite_analytic_variety_domain_inside (S:set X):VAR S ->S `<=` U.
Proof. move=>[_ [I [f [hf hS]]]] x /hS [hx _];exact:hx. Qed.

(** Source for [finite_analytic_variety_constant_equation]:
    one original constant equation defines an analytic
    variety, including the empty and whole-domain cases,
    3.4.5, pp. 320–321. *)
Lemma finite_analytic_variety_constant_equation (c:R):VAR (U `&` [set _|c=0]).
Proof.
have hOpen x (hx:U x):norm_domain_interior NX U x.
  have hNear:=hU;rewrite openE in hNear.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hNear x hx)).
split;first exact:hU.
exists (Finite.clone 'I_1 _),(fun (_:'I_1) (_:X)=>c);split.
- move=>_;exact:(@norm_constant_analytic R X R^o NX (fun z=>`|z|) hNX
    (@scalar_absolute_value_norm R) U hOpen c).
- move=>x;split.
  + move=>[hx hZero];split;first exact:hx. by move=>_.
  + move=>[hx hZero];split;first exact:hx. exact:hZero ord0.
Qed.

(** Source for [finite_analytic_variety_domain_whole]: zero
    defines the whole original U, 3.4.5, pp. 320–321. *)
Lemma finite_analytic_variety_domain_whole:VAR U.
Proof.
have hSet:U=U `&` [set _|(0:R)=0] by apply/seteqP;split;[by move=>x hx;split|by move=>x [hx _]].
have hVar:=finite_analytic_variety_constant_equation (0:R).
by rewrite -hSet in hVar.
Qed.

(** Source for [finite_analytic_variety_domain_empty]: the
    unit equation defines the empty original variety,
    3.4.5, pp. 320–321. *)
Lemma finite_analytic_variety_domain_empty:VAR set0.
Proof.
have hSet:set0=U `&` [set _|(1:R)=0].
  apply/seteqP;split;first by move=>x hx;case:hx.
  move=>x [_ hOne];by move/eqP:hOne;rewrite oner_eq0.
have hVar:=finite_analytic_variety_constant_equation (1:R).
by rewrite -hSet in hVar.
Qed.
End Boundary.
