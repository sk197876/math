(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, pp. 320–321:
    the empty set and whole open domain are actual finite
    analytic varieties, and every original variety stays
    inside its original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP HolomorphicArithmetic FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Boundary.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable U:set X.
Hypothesis hU:@open (real_norm_metric_space hNX) U.
Local Notation VAR S:=(@is_finite_holomorphic_variety R X NX hNX U S).

(** Source for [finite_holomorphic_variety_domain_inside]: the
    original domain condition in var(U,F), 3.4.5, p. 320. *)
Lemma finite_holomorphic_variety_domain_inside (S:set X):VAR S ->S `<=` U.
Proof. move=>[_ [I [f [hf hS]]]] x /hS [hx _];exact:hx. Qed.

(** Source for [finite_holomorphic_variety_constant_equation]:
    one original constant equation defines an analytic
    variety, including the empty and whole-domain cases,
    3.4.5, pp. 320–321. *)
Lemma finite_holomorphic_variety_constant_equation (c:ComplexScalars.C R):VAR (U `&` [set _|c=0]).
Proof.
have hOpen x (hx:U x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX U x.
  have hNear:=hU;rewrite openE in hNear.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX U x).2 (hNear x hx)).
split;first exact:hU.
exists (Finite.clone 'I_1 _),(fun (_:'I_1) (_:X)=>c);split.
- move=>_;exact:(@holomorphic_constant R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) U c hOpen).
- move=>x;split.
  + move=>[hx hZero];split;first exact:hx. by move=>_.
  + move=>[hx hZero];split;first exact:hx. exact:hZero ord0.
Qed.

(** Source for [finite_holomorphic_variety_domain_whole]: zero
    defines the whole original U, 3.4.5, pp. 320–321. *)
Lemma finite_holomorphic_variety_domain_whole:VAR U.
Proof.
have hSet:U=U `&` [set _|(0:ComplexScalars.C R)=0] by apply/seteqP;split;[by move=>x hx;split|by move=>x [hx _]].
have hVar:=finite_holomorphic_variety_constant_equation (0:ComplexScalars.C R).
by rewrite -hSet in hVar.
Qed.

(** Source for [finite_holomorphic_variety_domain_empty]: the
    unit equation defines the empty original variety,
    3.4.5, pp. 320–321. *)
Lemma finite_holomorphic_variety_domain_empty:VAR set0.
Proof.
have hSet:set0=U `&` [set _|(1:ComplexScalars.C R)=0].
  apply/seteqP;split;first by move=>x hx;case:hx.
  move=>x [_ hOne];by move/eqP:hOne;rewrite oner_eq0.
have hVar:=finite_holomorphic_variety_constant_equation (1:ComplexScalars.C R).
by rewrite -hSet in hVar.
Qed.
End Boundary.
