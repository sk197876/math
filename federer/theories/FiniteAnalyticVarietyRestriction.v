(** Federer (1969), 3.4.5, pp. 320–321:
    finite analytic equations restrict to actual open subsets,
    supporting the equivalence of the germ and cover definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_variety_open_restriction]:
    a finite analytic variety restricts to a finite analytic
    variety in any actual open subdomain, 3.4.5, pp. 320–321. *)
Lemma finite_analytic_variety_open_restriction (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U V S:set X):
  is_finite_analytic_variety hNX U S ->@open (real_norm_metric_space hNX) V ->
  V `<=` U ->is_finite_analytic_variety hNX V (V `&` S).
Proof.
move=>[hU [I [f [hf hS]]]] hV hVU.
have hOpen x (hx:V x):norm_domain_interior NX V x.
  have hNeighbourhood:=hV;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX V x).2 (hNeighbourhood x hx)).
split;first exact:hV.
exists I,f;split.
- move=>i;exact (@norm_analytic_open_restriction R X R^o NX (fun z=>`|z|) hNX
    (@scalar_absolute_value_norm R) U V (f i) hVU hOpen (hf i)).
- move=>x;split.
  + move=>[hx /hS [_ hZero]];by split.
  + move=>[hx hZero];split;first exact:hx.
    apply/(hS x);split;[exact:hVU x hx|exact:hZero].
Qed.
