(** Federer (1969), 3.4.5, p. 319: existence
    and uniqueness of the exact factorial-growth classes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_growth_class_exists]: the
    subsets displayed in 3.4.5, p. 319, exist
    with exactly the independently stated derivative bounds. *)
Theorem analytic_germ_growth_class_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) s t:
  exists C:set (analytic_germ_space hNX a),is_analytic_germ_growth_class s t C.
Proof.
exists (fun alpha=>forall m,analytic_germ_jet_norm m alpha<=s%:R*t%:R^+m*(m`!)%:R).
by constructor.
Qed.

(** Source for [analytic_germ_growth_class_unique]: all-order
    membership determines the original subset uniquely,
    3.4.5, p. 319. *)
Lemma analytic_germ_growth_class_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) s t
    (C D:set (analytic_germ_space hNX a)):
  is_analytic_germ_growth_class s t C ->is_analytic_germ_growth_class s t D ->C=D.
Proof.
move=>hC hD;apply/seteqP;split=>alpha hAlpha.
- exact:((analytic_germ_growth_membership hD alpha).2 ((analytic_germ_growth_membership hC alpha).1 hAlpha)).
- exact:((analytic_germ_growth_membership hC alpha).2 ((analytic_germ_growth_membership hD alpha).1 hAlpha)).
Qed.
