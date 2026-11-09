(** Federer (1969), 3.4.5, p. 319: factorial
    derivative-growth classes, specified by their exact membership law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_jet_norm]: the actual norm
    of D^m(alpha) in the metric and growth classes of
    3.4.5, p. 319; degree zero is included. *)
Definition analytic_germ_jet_norm (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m (alpha:analytic_germ_space hNX a):R:=
  @ContinuousMultilinear.norm R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    (@AnalyticGermJets.value R X NX hNX a m alpha).
Arguments analytic_germ_jet_norm {R X NX hNX a} m alpha.

(** Source for [is_analytic_germ_growth_class]: the exact
    subset defined by all bounds ||D^m(alpha)||<=s*t^m*m!
    in 3.4.5, p. 319. The membership specification
    precedes existence; it asserts no closedness or compactness.
    The book uses positive integer s and t in its covering theorem. *)
Record is_analytic_germ_growth_class (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (s t:nat)
    (C:set (analytic_germ_space hNX a)):Prop:={
  (** Source for [analytic_germ_growth_membership]: the original
      all-order factorial bounds, 3.4.5, p. 319. *)
  analytic_germ_growth_membership:forall alpha,C alpha <->
    forall m,analytic_germ_jet_norm m alpha<=s%:R*t%:R^+m*(m`!)%:R
}.
