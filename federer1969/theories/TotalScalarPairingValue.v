(** Federer (1969), 2.5.7, pp. 98–99: the pairing (f,k) -> integral f*k. We
    reuse the sealed integral functional from 2.5.1, p. 92. Its value is
    specified only when the product is summable; no default value for a
    divergent integral enters the laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralComparison MeasureConullZeroIntegral
  SummableRealFunctionUP SummableRealArithmetic RealIntegralFunctionalUP RealIntegralFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_pairing]: the product integral in Federer
    2.5.7, pp. 98–99 The existing sealed integral supplies the value. *)
Definition total_scalar_pairing (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : X -> R) :=
  @lattice_measure_integral R X mu (summable_real_functions mu) (fun h hh => hh)
    (fun x => (f x*g x)%R).

(** Source for [total_scalar_pairing_specification]: the integral law for
    the pairing of Federer 2.5.7, pp. 98–99 Summability is explicit. *)
Lemma total_scalar_pairing_specification (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : X -> R) :
  summable_real_functions mu (fun x => (f x*g x)%R) ->
  is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) (total_scalar_pairing mu f g)%:E.
Proof.
exact: (@lattice_measure_integral_specification R X mu (summable_real_functions mu) (fun h hh => hh)).
Qed.

(** Source for [total_scalar_pairing_value_of_integral]: uniqueness of the
    real integral in the pairing of Federer 2.5.7, pp. 98–99, by 2.4.4, p.
    82 *)
Lemma total_scalar_pairing_value_of_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : X -> R) c :
  is_measure_integral mu (real_total_integrand (fun x => (f x*g x)%R)) c%:E ->
  total_scalar_pairing mu f g=c.
Proof.
move=> hi.
have hs := @total_scalar_pairing_specification R X mu f g (ex_intro _ c hi).
have he := measure_integral_unique hs hi; by injection he.
Qed.

(** Source for [total_scalar_pairing_commute]: supporting symmetry of the
    scalar product integral in Federer 2.5.7, pp. 98–99 This is pointwise
    multiplication symmetry and does not assert summability by itself. *)
Lemma total_scalar_pairing_commute (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : X -> R) :
  total_scalar_pairing mu f g=total_scalar_pairing mu g f.
Proof.
rewrite /total_scalar_pairing.
have he : (fun x => (f x*g x)%R)=(fun x => (g x*f x)%R) by apply: funext=> x; exact: mulrC.
by rewrite he.
Qed.

(** Source for [total_scalar_pairing_add_left]: linearity in the test
    function of Federer 2.5.7, pp. 98–99 Both input products are summable,
    which also proves summability of their sum. *)
Lemma total_scalar_pairing_add_left (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g k : X -> R) :
  summable_real_functions mu (fun x => (f x*k x)%R) ->
  summable_real_functions mu (fun x => (g x*k x)%R) ->
  total_scalar_pairing mu (fun x => (f x+g x)%R) k=
    (total_scalar_pairing mu f k+total_scalar_pairing mu g k)%R.
Proof.
move=> hf hg; apply: total_scalar_pairing_value_of_integral.
have hi := @real_total_integral_add R X mu hm _ _ _ _
  (@total_scalar_pairing_specification R X mu f k hf)
  (@total_scalar_pairing_specification R X mu g k hg).
have he : (fun x => (f x*k x+g x*k x)%R)=(fun x => ((f x+g x)*k x)%R).
  by apply: funext=> x; rewrite mulrDl.
by rewrite he in hi.
Qed.

(** Source for [total_scalar_pairing_scale_left]: homogeneity in the test
    function of Federer 2.5.7, pp. 98–99 Zero and negative scalars are
    included because the products have finite real values. *)
Lemma total_scalar_pairing_scale_left (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f k : X -> R) (c : R) :
  summable_real_functions mu (fun x => (f x*k x)%R) ->
  total_scalar_pairing mu (fun x => (c*f x)%R) k=(c*total_scalar_pairing mu f k)%R.
Proof.
move=> hf; apply: total_scalar_pairing_value_of_integral.
have hi := @real_total_integral_scale R X mu hm _ _ c
  (@total_scalar_pairing_specification R X mu f k hf).
have he : (fun x => (c*(f x*k x))%R)=(fun x => ((c*f x)*k x)%R).
  by apply: funext=> x; rewrite mulrA.
by rewrite he in hi.
Qed.

(** Source for [total_scalar_pairing_add_right]: additivity in the density
    used repeatedly in Federer 2.5.7, p. 99 *)
Lemma total_scalar_pairing_add_right (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g k : X -> R) :
  summable_real_functions mu (fun x => (g x*f x)%R) ->
  summable_real_functions mu (fun x => (k x*f x)%R) ->
  total_scalar_pairing mu f (fun x => (g x+k x)%R)=
    (total_scalar_pairing mu f g+total_scalar_pairing mu f k)%R.
Proof.
move=> hg hk; rewrite [total_scalar_pairing mu f _]total_scalar_pairing_commute
  (@total_scalar_pairing_add_left R X mu hm g k f hg hk).
by rewrite [total_scalar_pairing mu g f]total_scalar_pairing_commute
  [total_scalar_pairing mu k f]total_scalar_pairing_commute.
Qed.

(** Source for [total_scalar_pairing_monotone_left]: order preservation for
    a nonnegative density, used in Federer 2.5.7, pp. 98–99 It follows from
    integral comparison 2.4.4(5), p. 82. *)
Lemma total_scalar_pairing_monotone_left (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g k : X -> R) :
  summable_real_functions mu (fun x => (f x*k x)%R) ->
  summable_real_functions mu (fun x => (g x*k x)%R) ->
  (forall x, (0 <= k x)%R) -> (forall x, (f x <= g x)%R) ->
  (total_scalar_pairing mu f k <= total_scalar_pairing mu g k)%R.
Proof.
move=> hf hg hk hfg.
have hh : (total_scalar_pairing mu f k)%:E <= (total_scalar_pairing mu g k)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _
    (@total_scalar_pairing_specification R X mu f k hf)
    (@total_scalar_pairing_specification R X mu g k hg)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x*k x)%:E,(g x*k x)%:E; split; first by apply/real_total_integrand_graph.
  split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; apply: (ler_wpM2r (hk x)); exact: hfg x.
by move: hh; rewrite lee_fin.
Qed.

(** Source for [total_scalar_pairing_zero_right]: zero candidate density in
    Federer 2.5.7, p. 98 The product is identically zero even if f is not
    summable. *)
Lemma total_scalar_pairing_zero_right (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  total_scalar_pairing mu f (fun _ => 0%R)=0%R.
Proof.
apply: total_scalar_pairing_value_of_integral.
apply: (@measure_almost_zero_integral R X mu hm).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
apply/real_total_integrand_graph; by rewrite mulr0.
Qed.
