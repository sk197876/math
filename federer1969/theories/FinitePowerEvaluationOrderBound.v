(** Individual coefficient limits for Federer (1969),
    3.2.45, pp. 279–280. The finite evaluation
    inverse and original order limits suffice. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanLinearMaps
  FinitePowerEvaluationRecovery FiniteRealCombinationLimit ExtendedRealOrderLimit ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_power_evaluation_coefficient_limit]: supporting
    passage from finitely many actual tube-volume limits
    to each coefficient in Federer 3.2.45,
    pp. 279–280. Apply the proved finite linear
    inverse formula to every original coefficient vector
    and use finite signed scalar limit arithmetic.
    The maps are local witnesses with their inverse
    law, not extra coefficient-limit assumptions. *)
Lemma finite_power_evaluation_coefficient_limit (R : realType) N
    (E G : {linear R_n R N.+1 -> R_n R N.+1})
    (c : nat -> R_n R N.+1) (d : R_n R N.+1) :
  cancel E G ->
  (forall j, extended_order_limit (fun s => (E (c s) j)%:E) (E d j)%:E) ->
  forall i, extended_order_limit (fun s => (c s i)%:E) (d i)%:E.
Proof.
move=> hInverse hLimits i.
pose w (j : 'I_N.+1) := G (@coordinate_basis R N.+1 j) i.
have h := @finite_real_combination_order_limit R 'I_N.+1 (index_enum 'I_N.+1)
  (fun j s => E (c s) j) (fun j => E d j) w (fun j _ => hLimits j).
have hFunction : (fun s => (\sum_(j <- index_enum 'I_N.+1) w j*E (c s) j)%:E)=
    (fun s => (c s i)%:E).
  apply: funext=> s; congr (_%:E); rewrite (finite_power_evaluation_recovery hInverse).
  apply: eq_bigr=> j _; exact: mulrC.
have hValue : (\sum_(j <- index_enum 'I_N.+1) w j*E d j)=d i.
  rewrite (finite_power_evaluation_recovery hInverse); apply: eq_bigr=> j _; exact: mulrC.
by rewrite hFunction hValue in h.
Qed.

(** Source for [finite_power_evaluation_coefficient_upper_bound]: supporting
    the needed mixed-coefficient comparison in Federer
    3.2.45, pp. 279–280. Each approximating
    coefficient already has its own proved upper bound.
    Finite evaluation convergence identifies its actual
    limit; the original closed order-bound law passes
    that bound to the limit. A pointwise order
    between whole polynomials is never used to infer
    an order between their coefficients. *)
Theorem finite_power_evaluation_coefficient_upper_bound (R : realType) N
    (E G : {linear R_n R N.+1 -> R_n R N.+1})
    (c : nat -> R_n R N.+1) (d b : R_n R N.+1) :
  cancel E G ->
  (forall j, extended_order_limit (fun s => (E (c s) j)%:E) (E d j)%:E) ->
  (forall s i, c s i<=b i) -> forall i, d i<=b i.
Proof.
move=> hInverse hLimits hBounds i.
have hLimit := @finite_power_evaluation_coefficient_limit R N E G c d hInverse hLimits i.
have hBoundsE s : ((c s i)%:E<=(b i)%:E)%E by rewrite lee_fin; exact: hBounds s i.
have h := @extended_order_limit_upper_bound R (fun s => (c s i)%:E) (d i)%:E (b i)%:E
  hLimit hBoundsE.
by rewrite lee_fin in h.
Qed.
