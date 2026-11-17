(** Supporting the corrected infinity argument in Federer (1969),
    3.2.45, p. 279. Uniform positive probability floors and the
    existing contraction squeeze determine the full supremum. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal ring.
From Federer Require Import RealPower ExtendedRealBounds ExtendedRealOrderLimit
  ExtendedRealLimitBounds ExtendedContractionSqueeze PositiveNaturalRootLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_root_lower_supremum]: expanded limit
    helper for Federer 3.2.45, p. 279. If every positive
    contraction of a nonnegative extended bound has a uniform
    natural-root lower approximation, the approximating family
    has exactly that supremum. Neither the bound nor its
    approximants are required to be finite. *)
Theorem uniform_root_lower_supremum (R : realType) (u : nat -> \bar R) (b : \bar R) :
  0 <= b -> (forall j, 0 <= u j) -> (forall j, u j <= b) ->
  (forall r : R, (0 < r)%R -> (r < 1)%R -> exists a : R, (0 < a)%R /\
    forall j, ((r * real_power a ((j.+1)%:R)^-1)%R)%:E * b <= u j) ->
  extended_real_sup [set z | exists j, z = u j] = b.
Proof.
move=> hB hU hUpper hLower.
pose S := extended_real_sup [set z | exists j, z = u j].
have hS j : u j <= S by apply: extended_real_sup_upper; exists j.
have hS0 : 0 <= S := le_trans (hU 0%N) (hS 0%N).
have hSB : S <= b by apply: extended_real_sup_least=> z [j ->]; exact: hUpper.
have hBS : b <= S.
  apply: (@extended_contraction_squeeze R b S hS0)=> r /andP[hR hR1].
  have [a [hA hApproximation]] := hLower r hR hR1.
  clear hLower hUpper hSB.
  case: b hB hApproximation=> [x| |] hB hApproximation.
  - have hLimit := @positive_natural_root_scalar_order_limit R a (r*x)%R hA.
    apply: (@extended_order_limit_upper_bound R
      (fun j : nat => ((r*x)*real_power a ((j.+1)%:R)^-1)%R%:E)
      (r*x)%R%:E S hLimit)=> j.
    have h := le_trans (hApproximation j) (hS j).
    rewrite -EFinM in h.
    have hEqual : (r * real_power a ((j.+1)%:R)^-1 * x =
      (r*x)*real_power a ((j.+1)%:R)^-1)%R by ring.
    by rewrite hEqual in h.
  - have hPositive : (0 < r * real_power a (1%:R)^-1)%R.
      apply: mulr_gt0 hR _; exact: real_power_strictly_positive hA.
    have h := le_trans (hApproximation 0%N) (hS 0%N).
    have hCoefficient : (((r * real_power a (1%:R)^-1)%R)%:E * +oo) = +oo.
      exact: gt0_muley (lte_tofin hPositive).
    rewrite hCoefficient in h.
    by rewrite (gt0_muley (lte_tofin hR)); exact h.
  - by move: hB; rewrite leNgt ltNyr.
apply/eqP; by rewrite eq_le hSB hBS.
Qed.

(** Source for [uniform_root_lower_cofinal]: the finite-exponent
    lower approximation consequence of the same argument in
    Federer 3.2.45, p. 279. Every strict lower bound on
    the endpoint is exceeded by an actual approximant. *)
Corollary uniform_root_lower_cofinal (R : realType) (u : nat -> \bar R) (b : \bar R) :
  0 <= b -> (forall j, 0 <= u j) -> (forall j, u j <= b) ->
  (forall r : R, (0 < r)%R -> (r < 1)%R -> exists a : R, (0 < a)%R /\
    forall j, ((r * real_power a ((j.+1)%:R)^-1)%R)%:E * b <= u j) ->
  forall c, c < b -> exists j, c < u j.
Proof.
move=> hB hU hUpper hLower c hC.
have hSup := @uniform_root_lower_supremum R u b hB hU hUpper hLower.
apply: contrapT=> hNo.
have hBound : b <= c.
  rewrite -hSup; apply: extended_real_sup_least=> z [j ->].
  rewrite leNgt; apply/negP=> h; apply: hNo; by exists j.
by have := lt_le_trans hC hBound; rewrite ltxx.
Qed.
