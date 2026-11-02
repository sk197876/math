(** Federer (1969), 2.5.1, p. 92: increasing continuity of the integral on a
    summable real-function lattice, cited there to 2.4.7, p. 84. These
    supporting graph and scalar-limit adapters permit applying the earlier
    abstract lower-limit theorem to total finite functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionLimitExtremaUP ExtendedRealOrderLimit
  ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedConvergentLowerLimit RealScalarOrderLimits
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_order_limit_translate]: subtracting the first term to
    use 2.4.7 for the signed increasing convergence in Federer 2.5.1, p. 92 *)
Lemma real_order_limit_translate (R : realType) (u : nat -> R) (a c : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (u n+c)%R%:E) (a+c)%R%:E.
Proof.
move=> hl; have hh := @real_affine_order_limit R u a 1%R c hl.
have he : (fun n => (c+1 * u n)%R%:E)=(fun n => (u n+c)%R%:E).
  by apply: funext=> n; rewrite mul1r addrC.
by rewrite he mul1r addrC in hh.
Qed.

(** Source for [real_total_pointwise_lower_limit]: supporting lower-limit
    specification for the increasing convergence in Federer 2.5.1, p. 92
    This graph adapter needs only pointwise convergence, not monotonicity. *)
Lemma real_total_pointwise_lower_limit (R : realType) (X : Type)
    (f : nat -> X -> R) (g : X -> R) :
  (forall x, extended_order_limit (fun n => (f n x)%:E) (g x)%:E) ->
  is_partial_function_lower_limit (fun n => real_total_integrand (f n)) (real_total_integrand g).
Proof.
move=> hl; have hs x := extended_convergent_lower_limit (hl x).
constructor.
- apply/seteqP; split=> x hx.
  + exists 0%N=> n _; exists (f n x)%:E; by apply/real_total_integrand_graph.
  + exists (g x)%:E; by apply/real_total_integrand_graph.
- move=> x y /real_total_integrand_graph hy b [K hK].
  rewrite -hy; apply: (extended_real_supremum_upper (hs x)).
  exists K=> n hn; apply: (hK n hn (f n x)%:E); by apply/real_total_integrand_graph.
- move=> x y /real_total_integrand_graph hy b hb.
  rewrite -hy; apply: (extended_real_supremum_least (hs x))=> c [K hK].
  apply: hb; exists K=> n hn z /real_total_integrand_graph hz.
  rewrite -hz; exact: hK n hn.
Qed.
