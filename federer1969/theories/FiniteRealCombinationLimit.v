(** Finite scalar limit arithmetic supporting coefficient
    recovery in Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealScalarOrderLimits RealSequenceLimitArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_real_combination_order_limit]: supporting
    finite inverse interpolation of tube-volume limits in
    Federer 3.2.45, pp. 279–280, using the order
    limit of 2.1.1, p. 51. Proved scalar scaling
    and addition pass each prescribed finite linear
    combination to its limit. Both signs, zero weights,
    repeated indices and the empty sum are retained. *)
Lemma finite_real_combination_order_limit (R : realType) (I : eqType) (s : seq I)
    (u : I -> nat -> R) (b c : I -> R) :
  (forall i, i \in s -> extended_order_limit (fun n => (u i n)%:E) (b i)%:E) ->
  extended_order_limit (fun n => (\sum_(i <- s) c i*u i n)%:E) (\sum_(i <- s) c i*b i)%:E.
Proof.
elim: s=> [|i s hInduction] hLimits.
- have hZero : (fun n : nat => (\sum_(i <- [::]) c i*u i n)%:E)=(fun _ : nat => (0 : R)%:E).
    by apply: funext=> n; rewrite big_nil.
  rewrite hZero big_nil; exact: real_constant_order_limit.
- have hTail j : j \in s -> extended_order_limit (fun n => (u j n)%:E) (b j)%:E.
    move=> hj; apply: hLimits; by rewrite in_cons hj orbT.
  have hHead := @real_scalar_order_limit R (u i) (b i) (c i) (hLimits i (mem_head i s)).
  have h := real_sequence_limit_add hHead (hInduction hTail).
  have hFunction : (fun n => (\sum_(j <- i::s) c j*u j n)%:E)=
      (fun n => (c i*u i n+\sum_(j <- s) c j*u j n)%:E).
    by apply: funext=> n; rewrite big_cons.
  by rewrite hFunction big_cons.
Qed.
