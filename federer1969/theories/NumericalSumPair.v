(** Federer (1969), 3.2.13, p. 250: finite
    signed fibre sums for the one-dimensional radial
    map. Two distinct points have an always-defined
    real sum, even with weights of opposite signs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial NumericalSum NumericalSumValues NumericalSumAdd NumericalSumSingleSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_real_pair]: supporting
    two-point numerical sum in the m= 1 polar
    formula, Federer 3.2.13, p. 250.
    All real-valued summands are allowed. *)
Lemma numerical_sum_real_pair (R:realType) (X:choiceType) (g:X->R) (a b:X):
  a!=b ->numerical_sum ([set a] `|` [set b]) (fun x=>(g x)%:E)=Some (g a+g b)%R%:E.
Proof.
move=>hab.
pose A:=[set a] `|` [set b].
pose f (x:X):=if x==a then (g a)%:E else (0:extended_real_line R).
pose h (x:X):=if x==b then (g b)%:E else (0:extended_real_line R).
have hA:A a by left.
have hB:A b by right.
have hF:numerical_sum A f=Some (g a)%:E.
  have hh:=@numerical_sum_single_support R X A f a hA.
  rewrite /f eqxx in hh; apply:hh=>x _ hxa.
  by rewrite (negbTE hxa).
have hH:numerical_sum A h=Some (g b)%:E.
  have hh:=@numerical_sum_single_support R X A h b hB.
  rewrite /h eqxx in hh; apply:hh=>x _ hxb.
  by rewrite (negbTE hxb).
have hSum:=(numerical_sum_add hF hH
  (Logic.eq_refl:extended_add (g a)%:E (g b)%:E=Some (g a+g b)%R%:E)).2.
have hEq:numerical_sum A (fun x=>(g x)%:E)=numerical_sum A (fun x=>f x+h x).
  apply:numerical_sum_ext=>x [hx|hx].
  - rewrite hx /f /h eqxx (negbTE hab) adde0; by [].
  - have hba:b!=a by rewrite eq_sym.
    rewrite hx /f /h eqxx (negbTE hba) add0e; by [].
by rewrite hEq.
Qed.
