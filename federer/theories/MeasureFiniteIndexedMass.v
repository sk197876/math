(** Federer (1969), 3.4.10, p. 337:
    finite mass survives the finite local exceptional
    union. Extract only the missing finite-mass connection
    from the existing finite outer-measure bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteUnionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_indexed_union_finite_mass]: the
    finite exceptional-family assembly in 3.4.10, p. 337.
    Reuse the outer-measure bound of 2.1.2,
    pp. 53–54, without rectifiability or measurability
    hypotheses on the actual members. *)
Theorem measure_finite_indexed_union_finite_mass (R:realType) (X:choiceType)
    (J:finType) (mu:set X->\bar R) (F:J->set X):
  is_measure mu ->(forall j,mu (F j)< +oo) ->mu (\bigcup_j F j)< +oo.
Proof.
move=>hMu hMass.
have hValue j:mu (F j)=(fine (mu (F j)))%:E.
  have hFinite:mu (F j) \is a fin_num.
    rewrite ge0_fin_numE;first exact:hMass j.
    exact:measure_nonnegative hMu _.
  by rewrite fineK.
have hSum:(\sum_j mu (F j))=(\sum_j fine (mu (F j)))%:E.
  rewrite -sumEFin;apply:eq_bigr=>j _;exact:hValue j.
apply:(le_lt_trans (@measure_finite_union_bound R X J mu F hMu)).
by rewrite hSum ltry.
Qed.
