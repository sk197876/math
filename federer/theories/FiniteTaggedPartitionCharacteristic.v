(** Federer (1969), 4.1.23, p. 380:
    the original finite disjoint partition
    preserves the literal characteristic field
    and its total measure. No tag
    or point of an empty cell
    is used in these exact identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import FiniteTaggedBorelPartitionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP MeasureBasic
  MeasureCharacteristicIntegral MeasureIntegralUP MeasureIntegralUniqueness
  FiniteSignedRealIntegral.
From Federer Require Import SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_tagged_partition_characteristic_sum]:
    the exact identity 1_B=sum_k 1_Bk
    underlying S=sum_k S_k in
    Federer 4.1.23, p. 380.
    All values are pointwise, including
    points on cell and box boundaries. *)
Theorem finite_tagged_partition_characteristic_sum (R : realType)
    (X : metricType R) (K : set X) e
    (I : finType) (A : I -> set X) (tag : I -> X)
    (hP : is_finite_tagged_borel_partition K e A tag) x :
  @CharacteristicFunction.value R X K x=
    \sum_i @CharacteristicFunction.value R X (A i) x.
Proof.
pose hK := @CharacteristicFunction.laws R X K.
pose hA := fun i => @CharacteristicFunction.laws R X (A i).
case: (pselect (K x))=> hx.
- have [i hi] := finite_tagged_partition_cover hP hx.
  rewrite (characteristic_on_set hK hx) (bigD1 i) //
    (characteristic_on_set (hA i) hi).
  have hOther : \sum_(j | j!=i) @CharacteristicFunction.value R X (A j) x=0.
    apply: big1=> j hJI.
    apply: (@characteristic_off_set R X (A j)
      (@CharacteristicFunction.value R X (A j)) (hA j) x)=> hj.
    have hEqual := @finite_tagged_partition_disjoint R X K e I A tag hP j i x hj hi.
    by move: hJI; rewrite hEqual eqxx.
  change (1 = 1 + \sum_(j | j!=i) @CharacteristicFunction.value R X (A j) x).
  by rewrite hOther addr0.
- rewrite (characteristic_off_set hK hx); symmetry.
  apply: big1=> i _.
  apply: (@characteristic_off_set R X (A i)
    (@CharacteristicFunction.value R X (A i)) (hA i) x)=> hi.
  exact: hx (@finite_tagged_partition_inside R X K e I A tag hP i x hi).
Qed.

(** Source for [finite_tagged_partition_measure_sum]:
    the equality sum_k Leb(B_k)=Leb(B)
    used for M(Q) in Federer
    4.1.23, p. 380. Only
    the original finite measure and measurable
    cells are required; zero measures and
    an empty partition retain their literal values. *)
Theorem finite_tagged_partition_measure_sum (R : realType)
    (X : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (K : set X) e (I : finType) (A : I -> set X) (tag : I -> X)
    (hP : is_finite_tagged_borel_partition K e A tag)
    (hK : measure_measurable mu K) (hFinite : (mu K< +oo)%E)
    (hCells : forall i, measure_measurable mu (A i)) :
  (\sum_i fine (mu (A i)))%:E=mu K.
Proof.
have hNumbers i : mu (A i) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (A i))).
  apply: (le_lt_trans _ hFinite).
  apply: (@measure_mono R X mu hm (A i) K).
  exact: (@finite_tagged_partition_inside R X K e I A tag hP i).
have hIntegrals i : is_measure_integral mu
    (real_total_integrand (@CharacteristicFunction.value R X (A i)))
    (fine (mu (A i)))%:E.
  rewrite (fineK (hNumbers i)).
  exact: (@measure_characteristic_integral R X mu hm (A i)
    (@CharacteristicFunction.value R X (A i)) (@CharacteristicFunction.laws R X (A i))
    (hCells i)).
have hSum := @finite_signed_real_sum_integral R X I mu hm (enum I)
  (fun i => @CharacteristicFunction.value R X (A i))
  (fun i => fine (mu (A i))) (fun i _ => hIntegrals i).
rewrite !big_enum in hSum.
have hFunction : (fun x : X => \sum_(i <- enum I) @CharacteristicFunction.value R X (A i) x)=
    (@CharacteristicFunction.value R X K).
  apply: funext=> x; rewrite big_enum; symmetry.
  exact: (@finite_tagged_partition_characteristic_sum R X K e I A tag hP x).
rewrite hFunction in hSum.
exact: measure_integral_unique hSum
  (@measure_characteristic_integral R X mu hm K (@CharacteristicFunction.value R X K)
    (@CharacteristicFunction.laws R X K) hK).
Qed.
