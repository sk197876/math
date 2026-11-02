(** Federer (1969), 2.5.14, p. 108: supporting positive density for the
    Radon vector representation. This isolates the finite-sum step of 2.5.3,
    p. 95, from any particular measure envelope. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws LatticeL1ApproximationUP LatticeL1ApproximationLaws
  RealIntegralFunctionalUP SummableRealFunctionUP CharacteristicFunctionUP
  MeasureUP MeasureBasic MeasureIntegralUP MeasureCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_characteristic_finite_simple_density]:
    finite positive combinations preserve the characteristic
    approximation needed in Federer 2.5.14, p. 108, by
    the argument of 2.5.3, p. 95. Characteristic density
    is an explicit hypothesis of this supporting lemma and
    is proved separately for the Radon measure. *)
Theorem positive_characteristic_finite_simple_density (R : realType) (X : choiceType) (I : eqType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hL0 : L (fun _ => 0%R))
    (hchar : forall S s, is_characteristic_function S s -> measure_measurable mu S -> mu S < +oo ->
      is_positive_lattice_l1_approximable mu L s) (t : seq I)
    (A : I -> set X) (s : I -> X -> R) (c : I -> R) :
  (forall i, i \in t -> is_characteristic_function (A i) (s i)) ->
  (forall i, i \in t -> measure_measurable mu (A i)) ->
  (forall i, i \in t -> mu (A i) < +oo) -> (forall i, i \in t -> (0 <= c i)%R) ->
  is_positive_lattice_l1_approximable mu L (fun x => (\sum_(i <- t) c i*s i x)%R).
Proof.
move=> hs hA hfin hpos.
elim: t hs hA hfin hpos=> [|i t IH] hs hA hfin hpos.
- have he : (fun x : X => (\sum_(j <- [::]) c j*s j x)%R)=(fun _ => (0%R : R)).
    by apply: funext=> x; rewrite big_nil.
  rewrite he; exact: (@positive_lattice_l1_approximable_zero R X mu hm L hL0).
- have hii : i \in i::t by rewrite in_cons eqxx.
  have hsub j : j \in t -> j \in i::t by move=> hj; rewrite in_cons hj orbT.
  have hchar_i := hchar (A i) (s i)
    (hs i hii) (hA i hii) (hfin i hii).
  have hscale := @positive_lattice_l1_approximable_scale R X mu hm L hL (s i) (c i) (hpos i hii) hchar_i.
  have htail := IH (fun j hj => hs j (hsub j hj)) (fun j hj => hA j (hsub j hj))
    (fun j hj => hfin j (hsub j hj)) (fun j hj => hpos j (hsub j hj)).
  have he : (fun x => (\sum_(j <- i::t) c j*s j x)%R)=
    (fun x => (c i*s i x+\sum_(j <- t) c j*s j x)%R) by apply: funext=> x; rewrite big_cons.
  rewrite he; exact: (@positive_lattice_l1_approximable_add R X mu hm L F hL hF _ _ hscale htail).
Qed.
