(** Federer (1969), 2.5.3, proof p. 95: pass from characteristic functions
    of finite measurable sets to finite positive linear combinations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellCoverUP DaniellCoverBasic
  DaniellCharacteristicApproximation LatticeL1ApproximationUP LatticeL1ApproximationLaws
  RealIntegralFunctionalUP SummableRealFunctionUP CharacteristicFunctionUP
  MeasureUP MeasureBasic MeasureIntegralUP MeasureCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_characteristic_l1_approximable]: exact
    characteristic-function case supporting Federer 2.5.3, p. 95 Arbitrarily
    small positive errors are allowed. *)
Lemma daniell_characteristic_l1_approximable (R : realType) (X : choiceType)
    (L : set (X -> R)) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu) (S : set X) (s : X -> R) :
  is_characteristic_function S s -> measure_measurable mu S -> mu S < +oo ->
  is_positive_lattice_l1_approximable mu L s.
Proof.
move=> hs hS hfin; split.
- exists (fine (mu S)).
  have hSf : mu S \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm S).
  rewrite fineK //; exact: (@measure_characteristic_integral R X mu hm S s hs hS).
- move=> d hd; have hd3 : (0 < d/3)%R by rewrite divr_gt0 // ltr0n.
  have [h [e [hh [he heb]]]] := @daniell_characteristic_lattice_approximation R X L F mu hm hF hc S s (d/3)%R hs hS hfin hd3.
  exists h,e; split=> //; split=> //.
  have heq : (d/3+(d/3+d/3))%R=d.
    rewrite -mulr2n -mulrS -(@mulr_natr R (d/3)%R 3) divfK //; by rewrite pnatr_eq0.
  by rewrite heq in heb.
Qed.

(** Source for [daniell_finite_positive_simple_density]: finite
    positive-combination case in Federer 2.5.3, proof p. 95 The empty sum is
    included; the existence of a suiting sequence for the empty set supplies
    the necessary lattice member. Disjointness of supports is unnecessary
    for this approximation statement. *)
Theorem daniell_finite_positive_simple_density (R : realType) (X : choiceType) (I : eqType)
    (L : set (X -> R)) (F : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hF : is_real_integral_functional mu L F)
    (hc : is_daniell_cover_envelope L F mu) (t : seq I)
    (A : I -> set X) (s : I -> X -> R) (c : I -> R) :
  (forall i, i \in t -> is_characteristic_function (A i) (s i)) ->
  (forall i, i \in t -> measure_measurable mu (A i)) ->
  (forall i, i \in t -> mu (A i) < +oo) -> (forall i, i \in t -> (0 <= c i)%R) ->
  is_positive_lattice_l1_approximable mu L (fun x => (\sum_(i <- t) c i*s i x)%R).
Proof.
move=> hs hA hfin hpos.
have hz : mu set0 < (1%R : R)%:E by rewrite (measure_empty hm) lte01.
have [f [b [hf _]]] := daniell_cover_approximation hc hz.
have hL0 := @function_lattice_zero R X L hL (f 0%N) (hf.1 0%N).1.
elim: t hs hA hfin hpos=> [|i t IH] hs hA hfin hpos.
- have he : (fun x : X => (\sum_(j <- [::]) c j*s j x)%R)=(fun _ => (0%R : R)).
    by apply: funext=> x; rewrite big_nil.
  rewrite he; exact: (@positive_lattice_l1_approximable_zero R X mu hm L hL0).
- have hii : i \in i::t by rewrite in_cons eqxx.
  have hsub j : j \in t -> j \in i::t by move=> hj; rewrite in_cons hj orbT.
  have hchar := @daniell_characteristic_l1_approximable R X L F mu hm hF hc (A i) (s i)
    (hs i hii) (hA i hii) (hfin i hii).
  have hscale := @positive_lattice_l1_approximable_scale R X mu hm L hL (s i) (c i) (hpos i hii) hchar.
  have htail := IH (fun j hj => hs j (hsub j hj)) (fun j hj => hA j (hsub j hj))
    (fun j hj => hfin j (hsub j hj)) (fun j hj => hpos j (hsub j hj)).
  have he : (fun x => (\sum_(j <- i::t) c j*s j x)%R)=
    (fun x => (c i*s i x+\sum_(j <- t) c j*s j x)%R) by apply: funext=> x; rewrite big_cons.
  rewrite he; exact: (@positive_lattice_l1_approximable_add R X mu hm L F hL hF _ _ hscale htail).
Qed.
