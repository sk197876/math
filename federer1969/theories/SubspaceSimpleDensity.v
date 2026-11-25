(** Federer (1969), 2.6.4, pp. 118–119: the passage from characteristic
    functions to finite simple functions in the L1 closure of the tensor
    image. No lattice closure is required here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import ModuleQuotient MeasureUP MeasureIntegralUP SummableRealFunctionUP
  CharacteristicFunctionUP SubspaceLoneApproximationUP SubspaceLoneApproximationArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [subspace_finite_positive_simple_density]: supporting
    finite-simple reduction in Federer 2.6.4, pp. 118–119.
    The empty sum and zero coefficients are included, and the
    selected supports need not be disjoint. *)
Theorem subspace_finite_positive_simple_density (R : realType) (X : choiceType) (I : eqType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (L : subspace (GRing.Lmodule.clone R (X -> R^o) _))
    (hLs : forall f, L f -> summable_real_functions mu f)
    (hchar : forall (A : set X) (s : X -> R), measure_measurable mu A ->
      (mu A < +oo)%E -> is_characteristic_function A s -> is_subspace_lone_approximable mu L s)
    (t : seq I) (A : I -> set X) (s : I -> X -> R) (c : I -> R) :
  (forall i, i \in t -> is_characteristic_function (A i) (s i)) ->
  (forall i, i \in t -> measure_measurable mu (A i)) ->
  (forall i, i \in t -> (mu (A i) < +oo)%E) -> (forall i, i \in t -> 0<=c i) ->
  is_subspace_lone_approximable mu L (fun x => \sum_(i <- t) c i*s i x).
Proof.
move=> hs hA hfin hpos; elim: t hs hA hfin hpos=> [|i t IH] hs hA hfin hpos.
- have he : (fun x : X => \sum_(j <- [::]) c j*s j x)=(fun _ => (0 : R)).
    by apply: funext=> x; rewrite big_nil.
  rewrite he; exact (@subspace_lone_approximable_zero R X mu hm L hLs).
- have hii : i \in i::t by rewrite in_cons eqxx.
  have hsub j : j \in t -> j \in i::t by move=> hj; rewrite in_cons hj orbT.
  have hc := hchar (A i) (s i) (hA i hii) (hfin i hii) (hs i hii).
  have hscale := @subspace_lone_approximable_positive_scale R X mu hm L hLs (s i) (c i) (hpos i hii) hc.
  have htail := IH (fun j hj => hs j (hsub j hj)) (fun j hj => hA j (hsub j hj))
    (fun j hj => hfin j (hsub j hj)) (fun j hj => hpos j (hsub j hj)).
  have he : (fun x => \sum_(j <- i::t) c j*s j x)=
    (fun x => c i*s i x+\sum_(j <- t) c j*s j x) by apply: funext=> x; rewrite big_cons.
  rewrite he; exact (@subspace_lone_approximable_add R X mu hm L hLs _ _ hscale htail).
Qed.
