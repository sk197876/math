(** Allard (1972), 3.5, p. 431: the weight of a rectifiable varifold
    V = Σ_i c_i v(E_i) is ‖V‖ = Σ_i c_i H^k⌞E_i, and its multiplicity
    function θ = Σ_i c_i 1_{E_i} (blueprint proof of al:3.5(1)). Here
    M = U = R^n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LinearBasis FiniteCoordinates Hom MeasureUP MeasureBasic MeasureRestriction HausdorffMeasure
  NonnegativeSum NonnegativeSumSupport.
From Allard Require Import AllardGrassmann AllardVarifolds AllardRectifiableVarifolds AllardSetVarifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableSum.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation GB := (grassmann_bundle R n k).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).

(** Source for [rectifiable_sum_measure]: Allard 3.5, p. 431: the measure
    Σ_i c_i H^k⌞E_i over R^n, the weight of Σ_i c_i v(E_i). Definition. *)
Definition rectifiable_sum_measure (c : nat -> R) (E : nat -> set RnM) : set RnM -> \bar R :=
  fun A => nonnegative_sum [set: nat] (fun i => ((c i)%:E * HK (E i `&` A))%E).

(** Source for [rectifiable_sum_density]: blueprint proof of al:3.5(1):
    the multiplicity θ(x) = Σ_i c_i 1_{E_i}(x) ∈ [0, ∞]. Definition. *)
Definition rectifiable_sum_density (c : nat -> R) (E : nat -> set RnM) (x : RnM) : \bar R :=
  nonnegative_sum [set: nat] (fun i => if `[< E i x >] then (c i)%:E else 0%E).

(** Source for [rectifiable_varifold_components]: Allard 3.5, p. 431: in
    a representation V = Σ_i c_i W_i of a rectifiable varifold with
    W_i characterised by 3.5, W_i = v(E_i). Supporting lemma. *)
Lemma rectifiable_varifold_components (E : nat -> set RnM) (W : nat -> set GB -> \bar R) :
  (forall i, locrect (E i)) -> (forall i, is_set_varifold (E i) (W i)) ->
  forall i, W i = set_varifold (E i).
Proof.
move=> hE hW i; apply: (set_varifold_unique (hW i)).
exact: set_varifold_set_varifold (hE i).
Qed.

(** Source for [rectifiable_varifold_weight]: Allard 3.1 and 3.5, p. 431,
    with blueprint al:3.5:lem: if V = Σ_i c_i v(E_i), then
    ‖V‖ = Σ_i c_i H^k⌞E_i, as measures over R^n. Direct formalisation. *)
Theorem rectifiable_varifold_weight (V : set GB -> \bar R) (c : nat -> R) (E : nat -> set RnM)
    (W : nat -> set GB -> \bar R) :
  (forall i, locrect (E i)) -> (forall i, is_set_varifold (E i) (W i)) ->
  (forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * W i A)%E)) ->
  varifold_weight V = rectifiable_sum_measure c E.
Proof.
move=> hE hW hV; apply: funext=> A.
rewrite varifold_weightE hV /rectifiable_sum_measure.
apply: nonnegative_sum_ext=> i _.
rewrite (rectifiable_varifold_components hE hW i).
by have := congr1 (fun f => f A) (set_varifold_weight (hE i)); rewrite varifold_weightE => ->.
Qed.

(** Source for [rectifiable_varifold_representation]: Allard 3.5,
    p. 431: unfolding RV_k(R^n), every rectifiable varifold has a
    representation V = Σ_i c_i v(E_i) with ‖V‖ = Σ_i c_i H^k⌞E_i.
    Supporting lemma. *)
Lemma rectifiable_varifold_representation (V : set GB -> \bar R) :
  is_rectifiable_varifold V ->
  exists (c : nat -> R) (E : nat -> set RnM), [/\ forall i, 0 < c i, forall i, locrect (E i),
    forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * set_varifold (E i) A)%E) &
    varifold_weight V = rectifiable_sum_measure c E].
Proof.
move=> [hV [c [E [W [hc hE hW hsum]]]]].
exists c, E; split=> //.
- move=> A; rewrite hsum; apply: nonnegative_sum_ext=> i _.
  by rewrite (rectifiable_varifold_components hE hW i).
- exact: rectifiable_varifold_weight hE hW hsum.
Qed.
End RectifiableSum.
