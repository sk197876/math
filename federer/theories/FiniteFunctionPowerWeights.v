(** Federer (1969), 2.10.29, p. 195: products of conserved finite level
    weights sum to one for arbitrary positive integer Cartesian powers.
    These supporting finite algebraic sums expand the cube-cover
    calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [normalised_finite_function_weight_sum]: supporting
    product of the conserved level sums in
    the arbitrary Cartesian cube covers of
    2.10.29, p. 195. Empty coordinate
    types obey the empty-product convention. *)
Lemma normalised_finite_function_weight_sum (R : realType) (I J : finType) (w : J -> R) :
  (\sum_j w j= 1)%R -> (\sum_(f : {ffun I -> J}) \prod_i w (f i)= 1)%R.
Proof.
move=> hw.
have hd : (\prod_(i : I) \sum_(j : J) w j=\sum_(f : {ffun I -> J}) \prod_i w (f i))%R.
  exact: (bigA_distr_bigA (fun (_ : I) (j : J)=>w j)).
rewrite -hd; apply: big1=> i _; exact hw.
Qed.

(** Source for [normalised_finite_function_cover_budget]: supporting
    numerical-sum cube budget in 2.10.29,
    p. 195, keeping every finite function
    as its own cover index. *)
Lemma normalised_finite_function_cover_budget (R : realType) (I J : finType) (w : J -> R) (C : R) :
  (0<=C)%R -> (forall j, (0<=w j)%R) -> (\sum_j w j= 1)%R ->
  nonnegative_sum setT (fun f : {ffun I -> J}=>(C*\prod_i w (f i))%R%:E)=C%:E.
Proof.
move=> hC hw hsum.
rewrite finite_type_nonnegative_sum; last first.
  move=> f; rewrite lee_fin; apply: mulr_ge0 hC _; apply: prodr_ge0=> i _; exact: hw.
by rewrite sumEFin -mulr_sumr (normalised_finite_function_weight_sum I hsum) mulr1.
Qed.
