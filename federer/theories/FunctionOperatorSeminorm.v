(** Federer (1969), 2.5.7, p. 98: the supremum M over the closed unit ball,
    corrected by the erratum p. 2, book p. 98 line 11. This abstract
    supporting argument includes the zero space, whose unit sphere is empty
    but whose unit ball contains zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP LatticeAdditiveFunctional VectorFunctionLattice
  FunctionLatticeSeminormUP FunctionSeminormUnitBound ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_operator_seminorm]: direct corrected supremum
    defining M in Federer 2.5.7, p. 98, erratum p. 2 line 11 The supremum
    uses only the project's sealed bound laws. *)
Definition function_operator_seminorm (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R) :=
  extended_real_sup [set v | exists r, functional_unit_ball_values L A N r /\ v=r%:E].

(** Source for [function_operator_seminorm_nonnegative]: zero belongs to the
    closed ball in Federer 2.5.7, p. 98 This includes a zero seminorm. *)
Lemma function_operator_seminorm_nonnegative (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_linear_functional_on_functions L A)
    (hN : is_finite_function_seminorm L N) :
  0 <= function_operator_seminorm L A N.
Proof.
apply: extended_real_sup_upper; exists 0%R; split=> //.
exists (fun _ => 0%R); split; first exact: hL.2.1.
split; first by rewrite (@function_seminorm_zero R X L N hL hN) ler01.
by rewrite (@lattice_additive_zero R X L A hL.1 hA.1 (fun _ => 0%R) hL.2.1) normr0.
Qed.

(** Source for [function_operator_seminorm_finite_bound]: exact consequence
    of the finiteness hypothesis on M in Federer 2.5.7, p. 98 The bound is
    obtained without assuming definiteness of the seminorm. *)
Theorem function_operator_seminorm_finite_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R)
    (hL : is_vector_function_lattice L) (hA : is_linear_functional_on_functions L A)
    (hN : is_finite_function_seminorm L N) :
  function_operator_seminorm L A N < +oo ->
  exists M : R, function_operator_seminorm L A N=M%:E /\ (0 <= M)%R /\
    forall f, L f -> (`|A f| <= M*N f)%R.
Proof.
move=> ht; have h0 := @function_operator_seminorm_nonnegative R X L A N hL hA hN.
have hs : function_operator_seminorm L A N \is a fin_num.
  rewrite fin_numElt; apply/andP; split=> //.
  exact: lt_le_trans (ltNyr (0%R : R)) h0.
pose M := fine (function_operator_seminorm L A N).
have he : function_operator_seminorm L A N=M%:E by rewrite /M fineK.
exists M; split; first exact: he.
split; first by move: h0; rewrite he lee_fin.
apply: (@unit_bounded_functional_norm_bound R X L A N hL hA hN M)=> f hf hn.
have hu : (`|A f|)%:E <= function_operator_seminorm L A N.
  apply: extended_real_sup_upper; exists `|A f|%R; split=> //.
  exists f; by split=> //; split.
by rewrite he lee_fin in hu.
Qed.

(** Source for [function_operator_seminorm_least_bound]: least bound
    property of M in Federer 2.5.7, p. 98 This supports the later equality
    between M and the representing Lq norm. *)
Lemma function_operator_seminorm_least_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R) (M : R) :
  (0 <= M)%R -> (forall f, L f -> (`|A f| <= M*N f)%R) ->
  function_operator_seminorm L A N <= M%:E.
Proof.
move=> hM hb; apply: extended_real_sup_least=> v [r [[f [hf [hn ->]]] ->]].
rewrite lee_fin; apply: le_trans (hb f hf) _.
case: (eqVneq M 0%R)=> [->|hneq]; first by rewrite !mul0r.
have hpos : (0 < M)%R by rewrite lt_neqAle eq_sym hneq hM.
by rewrite -{2}[M]mulr1 (ler_pM2l hpos).
Qed.
