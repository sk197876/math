(** Federer (1969), 2.5.8, p. 100: null-norm functions must be annihilated.
    This is Federer's own correction, erratum p. 2, book p. 100 line 3. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic
  FunctionLatticeSeminormUP VectorFunctionLattice TotalScalarLpUP TotalScalarLpLattice
  TotalScalarLpAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_null_respecting_functional_almost_equal]: supporting use
    of the hypothesis added to Federer 2.5.8, p. 100 line 3, erratum p. 2
    Almost equal total Lp functions have equal values. *)
Lemma lp_null_respecting_functional_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (A : (X -> R) -> R) :
  1 <= p -> is_linear_functional_on_functions (total_scalar_lp mu p) A ->
  (forall f, total_scalar_lp mu p f -> total_scalar_lp_norm mu p f=0 -> A f=0%R) ->
  forall f g, total_scalar_lp mu p f -> total_scalar_lp mu p g ->
    measure_almost_everywhere mu [set x | f x=g x] -> A f=A g.
Proof.
move=> hp hA hnull f g hf hg he.
have hd := @total_scalar_lp_subtract R X mu hm p f g hf hg.
have hz : total_scalar_lp_norm mu p (fun x => (f x-g x)%R)=0.
  apply: (@total_scalar_lp_almost_zero_norm R X mu hm p _ hd).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  change ((f x-g x)%R=0%R); by rewrite hx subrr.
have ha := hnull _ hd hz.
rewrite (@vector_lattice_additive_difference R X (total_scalar_lp mu p) A
  (@total_scalar_lp_vector_lattice R X mu hm p hp) hA.1 f g hf hg) in ha.
by apply/eqP; rewrite -subr_eq0 ha.
Qed.
