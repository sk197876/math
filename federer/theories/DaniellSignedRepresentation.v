(** Federer (1969), proof of 2.5.2, p. 93: the final passage from L+ to
    every f in L through its positive and negative parts. We use the book's
    ordered difference f-=f+-f, so no vector-space closure of L is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverMeasure DaniellPositiveRepresentation SummableRealFunctionUP
  SummableRealArithmetic RealIntegralFunctionalUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_cover_represents_lattice]: the complete
    representation conclusion for the constructed envelope in Federer 2.5.2,
    pp. 92–93 This theorem identifies every member's finite integral and
    applies even when the lattice is not closed under negation. *)
Theorem daniell_cover_represents_lattice (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) : is_real_integral_functional mu L A.
Proof.
move=> f hf.
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf).
pose p x := Order.max (f x) 0%R.
pose q x := (p x-f x)%R.
have hpL : L p := function_lattice_positive_part hL hf.
have hp0 : function_nonnegative p by move=> x; rewrite /p le_max lexx orbT.
have hfp : function_le f p by move=> x; rewrite /p le_max lexx.
have hqL : L q := function_lattice_ordered_difference hL hf hpL hfp.
have hq0 : function_nonnegative q by move=> x; rewrite /q subr_ge0; exact: hfp.
have hp : positive_function_lattice L p := conj hpL hp0.
have hq : positive_function_lattice L q := conj hqL hq0.
have hip := daniell_positive_lattice_representation hL hA hm hp.
have hiq := daniell_positive_lattice_representation hL hA hm hq.
have hi := @real_total_integral_subtract R X mu hmeasure p q (A p) (A q) hip hiq.
have hfun : (fun x => (p x-q x)%R)=f.
  by apply: funext=> x; rewrite /q opprB addrCA subrr addr0.
have hadd : (fun x => (f x+q x)%R)=p.
  by apply: funext=> x; rewrite /q addrCA subrr addr0.
have hval := @monotone_daniell_integral_add R X L A hA f q hf hqL.
rewrite hadd in hval.
by rewrite hfun hval addrK in hi.
Qed.
