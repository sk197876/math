(** Federer (1969), 2.5.3, p. 94: L regularity characterises the
    representing measure constructed in 2.5.2. This interface consequence
    transfers the suiting-envelope laws to any measure satisfying Federer's
    abstract regularity and integral laws, without exposing a construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  FunctionLatticeRegularUniqueness RegularDaniellRepresentation RealIntegralFunctionalUP
  RealIntegralFunctional MonotoneDaniellRepresentation DaniellCoverUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_lattice_regular_nonempty]: boundary consequence of
    Federer's finite-hull definition in 2.5.3, p. 94 The finite hull of the
    empty set already supplies a lattice member. *)
Lemma function_lattice_regular_nonempty (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) (hm : is_measure mu) :
  is_function_lattice_regular L mu -> exists f, L f.
Proof.
move=> hr; have hfin : mu set0 < +oo by rewrite (measure_empty hm) ltry.
have [W [_ [[V [hV _]] _]]] := (hr set0).1 hfin.
have [U [hU _]] := hV 0%N.
have [f [t [hf _]]] := hU 0%N.
exists f; exact hf.1.
Qed.

(** Source for [regular_representing_measure_envelope]: complete
    characterisation step in Federer 2.5.3, p. 94 The four later
    consequences can therefore be used with the abstract L-regularity
    premise, rather than a particular implementation. *)
Theorem regular_representing_measure_envelope (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A) :
  is_function_lattice_regular L mu -> is_daniell_cover_envelope L A mu.
Proof.
move=> hr.
have hne := @function_lattice_regular_nonempty R X L mu hm hr.
have hD := @real_integral_functional_is_monotone_daniell R X mu hm L A hL hA.
pose nu := @monotone_daniell_measure R X L A hL hD.
have hn := @monotone_daniell_measure_is_measure R X L A hL hD.
have hB := @monotone_daniell_measure_represents R X L A hL hD.
have hs := @monotone_daniell_measure_lattice_regular R X L A hL hD hne.
have he : mu=nu.
  apply: funext=> S; exact: (@function_lattice_regular_representation_unique R X L A hL mu nu hm hn hA hB hr hs S).
rewrite he; exact: (@monotone_daniell_measure_envelope R X L A hL hD hne).
Qed.
