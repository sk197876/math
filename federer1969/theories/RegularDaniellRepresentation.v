(** Federer (1969), 2.5.3, pp. 94–95: L regularity characterises the
    particular measure from 2.5.2. The nonempty-lattice hypothesis is
    explicit: empty L has no F2 hulls, and the separate empty-case
    representation in 2.5.2 cannot be L regular. Downstream results use only
    the sealed measure's laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellRepresentation
  FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness DaniellFiniteHulls DaniellOuterRegularity
  RealIntegralFunctionalUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [monotone_daniell_measure_lattice_regular]: the constructed
    measure's L regularity in Federer 2.5.3, pp. 94–95 The empty lattice is
    excluded for the documented finite-hull obstruction, not by an added
    axiom. *)
Theorem monotone_daniell_measure_lattice_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A) :
  (exists f, L f) ->
  is_function_lattice_regular L (@monotone_daniell_measure R X L A hL hA).
Proof.
move=> hne; exact: (@daniell_cover_lattice_regular R X L A hL
  (@monotone_daniell_measure R X L A hL hA)
  (@monotone_daniell_measure_is_measure R X L A hL hA)
  (@monotone_daniell_measure_represents R X L A hL hA)
  (@monotone_daniell_measure_envelope R X L A hL hA hne)).
Qed.

(** Source for [monotone_daniell_measure_lattice_outer_regular]: Supporting
    Federer 2.5.3, pp. 94–95.It is proved for the same sealed measure. *)
Theorem monotone_daniell_measure_lattice_outer_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A) :
  (exists f, L f) ->
  is_function_lattice_outer_regular L (@monotone_daniell_measure R X L A hL hA).
Proof.
move=> hne; exact: (@daniell_cover_lattice_outer_regular R X L A
  (@monotone_daniell_measure R X L A hL hA)
  (@monotone_daniell_measure_is_measure R X L A hL hA)
  (@monotone_daniell_measure_represents R X L A hL hA)
  (@monotone_daniell_measure_envelope R X L A hL hA hne)).
Qed.

(** Source for [monotone_daniell_regular_representation]: existence and
    uniqueness in the L regular characterisation of Federer 2.5.3, p. 94
    Further approximation and measurability assertions from 2.5.3 are
    separate statements. *)
Theorem monotone_daniell_regular_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_monotone_daniell_integral L A -> (exists f, L f) ->
  exists mu, is_measure mu /\ is_real_integral_functional mu L A /\
    is_function_lattice_regular L mu /\
    forall nu, is_measure nu -> is_real_integral_functional nu L A ->
      is_function_lattice_regular L nu -> forall S, mu S=nu S.
Proof.
move=> hL hA hne; pose mu := @monotone_daniell_measure R X L A hL hA.
have hm := @monotone_daniell_measure_is_measure R X L A hL hA.
have hi := @monotone_daniell_measure_represents R X L A hL hA.
have hr := @monotone_daniell_measure_lattice_regular R X L A hL hA hne.
exists mu; split=> //; split=> //; split=> //.
move=> nu hn hj hs; exact: (@function_lattice_regular_representation_unique R X L A hL mu nu hm hn hi hj hr hs).
Qed.
