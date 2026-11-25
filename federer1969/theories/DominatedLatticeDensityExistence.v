(** Federer (1969), 2.5.9, p. 100: existence of a measurable density with
    essential bound one. This is the existence and norm-bound portion;
    almost uniqueness is separate. The corrected total-domain and
    positive-density conventions are erratum p. 2, book p. 100 lines 21–24. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP CountablyMeasurableUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpFiniteSeminorm LpFunctionalDensityUP LpLinearFunctionalRepresentation
  DominatedLoneExtensionUP DominatedLoneExtension RegularLatticeLoneDensity RealLatticeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_lattice_density_exists]: existence
    and essential-bound conclusions of Federer 2.5.9, p. 100,
    using the corrected positive-density proof. The countably measurable
    ambient space is retained, as required by 2.5.7(ii). *)
Theorem dominated_lattice_density_exists (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_function_lattice_regular L mu -> measure_countably_measurable mu setT ->
  is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) ->
  exists k : X -> R, is_real_lattice_density mu L A k /\
    total_scalar_lp mu +oo k /\ total_scalar_lp_norm mu +oo k <= 1.
Proof.
move=> hF hrep hr hX hA hb.
pose S := @dominated_lone_extension R X L hL F A mu hm hF hrep hr hA hb.
have [hlin [hagree hbound]] := @dominated_lone_extension_specification R X L hL F A mu hm hF hrep hr hA hb.
have hnorm : function_operator_seminorm (total_scalar_lp mu 1) S (finite_total_scalar_lp_norm mu 1) <= 1.
  apply: (@function_operator_seminorm_least_bound R X _ S _ 1%R (ler01)).
  move=> f hf; rewrite mul1r; exact: hbound f hf.
have hfinite := le_lt_trans hnorm (ltry (1%R : R)).
have hc : (1 : \bar R)=+oo -> False by [].
have [_ [k [hk [hNk hu]]]] := @lp_linear_functional_representation R X mu hm 1 +oo S
  (or_intror (or_introl (conj erefl erefl))) hlin hfinite (fun _ => hX) (fun h => False_rect _ (hc h)).
exists k; split.
- split; first exact: hk.1.2.1.
  move=> f hf.
  have hfl := @represented_lattice_in_total_lone R X mu hm L F hrep f hf.
  have hi := hk.2 f hfl; by rewrite /S (hagree f hf) in hi.
- split; first exact: hk.1.
  by rewrite hNk.
Qed.
