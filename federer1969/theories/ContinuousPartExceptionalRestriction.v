(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureAlmostBasic MeasureRestriction BorelRegularMeasureUP
  AbsoluteContinuousPartUP AbsoluteContinuousPartBasic VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_exceptional_restriction]: supporting
    measure identity in Federer 2.9.15, pp. 160–161. Once
    E is reference-null and every reference-null subset outside
    E is also numerator-null, the continuous part equals the
    restriction of psi to X minus E. This isolates the printed
    two inequalities from the later geometric covering argument.
    No infinite masses are subtracted. E need not be Borel for
    this supporting identity, although W union P is proved Borel
    separately in the book theorem. *)
Theorem continuous_part_exceptional_restriction (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) (E : set X) :
  is_measure phi -> is_measure psi -> is_measure gamma -> is_borel_regular_measure psi ->
  is_absolutely_continuous_part phi psi gamma -> phi E=0 ->
  (forall T, T `<=` ~` E -> phi T=0 -> psi T=0) ->
  gamma=measure_restrict psi (~` E).
Proof.
move=> hphi hpsi hgamma hrpsi hg hE hnull; apply: funext=> A.
pose C := (~` E) `&` A.
have hgE := @continuous_part_null R X phi psi gamma hpsi hg E hE.
have hdiscard : gamma (A `\` C)=0.
  apply: (@measure_null_subset R X gamma hgamma _ E _ hgE).
  move=> x [hx hn]; apply: contrapT=> hne; apply: hn; by split.
have hgc := @null_remainder_measure_cover_bound R X gamma A C hgamma hdiscard.
have hdom := @continuous_part_dominated R X phi psi gamma hphi hrpsi hg C.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: le_trans hgc hdom.
- apply: (@continuous_part_greatest R X phi psi gamma hg A (psi C))=> B hB hz.
  have hphiT : phi (C `\` B)=0.
    apply: (@measure_null_subset R X phi hphi _ (A `\` B) _ hz).
    by move=> x [[_ hx] hn]; split.
  have hpsiT : psi (C `\` B)=0.
    apply: hnull _ _ hphiT; by move=> x [[hx _] _].
  exact: (@null_remainder_measure_cover_bound R X psi C B hpsi hpsiT).
Qed.
