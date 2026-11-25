(** Concentration on the common core supporting Federer
    (1969), 2.8.20, p. 152; Saks1934 Lemma B
    (6)–(8), p. 258, and Cesari1939 Lemma III,
    p. 306. A constant density on a positive
    finite-area core assigns a prescribed mass to every
    containing rectangle. We specify the resulting measure
    by its laws and prove existence from restriction and
    positive scaling. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction FiniteMeasureScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_core_concentration]: abstract supporting
    measure for the common-core construction in Federer
    2.8.20, p. 152; Saks1934 (6)–(8), p. 258.
    Its total mass and the mass of every containing set
    are the prescribed nonnegative real m. *)
Record is_core_concentration (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E : set X) (m : R) (nu : set X -> \bar R) : Prop := {
  (** Source for [core_concentration_measure]: supporting
      measure law for Federer 2.8.20, p. 152. *)
  core_concentration_measure : is_measure nu;
  (** Source for [core_concentration_measurable]: preservation
      of measurable cells for Federer 2.8.20, p. 152. *)
  core_concentration_measurable : forall S, measure_measurable mu S -> measure_measurable nu S;
  (** Source for [core_concentration_total]: prescribed cost
      of one core for Federer 2.8.20, p. 152. *)
  core_concentration_total : nu setT = m%:E;
  (** Source for [core_concentration_containing]: large mass
      on every cell containing the core, supporting Federer
      2.8.20, p. 152; Saks1934 (7)–(8), p. 258. *)
  core_concentration_containing : forall S, E `<=` S -> nu S = m%:E
}.

(** Source for [core_concentration_exists]: existence of the
    normalized constant-density measure used on one common core
    in the proof supporting Federer 2.8.20, p. 152.
    The implementation occurs only inside this opaque proof;
    no positivity or finiteness of the ambient measure is assumed. *)
Theorem core_concentration_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E : set X) (m : R) :
  is_measure mu -> 0<mu E -> mu E \is a fin_num -> (0<=m)%R ->
  exists nu, is_core_concentration mu E m nu.
Proof.
move=> hm hpos hfin hm0.
pose e := fine (mu E).
have he : mu E = e%:E by rewrite /e fineK.
have he0 : (0<e)%R by move: hpos; rewrite he lte_fin.
pose c := (m/e)%R.
have hc : (0<=c)%R := divr_ge0 hm0 (ltW he0).
pose nu := fun S => c%:E * measure_restrict mu E S.
have hmass : (c%:E * mu E = m%:E)%E.
  by rewrite he -EFinM /c mulfVK ?gt_eqF.
exists nu; constructor.
- exact (@finite_scale_is_measure R X (measure_restrict mu E)
    (measure_restrict_is_measure hm E) c hc).
- move=> S hS T; rewrite /nu (measure_restrict_measurable E hS T) ge0_muleDr //;
    exact (@measure_nonnegative R X (measure_restrict mu E)
      (@measure_restrict_is_measure R X mu hm E) _).
- by rewrite /nu /measure_restrict setIT hmass.
- move=> S hES; rewrite /nu /measure_restrict.
  have -> : E `&` S = E.
    apply/seteqP; split=> [x [hx _]|x hx] //; split=> //; exact: hES x hx.
  exact hmass.
Qed.
