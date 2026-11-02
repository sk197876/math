(** Federer (1969), 2.5.11, p. 102: on the vertical line {u} x Y_2 the L
    regular measure phi of lambda agrees with the image of beta_2 under v
    mapped to (u,v), and on the horizontal line Y_1 x {v} it agrees with the
    image of beta_1 under u mapped to (u,v). This makes precise the
    displayed integrals integral k(u,v) d beta_2 v and integral k(u,v) d
    beta_1 u. Federer deduces them from L_1(phi)=L; here they follow from
    the two envelope estimates of 2.5.2, p. 92, the maximality law of the
    product measure in 2.6.1, p. 115, and the level estimate of 2.5.3, p.
    94. This is a documented variation of the proof route, not a change of
    the statement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CardinalSuccessorUP CardinalMeasureUP CardinalMeasureLaws
  CardinalProductExample MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  MeasurePushforward MeasureRestriction CountingMeasure ProductMeasureUP ProductMeasure
  FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellCoverUP
  RegularDaniellEnvelope FunctionLatticeRegularityUP RealIntegralFunctionalUP RealIntegralFunctional
  FunctionLatticeLevelMeasurability RepresentedLatticeClosedLevels
  CharacteristicFunctionUP CharacteristicFunctionSealed DaniellEnvelopeBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

Section Strips.
Variable R : realType.
Variables J1 J2 : choiceType.
Hypothesis h1 : is_cardinal_successor (@setT nat) (@setT J1).
Hypothesis h2 : is_cardinal_successor (@setT J1) (@setT J2).
Variable phi : set (J1 * J2) -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hA : is_real_integral_functional phi (@example_lattice R J1 J2 h1) (@example_lambda R J1 J2 h1).
Hypothesis hr : is_function_lattice_regular (@example_lattice R J1 J2 h1) phi.

Local Notation beta1 := (@example_beta1 R J1).
Local Notation beta2 := (@example_beta2 R J1 J2).
Local Notation hb1 := (@example_beta1_measure R J1).
Local Notation hb2 := (@example_beta2_measure R J1 J2 h1).
Local Notation nu1 := (@example_nu1 R J1 J2 h1).
Local Notation nu2 := (@example_nu2 R J1 J2).
Local Notation L := (@example_lattice R J1 J2 h1).
Local Notation hL := (@example_lattice_is_lattice R J1 J2 h1).
Local Notation lambda := (@example_lambda R J1 J2 h1).
Local Notation chi := (@example_rectangle_characteristic R J1 J2).

(** Source for [chi_value]: supporting unfolding of the rectangle
    characteristic function of Federer 2.5.11, p. 102, to the
    characteristic function of 2.3.1, p. 60, defined in
    CharacteristicFunctionSealed.v. *)
Lemma chi_value (A : set J1) (B : set J2) (x : J1 * J2) :
  chi A B x = CharacteristicFunction.value R (A `*` B) x.
Proof. by []. Qed.

(** Source for [example_envelope]: the suiting-sequence envelope law
    of 2.5.2, p. 92, for the L regular measure phi of Federer 2.5.11,
    p. 102, by the uniqueness in 2.5.3, p. 94. *)
Lemma example_envelope : is_daniell_cover_envelope L lambda phi.
Proof. exact (regular_representing_measure_envelope hL hm hA hr). Qed.

(** Source for [example_characteristic_nonnegative]: supporting
    nonnegativity of the rectangle characteristic functions used as
    lattice tests in Federer 2.5.11, p. 102. *)
Lemma example_characteristic_nonnegative (A : set J1) (B : set J2) :
  function_nonnegative (chi A B).
Proof.
move=> x; case: (pselect ((A `*` B) x))=> hx.
- by rewrite chi_value (characteristic_on_set (CharacteristicFunction.laws _ _) hx) ler01.
- by rewrite chi_value (characteristic_off_set (CharacteristicFunction.laws _ _) hx) lexx.
Qed.

(** Source for [example_characteristic_level]: a rectangle is the
    closed unit level of its characteristic function, supporting the
    measurability of the lines in Federer 2.5.11, p. 102, by 2.5.3. *)
Lemma example_characteristic_level (A : set J1) (B : set J2) :
  A `*` B = [set x | (1 <= chi A B x)%R].
Proof.
apply/seteqP; split=> x hx.
- by rewrite /= chi_value (characteristic_on_set (CharacteristicFunction.laws _ _) hx) lexx.
- apply: contrapT=> hn; move: hx.
  by rewrite /= chi_value (characteristic_off_set (CharacteristicFunction.laws _ _) hn) ler10.
Qed.

(** Source for [vertical_embedding]: the map v mapped to (u,v) whose
    image is the vertical line {u} x Y_2 in Federer 2.5.11, p. 102. *)
Definition vertical_embedding (u : J1) (v : J2) : J1 * J2 := (u, v).

(** Source for [horizontal_embedding]: the map u mapped to (u,v) whose
    image is the horizontal line Y_1 x {v} in Federer 2.5.11, p. 102. *)
Definition horizontal_embedding (v : J2) (u : J1) : J1 * J2 := (u, v).

(** Source for [vertical_image]: the image measure of beta_2 on the
    vertical line, Federer 2.1.2, p. 54, for the integral
    integral k(u,v) d beta_2 v in 2.5.11, p. 102. *)
Definition vertical_image (u : J1) : set (J1 * J2) -> \bar R :=
  measure_pushforward (vertical_embedding u) beta2.

(** Source for [horizontal_image]: the image measure of beta_1 on the
    horizontal line, Federer 2.1.2, p. 54, for the integral
    integral k(u,v) d beta_1 u in 2.5.11, p. 102. *)
Definition horizontal_image (v : J2) : set (J1 * J2) -> \bar R :=
  measure_pushforward (horizontal_embedding v) beta1.

(** Source for [vertical_embedding_injective]: supporting injectivity
    of the coordinate map in Federer 2.5.11, p. 102. *)
Lemma vertical_embedding_injective (u : J1) : injective (vertical_embedding u).
Proof. by move=> a b []. Qed.

(** Source for [horizontal_embedding_injective]: supporting injectivity
    of the coordinate map in Federer 2.5.11, p. 102. *)
Lemma horizontal_embedding_injective (v : J2) : injective (horizontal_embedding v).
Proof. by move=> a b []. Qed.

(** Source for [vertical_image_measure]: the image of beta_2 is a
    measure, Federer 2.1.2, p. 54. *)
Lemma vertical_image_measure (u : J1) : is_measure (vertical_image u).
Proof. exact (measure_pushforward_is_measure _ hb2). Qed.

(** Source for [horizontal_image_measure]: the image of beta_1 is a
    measure, Federer 2.1.2, p. 54. *)
Lemma horizontal_image_measure (v : J2) : is_measure (horizontal_image v).
Proof. exact (measure_pushforward_is_measure _ hb1). Qed.

(** Source for [vertical_image_le_nu1]: the image of beta_2 on the
    vertical line is dominated by alpha_1 x beta_2, by the maximality
    law of the Cartesian product in Federer 2.6.1, p. 115, since the
    image is bounded on every measurable rectangle by the product. *)
Lemma vertical_image_le_nu1 (u : J1) (S : set (J1 * J2)) : vertical_image u S <= nu1 S.
Proof.
apply: (product_measure_greatest_law (product_measure_specification
  (counting_measure_is_measure R J1) hb2) (vertical_image_measure u)).
move=> A B hA' hB; rewrite /vertical_image /measure_pushforward.
case: (pselect (A u))=> hu.
- have -> : vertical_embedding u @^-1` (A `*` B) = B.
    by apply/seteqP; split=> v; [move=> [_ hv]|move=> hv; split].
  apply: lee_pemull (measure_nonnegative hb2 B) _.
  rewrite -(example_counting_singleton R u); apply: (measure_mono (counting_measure_is_measure R J1)).
  by move=> x ->.
- have -> : vertical_embedding u @^-1` (A `*` B) = set0.
    by apply/seteqP; split=> v // [hv _]; exact (hu hv).
  rewrite (measure_empty hb2); apply: mule_ge0.
  + exact: (measure_nonnegative (counting_measure_is_measure R J1) A).
  + exact: (measure_nonnegative hb2 B).
Qed.

(** Source for [horizontal_image_le_nu2]: the image of beta_1 on the
    horizontal line is dominated by beta_1 x alpha_2, by the maximality
    law of the Cartesian product in Federer 2.6.1, p. 115. *)
Lemma horizontal_image_le_nu2 (v : J2) (S : set (J1 * J2)) : horizontal_image v S <= nu2 S.
Proof.
apply: (product_measure_greatest_law (product_measure_specification
  hb1 (counting_measure_is_measure R J2)) (horizontal_image_measure v)).
move=> A B hA' hB; rewrite /horizontal_image /measure_pushforward.
case: (pselect (B v))=> hv.
- have -> : horizontal_embedding v @^-1` (A `*` B) = A.
    by apply/seteqP; split=> u; [move=> [hu _]|move=> hu; split].
  rewrite muleC; apply: lee_pemull (measure_nonnegative hb1 A) _.
  rewrite -(example_counting_singleton R v); apply: (measure_mono (counting_measure_is_measure R J2)).
  by move=> x ->.
- have -> : horizontal_embedding v @^-1` (A `*` B) = set0.
    by apply/seteqP; split=> u // [_ hu]; exact (hv hu).
  rewrite (measure_empty hb1); apply: mule_ge0.
  + exact: (measure_nonnegative hb1 A).
  + exact: (measure_nonnegative (counting_measure_is_measure R J2) B).
Qed.

(** Source for [vertical_image_level_bound]: the level estimate
    t nu{f>t} <= lambda(f) of Federer 2.5.3, p. 94, for the image of
    beta_2, through alpha_1 x beta_2 and the first summand of lambda
    in 2.5.11, p. 102. *)
Lemma vertical_image_level_bound (u : J1) (f : J1 * J2 -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  t%:E * vertical_image u [set x | (t < f x)%R] <= (lambda f)%:E.
Proof.
move=> hf ht.
have ht0 : 0 <= t%:E by rewrite lee_fin ltW.
apply: le_trans (lee_wpmul2l ht0 (vertical_image_le_nu1 u _)) _.
apply: le_trans (represented_lattice_strict_level_bound (@example_nu1_measure R J1 J2 h1)
  (@example_integral1_spec R J1 J2 h1) hf ht) _.
rewrite lee_fin /example_lambda lerDl.
exact: (@monotone_daniell_integral_nonnegative R _ L _ hL
  (real_integral_functional_is_monotone_daniell (@example_nu2_measure R J1 J2) hL
    (@example_integral2_spec R J1 J2 h1)) f hf.1 hf.2).
Qed.

(** Source for [horizontal_image_level_bound]: the level estimate of
    Federer 2.5.3, p. 94, for the image of beta_1, through
    beta_1 x alpha_2 and the second summand of lambda in 2.5.11, p. 102. *)
Lemma horizontal_image_level_bound (v : J2) (f : J1 * J2 -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  t%:E * horizontal_image v [set x | (t < f x)%R] <= (lambda f)%:E.
Proof.
move=> hf ht.
have ht0 : 0 <= t%:E by rewrite lee_fin ltW.
apply: le_trans (lee_wpmul2l ht0 (horizontal_image_le_nu2 v _)) _.
apply: le_trans (represented_lattice_strict_level_bound (@example_nu2_measure R J1 J2)
  (@example_integral2_spec R J1 J2 h1) hf ht) _.
rewrite lee_fin /example_lambda lerDr.
exact: (@monotone_daniell_integral_nonnegative R _ L _ hL
  (real_integral_functional_is_monotone_daniell (@example_nu1_measure R J1 J2 h1) hL
    (@example_integral1_spec R J1 J2 h1)) f hf.1 hf.2).
Qed.

(** Source for [vertical_image_increasing_union]: continuity of the
    image of beta_2 along sequences of sets, Federer 2.5.11, p. 102:
    a two-valued measure of a large countable union is attained by a
    member of the union. *)
Lemma vertical_image_increasing_union (V : nat -> set (J1 * J2)) (u : J1) (c : \bar R) :
  (forall n m, (n <= m)%N -> V n `<=` V m) -> (forall n, vertical_image u (V n) <= c) ->
  vertical_image u (\bigcup_n V n) <= c.
Proof.
move=> _ hc; rewrite /vertical_image /measure_pushforward preimage_bigcup /example_beta2.
have [h|h] := cardinal_measure_values R (@setT J1)
  (\bigcup_(n in setT) vertical_embedding u @^-1` V n).
- rewrite h; exact (le_trans (measure_nonnegative (vertical_image_measure u) (V 0%N)) (hc 0%N)).
- have [n hn] := cardinal_measure_union_large (@aleph_one_sigma_small J1 J2 setT h1)
    ((cardinal_measure_one_iff R _ _).1 h).
  rewrite h -(cardinal_measure_large R hn); exact (hc n).
Qed.

(** Source for [horizontal_image_increasing_union]: continuity of the
    image of beta_1 along sequences of sets, Federer 2.5.11, p. 102. *)
Lemma horizontal_image_increasing_union (V : nat -> set (J1 * J2)) (v : J2) (c : \bar R) :
  (forall n m, (n <= m)%N -> V n `<=` V m) -> (forall n, horizontal_image v (V n) <= c) ->
  horizontal_image v (\bigcup_n V n) <= c.
Proof.
move=> _ hc; rewrite /horizontal_image /measure_pushforward preimage_bigcup /example_beta1.
have [h|h] := cardinal_measure_values R (@setT nat)
  (\bigcup_(n in setT) horizontal_embedding v @^-1` V n).
- rewrite h; exact (le_trans (measure_nonnegative (horizontal_image_measure v) (V 0%N)) (hc 0%N)).
- have [n hn] := cardinal_measure_union_large (@countable_sigma_small J1)
    ((cardinal_measure_one_iff R _ _).1 h).
  rewrite h -(cardinal_measure_large R hn); exact (hc n).
Qed.

(** Source for [vertical_image_le_phi]: the image of beta_2 on the
    vertical line is dominated by phi, by the lower envelope estimate
    of Federer 2.5.2, p. 92, applied in 2.5.11, p. 102. *)
Lemma vertical_image_le_phi (u : J1) (S : set (J1 * J2)) : vertical_image u S <= phi S.
Proof.
apply: (daniell_envelope_dominates hL (@example_lambda_monotone_daniell R J1 J2 h1)
  example_envelope (vertical_image_measure u)).
- exact: vertical_image_level_bound.
- by move=> V c; exact: vertical_image_increasing_union.
Qed.

(** Source for [horizontal_image_le_phi]: the image of beta_1 on the
    horizontal line is dominated by phi, Federer 2.5.11, p. 102. *)
Lemma horizontal_image_le_phi (v : J2) (S : set (J1 * J2)) : horizontal_image v S <= phi S.
Proof.
apply: (daniell_envelope_dominates hL (@example_lambda_monotone_daniell R J1 J2 h1)
  example_envelope (horizontal_image_measure v)).
- exact: horizontal_image_level_bound.
- by move=> V c; exact: horizontal_image_increasing_union.
Qed.

(** Source for [phi_vertical_upper]: on subsets of the vertical line,
    phi is bounded by the image of beta_2, Federer 2.5.11, p. 102: the
    characteristic function of {u} x H, with H the section or Y_2, is
    a lattice test of the upper envelope estimate of 2.5.2, p. 92. *)
Lemma phi_vertical_upper (u : J1) (B : set (J1 * J2)) :
  B `<=` [set u] `*` setT -> phi B <= vertical_image u B.
Proof.
move=> hB; rewrite /vertical_image /measure_pushforward.
case: (pselect (vertical_embedding u @^-1` B #<= @setT J1))=> [hs|hl].
- have hH : measure_measurable beta2 (vertical_embedding u @^-1` B).
    exact (cardinal_measure_small_measurable R (@aleph_one_sigma_small J1 J2 setT h1) hs).
  have [hLc [_ hlam]] := @example_vertical_rectangle_in_lattice R J1 J2 h1 u _ hH.
  rewrite -hlam.
  apply: daniell_envelope_hull_bound example_envelope _ _ (conj hLc (example_characteristic_nonnegative _ _)) _.
  move=> [a b] hab; have [ha _] := hB _ hab.
  rewrite chi_value (characteristic_on_set (CharacteristicFunction.laws _ _)); first exact: lexx.
  by split=> //=; rewrite -ha.
- have [hLc [_ hlam]] := @example_vertical_rectangle_in_lattice R J1 J2 h1 u _
    (measure_measurable_whole hb2).
  rewrite /example_beta2 (cardinal_measure_large R hl).
  rewrite -(@example_beta2_whole R J1 J2 h2) -hlam.
  apply: daniell_envelope_hull_bound example_envelope _ _ (conj hLc (example_characteristic_nonnegative _ _)) _.
  move=> x hx; have hx' := hB _ hx.
  by rewrite chi_value (characteristic_on_set (CharacteristicFunction.laws _ _) hx') lexx.
Qed.

(** Source for [phi_horizontal_upper]: on subsets of the horizontal
    line, phi is bounded by the image of beta_1, Federer 2.5.11, p. 102. *)
Lemma phi_horizontal_upper (v : J2) (B : set (J1 * J2)) :
  B `<=` setT `*` [set v] -> phi B <= horizontal_image v B.
Proof.
move=> hB; rewrite /horizontal_image /measure_pushforward.
case: (pselect (horizontal_embedding v @^-1` B #<= @setT nat))=> [hs|hl].
- have hG : measure_measurable beta1 (horizontal_embedding v @^-1` B).
    exact (cardinal_measure_small_measurable R (@countable_sigma_small J1) hs).
  have [hLc [_ hlam]] := @example_horizontal_rectangle_in_lattice R J1 J2 h1 _ v hG.
  rewrite -hlam.
  apply: daniell_envelope_hull_bound example_envelope _ _ (conj hLc (example_characteristic_nonnegative _ _)) _.
  move=> [a b] hab; have [_ hb] := hB _ hab.
  rewrite chi_value (characteristic_on_set (CharacteristicFunction.laws _ _)); first exact: lexx.
  by split=> //=; rewrite -hb.
- have [hLc [_ hlam]] := @example_horizontal_rectangle_in_lattice R J1 J2 h1 _ v
    (measure_measurable_whole hb1).
  rewrite /example_beta1 (cardinal_measure_large R hl).
  rewrite -(@example_beta1_whole R J1 h1) -hlam.
  apply: daniell_envelope_hull_bound example_envelope _ _ (conj hLc (example_characteristic_nonnegative _ _)) _.
  move=> x hx; have hx' := hB _ hx.
  by rewrite chi_value (characteristic_on_set (CharacteristicFunction.laws _ _) hx') lexx.
Qed.

(** Source for [phi_restrict_vertical]: phi restricted to the vertical
    line {u} x Y_2 is the image of beta_2, Federer 2.5.11, p. 102; this
    is the measure behind integral k(u,v) d beta_2 v. Restriction is
    2.1.2, p. 54. *)
Theorem phi_restrict_vertical (u : J1) :
  measure_restrict phi ([set u] `*` setT) = vertical_image u.
Proof.
apply: funext=> T; rewrite /measure_restrict; apply/le_anti/andP; split.
- have hsub : ([set u] `*` setT) `&` T `<=` [set u] `*` setT by move=> x [hx _].
  apply: (le_trans (phi_vertical_upper hsub)).
  rewrite /vertical_image /measure_pushforward; apply: (measure_mono hb2).
  by move=> v [_ hv].
- apply: (le_trans _ (vertical_image_le_phi u (([set u] `*` setT) `&` T))).
  rewrite /vertical_image /measure_pushforward; apply: (measure_mono hb2).
  by move=> v hv; split=> //; split.
Qed.

(** Source for [phi_restrict_horizontal]: phi restricted to the
    horizontal line Y_1 x {v} is the image of beta_1, Federer 2.5.11,
    p. 102; this is the measure behind integral k(u,v) d beta_1 u. *)
Theorem phi_restrict_horizontal (v : J2) :
  measure_restrict phi (setT `*` [set v]) = horizontal_image v.
Proof.
apply: funext=> T; rewrite /measure_restrict; apply/le_anti/andP; split.
- have hsub : (setT `*` [set v]) `&` T `<=` setT `*` [set v] by move=> x [hx _].
  apply: (le_trans (phi_horizontal_upper hsub)).
  rewrite /horizontal_image /measure_pushforward; apply: (measure_mono hb1).
  by move=> u [_ hu].
- apply: (le_trans _ (horizontal_image_le_phi v ((setT `*` [set v]) `&` T))).
  rewrite /horizontal_image /measure_pushforward; apply: (measure_mono hb1).
  by move=> u hu; split=> //; split.
Qed.

(** Source for [vertical_line_phi_measurable]: the vertical line is
    phi measurable, as the closed unit level of a lattice function,
    Federer 2.5.3, p. 94, applied to {u} x Y_2 in 2.5.11, p. 102. *)
Lemma vertical_line_phi_measurable (u : J1) : measure_measurable phi ([set u] `*` setT).
Proof.
rewrite example_characteristic_level.
exact (represented_lattice_closed_upper_level_measurable hm hA 1%R
  (@example_vertical_line_values R J1 J2 h1 h2 u).1).
Qed.

(** Source for [horizontal_line_phi_measurable]: the horizontal line
    is phi measurable, Federer 2.5.3, p. 94, applied to Y_1 x {v} in
    2.5.11, p. 102. *)
Lemma horizontal_line_phi_measurable (v : J2) : measure_measurable phi (setT `*` [set v]).
Proof.
rewrite example_characteristic_level.
exact (represented_lattice_closed_upper_level_measurable hm hA 1%R
  (@example_horizontal_line_values R J1 J2 h1 v).1).
Qed.

End Strips.
