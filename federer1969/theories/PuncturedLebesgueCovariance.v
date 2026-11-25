(** Federer (1969), 2.7.16, printed p. 135: "Thus L^n is |det|^{-1}
    covariant with respect to the action of GL(n, R) on R^n. (This action is
    not transitive, but a transitive action results through replacement of
    R^n by R^n ~ {0}, which really does not matter because L^n{0} = 0.)" and
    "L^n is invariant with respect to the action of SL(n, R)". Here n >= 1
    and X = R^n ~ {0} carries the relative topology (set_type). The measure
    over X is the restriction phi(T) = L^n(T) of L^n to subsets T of X
    (punctured_lebesgue). The module proves that phi is a |det|^{-1}
    covariant measure for the action of GL(n, R) on X, and an invariant
    measure for the action of SL(n, R), in the sense of 2.7.1, p. 122: phi
    is the K(X) regular measure associated with the monotone Daniell
    integral u |-> int u' dL^n on K(X), where u' is u extended by 0 to R^n.
    Since L^n{0} = 0, phi is the image of L^n under a retraction of R^n onto
    X, and L^n is the image of phi under the inclusion of X; hence phi is a
    Borel regular measure representing that integral (2.4.18, p. 90). The
    K(X) regular measure representing the integral (2.5.3, p. 94) is a Radon
    measure (2.5.14, p. 107), hence Borel regular, and the two coincide by
    RepresentingMeasureComparison.v, since X is a locally compact Hausdorff
    metric space with a countable base covered by the open sets {x : 1/(k+1)
    < |x| < k} with compact closure. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis Hom HomInner
  EuclideanCoordinateTopology TopologicalBorel BorelRegularMeasureUP ContinuousBorelPreimages
  MeasureUP MeasureBasic MeasureSplit MeasurePushforward CountableOpenBaseUP
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MonotoneDaniellIntegralUP CovariantIntegralUP SubtypeCompactHausdorff
  IsotropyGroupTopology EuclideanLebesgueDimensions EuclideanAdditiveGroup EuclideanLebesgueHaar
  EuclideanLinearMaps EuclideanLinearGroupCovariance HomSpaceTopology LinearGroupTopology
  LinearGroupSealed GeneralLinearPunctured SpecialLinearTopology MeasureIntegralUP MeasurableFunctionUP
  PartialFunctionUP PartialFunctionPrecomposition SummableRealFunctionUP MeasureIntegralGraphEquivalence
  PushforwardIntegral PushforwardMeasurabilityTransfer CompactSupportSummability CovariantMeasureImage
  RegularDaniellRepresentation CompactSupportCountableRadon RadonBorelRegularity
  RepresentingMeasureComparison ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PuncturedMeasure.
Variable R : realType.
Variable k : nat.
Local Notation n := k.+1.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation X := (set_type (~` [set (0 : E)])).
Local Notation Leb := (@euclidean_lebesgue_measure R n).

(** Source for [punctured_point]: the point e_1 of R^n ~ {0}, n >= 1,
    supporting Federer 2.7.16, p. 135. Definition. *)
Definition punctured_point : X.
Proof.
refine (exist _ (@coordinate_basis R n ord0 : E) (mem_set _)).
move=> /= h; have := congr1 (fun x : V => x ord0) h.
by rewrite /coordinate_basis !ffunE eqxx => /eqP; rewrite oner_eq0.
Defined.

(** Source for [punctured_retraction]: a retraction of R^n onto
    R^n ~ {0}, mapping 0 to e_1, supporting "which really does not
    matter because L^n{0} = 0", Federer 2.7.16, p. 135. Definition. *)
Definition punctured_retraction (x : E) : X :=
  if pselect ((~` [set (0 : E)]) x) is left h then exist _ x (mem_set h) else punctured_point.

(** Source for [punctured_retractionK]: the retraction fixes
    R^n ~ {0}, supporting Federer 2.7.16, p. 135. *)
Lemma punctured_retractionK (x : X) : punctured_retraction (set_val x) = x.
Proof.
rewrite /punctured_retraction; case: pselect=> [h|h]; first by apply: val_inj.
by exfalso; apply: h; exact: set_valP.
Qed.

(** Source for [punctured_lebesgue]: L^n as a measure over
    R^n ~ {0}, T |-> L^n(T), Federer 2.7.16, p. 135. Definition. *)
Definition punctured_lebesgue (T : set X) : \bar R := Leb (set_val @` T).

(** Source for [euclidean_origin_null]: L^n{0} = 0, n >= 1, Federer
    2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_origin_null : Leb [set (0 : E)] = 0%:E.
Proof. exact: euclidean_lebesgue_origin_null. Qed.

(** Source for [euclidean_lebesgue_remove_origin]: L^n(S ~ {0}) =
    L^n(S), "which really does not matter because L^n{0} = 0", Federer
    2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_lebesgue_remove_origin (S : set E) : Leb (S `\` [set 0]) = Leb S.
Proof.
have hm := euclidean_lebesgue_is_measure R n.
apply/eqP; rewrite eq_le; apply/andP; split.
- by apply: (measure_mono hm); exact: subDsetl.
- apply: le_trans (measure_binary_cover hm (_ : S `<=` (S `\` [set 0]) `|` [set 0])) _.
    by move=> x hx; case: (pselect (x = 0))=> h; [right|left].
  by rewrite euclidean_origin_null adde0.
Qed.

(** Source for [punctured_lebesgue_pushforward]: the restriction of L^n
    to R^n ~ {0} is the image of L^n under the retraction, since
    L^n{0} = 0, Federer 2.7.16, p. 135, with 2.1.2, p. 54. Supporting
    lemma. *)
Lemma punctured_lebesgue_pushforward : punctured_lebesgue = measure_pushforward punctured_retraction Leb.
Proof.
have hm := euclidean_lebesgue_is_measure R n.
apply: funext=> T; rewrite /punctured_lebesgue /measure_pushforward.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (measure_mono hm)=> _ [x hx <-]; by rewrite /= punctured_retractionK.
- apply: le_trans (measure_binary_cover hm (_ : _ `<=` (set_val @` T) `|` [set 0])) _.
    move=> x /= hx; case: (pselect (x = 0))=> h; [by right|left].
    exists (punctured_retraction x)=> //.
    rewrite /punctured_retraction; case: pselect=> [h1|h1]; first by [].
    by exfalso; apply: h1; exact: h.
  by rewrite euclidean_origin_null adde0.
Qed.

(** Source for [punctured_lebesgue_is_measure]: the restriction of L^n
    to R^n ~ {0} is a measure, Federer 2.1.2, p. 54. Supporting lemma. *)
Lemma punctured_lebesgue_is_measure : is_measure punctured_lebesgue.
Proof.
rewrite punctured_lebesgue_pushforward; apply: measure_pushforward_is_measure.
exact: euclidean_lebesgue_is_measure.
Qed.

(** Source for [punctured_lebesgue_image]: the image of the restriction
    of L^n to R^n ~ {0} under the inclusion is L^n, "which really does
    not matter because L^n{0} = 0", Federer 2.7.16, p. 135. Direct
    formalisation. *)
Theorem punctured_lebesgue_image : measure_pushforward set_val punctured_lebesgue = Leb.
Proof.
apply: funext=> S; rewrite /measure_pushforward /punctured_lebesgue.
rewrite -[in RHS](euclidean_lebesgue_remove_origin S).
congr (Leb _); apply/seteqP; split.
- move=> y [x hx hxy]; rewrite -hxy; split; first exact: hx.
  exact: (set_valP x).
- by move=> x [hx h0]; exists (exist _ x (mem_set h0)).
Qed.

(** Source for [punctured_lebesgue_preimage_measurable]: the inverse
    image in R^n ~ {0} of an L^n measurable set is measurable for the
    restriction of L^n, Federer 2.1.2, p. 54. Supporting lemma. *)
Lemma punctured_lebesgue_preimage_measurable (M : set E) :
  measure_measurable Leb M -> measure_measurable punctured_lebesgue (set_val @^-1` M).
Proof.
move=> hM T; rewrite /punctured_lebesgue (hM (set_val @` T)).
have h1 : set_val @` (T `&` set_val @^-1` M) = (set_val @` T) `&` M.
  apply/seteqP; split.
  - by move=> y [x [hxT hxM] <-]; split=> //; exists x.
  - by move=> y [[x hxT hxy] hyM]; exists x=> //; split=> //; rewrite /= hxy.
have h2 : set_val @` (T `\` set_val @^-1` M) = (set_val @` T) `\` M.
  apply/seteqP; split.
  - by move=> y [x [hxT hxM] <-]; split=> //; exists x.
  - by move=> y [[x hxT hxy] hyM]; exists x=> //; split=> //; rewrite /= hxy.
by rewrite h1 h2.
Qed.

(** Source for [punctured_lebesgue_borel_regular]: the restriction of
    L^n to R^n ~ {0} is Borel regular, Federer 2.2.3, p. 61: open sets
    are inverse images of open subsets of R^n, and the inverse image of
    a Borel hull of T in R^n is a Borel hull of T. Supporting lemma. *)
Lemma punctured_lebesgue_borel_regular : is_borel_regular_measure punctured_lebesgue.
Proof.
have hbr := euclidean_lebesgue_borel_regular R n.
have hm := euclidean_lebesgue_is_measure R n.
split.
- move=> U [O hO <-]; apply: punctured_lebesgue_preimage_measurable.
  exact: (borel_regular_borel_measurable hm hbr (open_borel_set hO)).
- move=> A; have [B' [hAB [hB hAe]]] := borel_regular_cover hbr (set_val @` A).
  exists (set_val @^-1` B'); split; [|split].
  + by move=> x hx; apply: hAB; exists x.
  + apply: (@continuous_borel_preimage X E set_val); last exact: hB.
    exact: set_type_val_continuous.
  + apply/eqP; rewrite eq_le; apply/andP; split.
    * apply: (measure_mono punctured_lebesgue_is_measure)=> x hx; apply: hAB; by exists x.
    * rewrite /punctured_lebesgue hAe; apply: (measure_mono hm).
      by move=> _ [x hx <-].
Qed.

(** Source for [punctured_countable_open_base]: R^n ~ {0} has a
    countable base, the traces of a countable base of R^n, as needed for
    2.5.14, p. 107, in Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma punctured_countable_open_base : exists U : nat -> set X, is_countable_open_base U.
Proof.
have [U hU] := @euclidean_countable_open_base R n.
exists (fun j => set_val @^-1` U j); split.
- move=> j; apply: open_comp; last exact: (countable_base_open hU j).
  by move=> x _; exact: set_type_val_continuous.
- by rewrite (countable_base_empty hU) preimage_set0.
- move=> W [O hO <-] x hx.
  have [i [hi hiO]] := countable_base_refines hU hO hx.
  by exists i; split=> // y hy; exact: hiO.
Qed.

(** Source for [punctured_shell]: the open set
    {x : 1/(j+1) < |x| < j} of R^n ~ {0}, supporting Federer 2.7.16,
    p. 135. Definition. *)
Definition punctured_shell (j : nat) : set X :=
  set_val @^-1` [set x : E | (j.+1%:R)^-1 < `|x| < j%:R].

(** Source for [punctured_shell_cover]: R^n ~ {0} is covered by the
    open sets {x : 1/(j+1) < |x| < j}, each contained in the compact set
    {x : 1/(j+1) <= |x| <= j}, supporting the hypotheses of 2.5.14,
    p. 107, in Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma punctured_shell_cover :
  [/\ forall j, open (punctured_shell j),
    forall j, exists2 C, compact C & punctured_shell j `<=` C &
    forall x : X, exists j, punctured_shell j x].
Proof.
split.
- move=> j; apply: open_comp; last first.
    have -> : [set x : E | (j.+1%:R)^-1 < `|x| < j%:R] =
        (fun x : E => `|x|) @^-1` `](j.+1%:R)^-1, j%:R[ by apply/seteqP; split=> x; rewrite /= in_itv.
    by apply: open_comp; [move=> x _; exact: norm_continuous|exact: interval_open].
  by move=> x _; exact: set_type_val_continuous.
- move=> j; pose C : set E := [set x : E | (j.+1%:R)^-1 <= `|x| <= j%:R].
  exists (set_val @^-1` C); last by move=> x /andP[h1 h2]; rewrite /C /= !ltW.
  apply: set_type_compact_preimage.
  + apply: (subclosed_compact _ (@euclidean_closed_ball_compact R n 0 j%:R)).
    * have -> : C = (fun x : E => `|x|) @^-1` `[(j.+1%:R)^-1, j%:R] by apply/seteqP; split=> x; rewrite /= in_itv.
      apply: preimage_closed; last exact: interval_closed.
      by move=> x _; exact: norm_continuous.
    * by move=> x /andP[_ h]; rewrite /= subr0.
  + move=> x /andP[h1 _] /= hx0; move: h1; rewrite hx0 normr0 leNgt invr_gt0 ltr0n.
    by [].
- move=> x; have hx0 : set_val x != 0 by apply/eqP; have := set_valP x.
  have hpos : 0 < `|set_val x| by rewrite normr_gt0.
  pose t := `|set_val x| + `|set_val x|^-1.
  have ht : 0 <= t by rewrite addr_ge0 ?invr_ge0 ?normr_ge0.
  have /andP[_ htr] := truncn_itv ht.
  exists (Num.truncn t).+1; rewrite /punctured_shell /=; apply/andP; split.
  + rewrite invf_plt ?posrE ?ltr0n //.
    apply: lt_trans (_ : t < _); first by rewrite /t ltr_pwDl // normr_ge0.
    apply: lt_le_trans htr _; by rewrite ler_nat.
  + apply: le_lt_trans htr; by rewrite /t lerDl invr_ge0 normr_ge0.
Qed.

(** Source for [punctured_extension]: u extended by 0 to R^n, for u
    defined on R^n ~ {0}, supporting "replacement of R^n by
    R^n ~ {0}", Federer 2.7.16, p. 135. Definition. *)
Definition punctured_extension (u : X -> R) (x : E) : R :=
  if pselect ((~` [set (0 : E)]) x) is left h then u (exist _ x (mem_set h)) else 0.

(** Source for [punctured_extensionE]: the extension agrees with u on
    R^n ~ {0}, supporting Federer 2.7.16, p. 135. *)
Lemma punctured_extensionE (u : X -> R) (x : X) : punctured_extension u (set_val x) = u x.
Proof.
rewrite /punctured_extension; case: pselect=> [h|h]; first by congr u; apply: val_inj.
by exfalso; apply: h; exact: set_valP.
Qed.

(** Source for [punctured_extension0]: the extension vanishes at 0,
    supporting Federer 2.7.16, p. 135. *)
Lemma punctured_extension0 (u : X -> R) : punctured_extension u 0 = 0.
Proof. by rewrite /punctured_extension; case: pselect=> // h; exfalso; exact: h. Qed.

(** Source for [punctured_extension_compact]: if u in K(R^n ~ {0}),
    then its extension by 0 belongs to K(R^n): the support of u is a
    compact subset of R^n not containing 0, so the extension vanishes
    near 0 and agrees with u near every other point; supporting Federer
    2.7.16, p. 135, with 2.5.13, p. 106. *)
Lemma punctured_extension_compact (u : X -> R) :
  compactly_supported_continuous_functions u ->
  compactly_supported_continuous_functions (punctured_extension u).
Proof.
move=> [hu hS].
pose S := real_function_support u.
have hSc : compact (set_val @` S).
  by apply: continuous_compact hS; apply: continuous_subspaceT=> x; exact: set_type_val_continuous.
have hScl : closed (set_val @` S) by apply: compact_closed hSc; exact: euclidean_hausdorff.
have hsub : [set x : E | punctured_extension u x <> 0] `<=` set_val @` S.
  move=> x hx; have hx0 : (~` [set (0 : E)]) x by move=> h0; apply: hx; rewrite h0 punctured_extension0.
  exists (exist _ x (mem_set hx0))=> //; apply: subset_closure=> /=.
  by rewrite -(punctured_extensionE u (exist _ x (mem_set hx0))).
have hsupp : real_function_support (punctured_extension u) `<=` set_val @` S.
  have he : set_val @` S = closure (set_val @` S) by exact: (closure_id _).1 hScl.
  by rewrite he; exact: closureS.
split; last by apply: (subclosed_compact (@real_function_support_closed R E _) hSc).
move=> x; case: (pselect (x = 0))=> [hx0|hx0].
- have hN : nbhs x (~` (set_val @` S)).
    apply: open_nbhs_nbhs; split; first by apply: closed_openC.
    by rewrite hx0=> -[y _ hy]; exact: (set_valP y hy).
  move=> A hA; rewrite /= nbhs_simpl /=.
  apply: (@filterS _ _ (nbhs_filter _) _ _ _ hN)=> y hy /=.
  have hy0 : punctured_extension u y = 0.
    by apply: contrapT=> hne; apply: hy; apply: hsupp; apply: subset_closure.
  have hx0' : punctured_extension u x = 0 by rewrite hx0 punctured_extension0.
  by rewrite hy0 -hx0'; exact: nbhs_singleton hA.
- have hxX : (~` [set (0 : E)]) x by [].
  pose x' : X := exist _ x (mem_set hxX).
  move=> A hA; rewrite /= nbhs_simpl /=.
  have hA' : nbhs (u x') A by rewrite -(punctured_extensionE u x'); exact: hA.
  have := hu x' A hA'; rewrite /= nbhs_simpl /= (@nbhsE X)=> -[W [[O hO hOW] hWx] hWA].
  have hOx : O x by rewrite -hOW in hWx.
  have hN : nbhs x (O `&` ~` [set (0 : E)]).
    apply: open_nbhs_nbhs; split; last by split.
    apply: openI; first exact: hO.
    exact: (@punctured_space_open R n).
  apply: (@filterS _ _ (nbhs_filter _) _ _ _ hN)=> y [hyO hy0] /=.
  pose y' : X := exist _ y (mem_set hy0).
  rewrite -[y]/(set_val y') punctured_extensionE; apply: hWA; rewrite -hOW.
  exact: hyO.
Qed.

Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KE := (@compactly_supported_continuous_functions R E).
Local Notation lambda := (@euclidean_lebesgue_integral R n).

(** Source for [punctured_integral]: the integral u |-> int u dL^n on
    K(R^n ~ {0}), u extended by 0, Federer 2.7.16, p. 135, with 2.5.13,
    p. 106. Definition. *)
Definition punctured_integral (u : X -> R) : R := lambda (punctured_extension u).

(** Source for [extended_increases_to_constant]: a constant sequence
    increases to its value, Federer 2.1.1, p. 51. Supporting lemma. *)
Lemma extended_increases_to_constant (a : \bar R) : extended_increases_to (fun _ : nat => a) a.
Proof.
split; first by move=> m p _; exact: lexx.
by split=> [b hb|b hb]; exists 0%N.
Qed.

(** Source for [punctured_integral_monotone]: u |-> int u' dL^n is a
    monotone Daniell integral on K(R^n ~ {0}), Federer 2.5.2, p. 92,
    because extension by 0 preserves the operations, the order and
    increasing convergence. Supporting lemma for 2.7.16, p. 135. *)
Lemma punctured_integral_monotone : is_monotone_daniell_integral KX punctured_integral.
Proof.
have [hadd hscale hmono hinc] := @euclidean_lebesgue_integral_monotone R n.
have hext (F : R -> R -> R) (f g : X -> R) : F 0 0 = 0 ->
    punctured_extension (fun x => F (f x) (g x)) =
    (fun y => F (punctured_extension f y) (punctured_extension g y)).
  move=> hF; apply: funext=> y; rewrite /punctured_extension.
  by case: pselect.
split.
- move=> f g hf hg; rewrite /punctured_integral (hext (fun a b => a + b) f g (addr0 0)).
  exact: hadd (punctured_extension_compact hf) (punctured_extension_compact hg).
- move=> c f hc hf; rewrite /punctured_integral.
  rewrite (hext (fun a b => c * a) f f (mulr0 c)).
  exact: hscale hc (punctured_extension_compact hf).
- move=> f g hf hg hfg; apply: hmono; try exact: punctured_extension_compact.
  by move=> y; rewrite /punctured_extension; case: pselect=> // h; exact: hfg.
- move=> f g hf hg hfg; apply: hinc; first by move=> m; exact: punctured_extension_compact.
    exact: punctured_extension_compact.
  move=> y; rewrite /punctured_extension; case: pselect=> h; first exact: hfg.
  exact: extended_increases_to_constant.
Qed.

(** Source for [punctured_integral_covariant]: int (u o A_f)' dL^n =
    |det f|^{-1} int u' dL^n for f in GL(n, R) and u in
    K(R^n ~ {0}), since (u o A_f)' = u' o f, Federer 2.7.16, p. 135.
    Supporting lemma. *)
Lemma punctured_integral_covariant (u : X -> R) (g : set_type (linear_group (@euclidean_inner_productP R n)
    (@coordinate_basisP R n))) :
  KX u -> punctured_integral (u \o punctured_linear_action g) =
    `|general_linear_det g|^-1 * punctured_integral u.
Proof.
move=> hu.
pose f := hom_as_linear (set_val g : Hom V V).
have he : punctured_extension (u \o punctured_linear_action g) = punctured_extension u \o (f : E -> E).
  apply: funext=> x /=; case: (pselect (x = 0))=> [->|hx0].
  - rewrite !punctured_extension0.
    have h0 : (set_val g : Hom V V) 0 = 0 by exact: (linear0 f).
    by rewrite h0 punctured_extension0.
  - pose x' : X := exist _ x (mem_set hx0).
    rewrite -[x]/(set_val x') punctured_extensionE /=.
    have -> : (f : E -> E) (set_val x') = set_val (punctured_linear_action g x') by [].
    by rewrite punctured_extensionE.
rewrite /punctured_integral he.
exact: (euclidean_lebesgue_linear_integral (general_linear_det_nonzero g) (punctured_extension_compact hu)).
Qed.

(** Source for [punctured_lebesgue_represents]: the restriction of L^n
    to R^n ~ {0} represents u |-> int u' dL^n on K(R^n ~ {0}): by
    2.4.18, p. 90, int u dphi = int u' d(i_# phi) = int u' dL^n for the
    inclusion i, Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma punctured_lebesgue_represents : is_real_integral_functional punctured_lebesgue KX punctured_integral.
Proof.
move=> u hu.
have hue := punctured_extension_compact hu.
have hI := @euclidean_lebesgue_integral_represents R n _ hue.
rewrite -punctured_lebesgue_image in hI.
have hm := punctured_lebesgue_is_measure.
have hmE := euclidean_lebesgue_is_measure R n.
have hbr := euclidean_lebesgue_borel_regular R n.
have hBE : forall A, borel_set A -> measure_measurable Leb A.
  by move=> A hA; exact: (borel_regular_borel_measurable hmE hbr hA).
have hmeasE := @continuous_real_integrand_measurable R E Leb hmE hBE _ hue.1.
have hinj : injective (set_val : X -> E) by move=> a b h; apply: val_inj; exact: h.
have hmeas : is_measure_measurable_function punctured_lebesgue
    (partial_function_precompose set_val (real_total_integrand (punctured_extension u))).
  apply: measurable_function_pushforward_precompose hinj _.
  by rewrite punctured_lebesgue_image.
have hP := (measure_pushforward_integral_iff hm hmeas _).2 hI.
apply: (measure_integral_graph_equivalent _ hP)=> x y.
have he : punctured_extension u \o set_val = u by apply: funext=> z; exact: punctured_extensionE.
by rewrite (precompose_total_integrand_graph set_val (punctured_extension u) x y) he.
Qed.

(** Source for [punctured_lebesgue_function_lattice_regular]: the
    restriction of L^n to R^n ~ {0} is K(R^n ~ {0}) regular, Federer
    2.5.3, p. 94: it coincides with the K(R^n ~ {0}) regular measure
    psi associated with u |-> int u' dL^n, because psi is Radon (2.5.14,
    p. 107), hence Borel regular, and two Borel regular measures
    representing the same integral agree (RepresentingMeasureComparison.v).
    Supporting theorem for 2.7.16, p. 135. *)
Theorem punctured_lebesgue_function_lattice_regular : is_function_lattice_regular KX punctured_lebesgue.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hne : exists f, KX f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [psi [hpsi [hpsiA [hpsir _]]]] := monotone_daniell_regular_representation hL punctured_integral_monotone hne.
have [U hU] := punctured_countable_open_base.
have hH := @punctured_space_hausdorff R n.
have hlc := @punctured_space_locally_compact R n.
have hrad := compact_support_regular_countable_base_radon hpsi hpsiA hpsir hH hlc hU.
have hpb := radon_borel_regular hpsi hrad.
have [hWo hWc hWT] := punctured_shell_cover.
have he := represented_borel_regular_scaled hH hlc hU hWo hWc hWT punctured_lebesgue_is_measure hpsi
  punctured_lebesgue_borel_regular hpb punctured_lebesgue_represents hpsiA ltr01 (fun f _ => esym (mul1r _)).
have -> : punctured_lebesgue = psi by apply: funext=> S; rewrite he mul1e.
exact: hpsir.
Qed.

(** Source for [punctured_lebesgue_covariant]: "Thus L^n is |det|^{-1}
    covariant with respect to the action of GL(n, R) on R^n. (This
    action is not transitive, but a transitive action results through
    replacement of R^n by R^n ~ {0}, which really does not matter because
    L^n{0} = 0.)", Federer 2.7.16, p. 135: the restriction of L^n to
    R^n ~ {0}, n >= 1, is a |det|^{-1} covariant measure for the
    transitive action of GL(n, R) on R^n ~ {0} in the sense of 2.7.1,
    p. 122. Direct formalisation. *)
Theorem punctured_lebesgue_covariant :
  is_covariant_measure (@punctured_linear_action R n) (fun g => `|general_linear_det g|^-1)
    punctured_lebesgue.
Proof.
exists punctured_integral; split.
- exact: punctured_integral_monotone.
- by move=> u g hu; exact: punctured_integral_covariant.
- exact: punctured_lebesgue_is_measure.
- exact: punctured_lebesgue_represents.
- exact: punctured_lebesgue_function_lattice_regular.
Qed.

(** Source for [punctured_lebesgue_special_linear_invariant]: "L^n is
    invariant with respect to the action of SL(n, R)", Federer 2.7.16,
    p. 135, for the action on R^n ~ {0}, in the sense of 2.7.1, p. 122.
    Direct formalisation. *)
Theorem punctured_lebesgue_special_linear_invariant :
  is_invariant_measure (@special_linear_punctured_action R n) punctured_lebesgue.
Proof.
exists punctured_integral; split.
- exact: punctured_integral_monotone.
- move=> u s hu; rewrite /special_linear_punctured_action.
  rewrite (punctured_integral_covariant (set_val s) hu).
  by have := set_valP s; rewrite /special_linear /= => ->; rewrite normr1 invr1.
- exact: punctured_lebesgue_is_measure.
- exact: punctured_lebesgue_represents.
- exact: punctured_lebesgue_function_lattice_regular.
Qed.

End PuncturedMeasure.
