(** Federer (1969), 2.7.16, p. 135: "It follows that no nonzero Radon
    measure phi over R^n ~ {0} can be invariant with respect to the action
    of GL(n, R), because phi would be SL(n, R) invariant, hence a positive
    multiple of L^n", for n >= 2. Federer's argument uses the uniqueness of
    invariant measures on the homogeneous space R^n ~ {0} = SL(n,
    R)/(isotropy group), which belongs to items of 2.7 after 2.7.10 that are
    not yet formalised. The proof here is direct. Invariance is read as
    phi(f[T]) = phi(T) for f in GL(n, R) and T a subset of R^n ~ {0}. Let P
    be the open box {x : 1 < x_1 < 2, 0 < x_i < 1 for i > 1} and d the
    linear map halving the second coordinate. Then d[P] is contained in P
    and phi(P) < oo, because the closure of P is a compact subset of R^n ~
    {0}; hence phi(P ~ d[P]) = 0, and the open box Q = {x : 1 < x_1 < 2, 1/2
    < x_2 < 1, 0 < x_i < 1 for i > 2}, contained in P ~ d[P], is phi null.
    By the transitivity of SL(n, R) on R^n ~ {0}, the sets f[Q] with f in
    GL(n, R) form an open cover of R^n ~ {0} by null sets, so every compact
    set is null, and phi = 0 by the inner regularity of the Radon measure
    phi on the open set R^n ~ {0} (2.2.5, p. 62). For n = 1 the assertion is
    false: dx/|x| is GL(1, R) invariant on R ~ {0}. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module tvs.
From mathcomp Require Import finmap functions cardinality lra.
From Federer Require Import RealMetricBackground FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric InnerNormedTopology EuclideanCoordinateTopology
  HomeomorphismUP MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic RadonMeasureUP IsotropyGroupTopology
  EuclideanAdditiveGroup EuclideanLebesgueHaar EuclideanLinearMaps EuclideanLebesgueLinear
  EuclideanLinearGroupCovariance
  SpecialLinearTransitive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OpenBox.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [euclidean_open_box_open]: the open coordinate box
    {x : a_i < x_i < b_i} is open in R^n, supporting Federer 2.7.16,
    p. 135. *)
Lemma euclidean_open_box_open (a b : 'I_n -> R) : open [set x : E | forall i, a i < x i < b i].
Proof.
have he : [set x : E | forall i, a i < x i < b i] =
    \big[setI/setT]_(i < n) [set x : E | a i < x i < b i].
  apply/seteqP; split=> x hx.
  - apply: (big_rec (fun S : set E => S x))=> // i S _ hS; split=> //; exact: hx i.
  - move=> i; move: hx; rewrite (bigD1 i) //=; by move=> [].
rewrite he; apply: big_ind=> [|S S' hS hS'|i _]; [exact: openT|exact: openI|].
have -> : [set x : E | a i < x i < b i] = (fun x : E => (x i : R^o)) @^-1` `](a i), (b i)[.
  by apply/seteqP; split=> x; rewrite /= in_itv.
apply: open_comp; last exact: interval_open.
by move=> x _; exact: euclidean_coordinate_continuous.
Qed.

End OpenBox.

Section InvariantRadon.
Variable R : realType.
Variable k : nat.
Local Notation n := k.+2.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation X := (set_type (~` [set (0 : E)])).

(** Source for [punctured_image_nonzero]: a linear automorphism maps
    R^n ~ {0} into itself, Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma punctured_image_nonzero (g : euclidean_general_linear R n) (x : X) :
  (sval g : E -> E) (set_val x) \in ~` [set (0 : E)].
Proof.
apply: mem_set=> /= h0.
have hinj := (euclidean_det_injective (sval g)).1 (svalP g).
have hx : set_val x <> 0 by have := set_valP x; rewrite /=.
by apply: hx; apply: hinj; rewrite h0 linear0.
Qed.

(** Source for [punctured_action]: the action of GL(n, R) on
    R^n ~ {0}, A(f, x) = f(x), Federer 2.7.16, p. 135. Definition. *)
Definition punctured_action (g : euclidean_general_linear R n) (x : X) : X :=
  exist _ ((sval g : E -> E) (set_val x)) (punctured_image_nonzero g x).

(** Source for [punctured_action_continuous]: each A_f is continuous on
    R^n ~ {0} with the relative topology, Federer 2.7.16, p. 135, with
    2.7.1, p. 121. Supporting lemma. *)
Lemma punctured_action_continuous (g : euclidean_general_linear R n) : continuous (punctured_action g).
Proof.
apply: set_type_continuous_into=> x.
apply: (@continuous_comp X E E set_val (sval g : E -> E)).
- exact: set_type_val_continuous.
- exact: euclidean_linear_continuous.
Qed.

(** Source for [general_linear_inverse]: f^{-1} for f in GL(n, R),
    Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma general_linear_inverse (g : euclidean_general_linear R n) :
  exists h : euclidean_general_linear R n, cancel (punctured_action g) (punctured_action h) /\
    cancel (punctured_action h) (punctured_action g).
Proof.
have hinj := (euclidean_det_injective (sval g)).1 (svalP g).
have [f [hgf hfg]] := euclidean_linear_inverse hinj.
have hdf : euclidean_det f != 0.
  apply/negP=> /eqP h; have := euclidean_det_inverse hgf; rewrite h mul0r=> /eqP.
  by rewrite eq_sym oner_eq0.
exists (exist _ f hdf); split=> x; apply: val_inj; rewrite /= ?hgf ?hfg //.
Qed.

(** Source for [punctured_action_image_open]: A_f maps open subsets of
    R^n ~ {0} onto open subsets, Federer 2.7.16, p. 135. Supporting
    lemma. *)
Lemma punctured_action_image_open (g : euclidean_general_linear R n) (U : set X) :
  open U -> open (punctured_action g @` U).
Proof.
move=> hU; have [h [hgh hhg]] := general_linear_inverse g.
have -> : punctured_action g @` U = punctured_action h @^-1` U.
  apply/seteqP; split=> y /=.
  - by move=> [x hx <-]; rewrite hgh.
  - by move=> hy; exists (punctured_action h y)=> //; rewrite hhg.
apply: open_comp hU=> y _; exact: punctured_action_continuous.
Qed.

(** Source for [general_linear_transitive]: GL(n, R) acts transitively
    on R^n ~ {0}, n >= 2, since SL(n, R) does, Federer 2.7.16, p. 135.
    Supporting lemma. *)
Lemma general_linear_transitive (x y : X) : exists g, punctured_action g x = y.
Proof.
have hx : set_val x != 0 by apply/eqP; have := set_valP x.
have hy : set_val y != 0 by apply/eqP; have := set_valP y.
have [f [hdf hfx]] := special_linear_transitive hx hy.
have hdf' : euclidean_det f != 0 by rewrite hdf oner_eq0.
by exists (exist _ f hdf'); apply: val_inj.
Qed.

(** Source for [punctured_box]: the set {x in R^n ~ {0} : a_i < x_i < b_i},
    supporting Federer 2.7.16, p. 135. Definition. *)
Definition punctured_box (a b : 'I_n -> R) : set X := set_val @^-1` [set x : E | forall i, a i < x i < b i].

(** Source for [punctured_box_open]: such boxes are open in
    R^n ~ {0}, supporting Federer 2.7.16, p. 135. *)
Lemma punctured_box_open (a b : 'I_n -> R) : open (punctured_box a b).
Proof.
apply: open_comp; last exact: euclidean_open_box_open.
by move=> x _; exact: set_type_val_continuous.
Qed.

(** Source for [box_lower]: lower corner (1, 0, ..., 0) of the box P,
    supporting Federer 2.7.16, p. 135. Definition. *)
Definition box_lower : 'I_n -> R := fun i => if i == ord0 then 1 else 0.

(** Source for [box_upper]: upper corner of the box P, with the second
    coordinate bounded by t, supporting Federer 2.7.16, p. 135.
    Definition. *)
Definition box_upper (t : R) : 'I_n -> R :=
  fun i => if i == ord0 then 2 else if i == second_index k then t else 1.

(** Source for [box_lower_half]: lower corner of the box Q, supporting
    Federer 2.7.16, p. 135. Definition. *)
Definition box_lower_half : 'I_n -> R := fun i => if i == second_index k then 2^-1 else box_lower i.

(** Source for [punctured_box_finite]: the box P has finite measure for
    every Radon measure over R^n ~ {0}, since its closure is a compact
    subset of R^n ~ {0}; supporting Federer 2.7.16, p. 135. *)
Lemma punctured_box_finite (xi : set X -> \bar R) : is_measure xi -> is_radon_measure xi ->
  (xi (punctured_box box_lower (box_upper 1)) < +oo)%E.
Proof.
move=> hm hr.
pose C := [set x : E | forall i, box_lower i <= x i <= box_upper 1 i].
have hC : compact C := @euclidean_closed_box_compact R n box_lower (box_upper 1).
have hC0 : C `<=` ~` [set (0 : E)].
  move=> x hx /= h0; have := hx ord0; rewrite h0 /box_lower /box_upper eqxx.
  by rewrite /= ffunE ler10.
have hc := set_type_compact_preimage hC hC0.
apply: le_lt_trans (@measure_mono R X xi hm _ (set_val @^-1` C) _) (radon_compact_finite hr hc).
move=> x /= hx i; have /andP[h1 h2] := hx i; by rewrite !ltW.
Qed.

(** Source for [no_general_linear_invariant_radon]: Federer 2.7.16,
    p. 135, "no nonzero Radon measure phi over R^n ~ {0} can be invariant
    with respect to the action of GL(n, R)", n >= 2: every Radon measure
    phi over R^n ~ {0} with phi(f[T]) = phi(T) for f in GL(n, R) and
    T a subset of R^n ~ {0} vanishes. Direct formalisation; the proof
    differs from Federer's. *)
Theorem no_general_linear_invariant_radon (xi : set X -> \bar R) :
  is_measure xi -> is_radon_measure xi ->
  (forall g T, xi (punctured_action g @` T) = xi T) -> forall T, xi T = 0%E.
Proof.
move=> hm hr hinv.
pose d := euclidean_diagonal_map (@second_scaling R k 2^-1).
have hd : euclidean_det d != 0 by rewrite second_scaling_det invr_eq0 pnatr_eq0.
pose dg : euclidean_general_linear R n := exist _ d hd.
pose P := punctured_box box_lower (box_upper 1).
pose Q := punctured_box box_lower_half (box_upper 1).
have hdP : punctured_action dg @` P = punctured_box box_lower (box_upper 2^-1).
  apply/seteqP; split=> y /=.
  - move=> [x hx <-] i; rewrite /= /euclidean_diagonal ffunE /second_scaling.
    have /andP[h1 h2] := hx i; rewrite /box_lower /box_upper in h1 h2 *.
    have hne : second_index k != ord0 by [].
    case: (eqVneq i (second_index k))=> [hj|hj].
    + rewrite hj (negbTE hne) eqxx in h1 h2 *.
      have h2' : (2 : R)^-1 * set_val x (second_index k) < 2^-1 * 1 by rewrite ltr_pM2l ?invr_gt0 ?ltr0n.
      by rewrite mulr1 in h2'; rewrite mulr_gt0 ?invr_gt0 ?ltr0n.
    + by rewrite mul1r (negbTE hj) in h2 *; rewrite h1 h2.
  - move=> hy.
    pose x : V := [ffun i => if i == second_index k then 2 * set_val y i else set_val y i].
    have hne : ((ord0 : 'I_n) == second_index k) = false by [].
    have hx0' : x ord0 = set_val y ord0 by rewrite /x ffunE hne.
    have hy0 := hy ord0; rewrite /box_lower /box_upper eqxx in hy0.
    have hx0 : x \in ~` [set (0 : E)].
      apply: mem_set=> /= h0; rewrite h0 ffunE in hx0'.
      by move: hy0; rewrite -hx0'; lra.
    exists (exist _ x hx0).
    + move=> i; rewrite /= /x ffunE; have /andP[h1 h2] := hy i; rewrite /box_lower /box_upper in h1 h2 *.
      have hne' : second_index k != ord0 by [].
      case: (eqVneq i (second_index k))=> [hj|hj].
      * rewrite hj (negbTE hne') eqxx in h1 h2 *.
        have h3 : 2 * set_val y (second_index k) < 2 * 2^-1 by rewrite ltr_pM2l ?ltr0n.
        rewrite mulfV ?pnatr_eq0 // in h3.
        by apply/andP; split=> //; rewrite mulr_gt0 ?ltr0n.
      * rewrite (negbTE hj) in h2; case: (i == ord0) in h1 h2 *; by rewrite h1 h2.
    + apply: val_inj; apply/ffunP=> i; rewrite /= /euclidean_diagonal !ffunE /second_scaling /x ?ffunE.
      case: (eqVneq i (second_index k))=> _; last by rewrite mul1r.
      by rewrite mulrA mulVf ?mul1r // pnatr_eq0.
have hsub : punctured_box box_lower (box_upper 2^-1) `<=` P.
  move=> y hy i; have /andP[h1 h2] := hy i; apply/andP; split=> //.
  rewrite /box_upper in h2 *; case: (i == ord0) in h2 *=> //.
  by case: (i == second_index k) in h2 *=> //; lra.
have hPfin := punctured_box_finite hm hr.
have hPm : measure_measurable xi (punctured_box box_lower (box_upper 2^-1)).
  by apply: (radon_open_measurable hr); exact: punctured_box_open.
have hdiff : xi (P `\` punctured_box box_lower (box_upper 2^-1)) = 0%E.
  have hs := hPm P.
  have hI : P `&` punctured_box box_lower (box_upper 2^-1) = punctured_box box_lower (box_upper 2^-1).
    by apply/seteqP; split=> y; [move=> []|move=> h; split=> //; exact: hsub].
  have hB : xi (punctured_box box_lower (box_upper 2^-1)) = xi P by rewrite -hdP hinv.
  rewrite hI hB in hs.
  have hf : xi P \is a fin_num by rewrite ge0_fin_numE ?(measure_nonnegative hm).
  have e1 : xi (P `\` punctured_box box_lower (box_upper 2^-1)) =
      (xi P + xi (P `\` punctured_box box_lower (box_upper 2^-1)) - xi P)%E.
    by rewrite [(xi P + _)%E]addeC addeK.
  by rewrite e1 -hs subee.
have hQ : xi Q = 0%E.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -hdiff.
  apply: (@measure_mono R X xi hm); move=> y hy; split.
  - move=> i; have /andP[h1 h2] := hy i; apply/andP; split=> //.
    rewrite /box_lower_half in h1; case: (eqVneq i (second_index k)) h1=> [->|hj] h1; last exact: h1.
    by rewrite /box_lower; have hi : second_index k != ord0 by []; rewrite (negbTE hi); lra.
  - move=> h; have /andP[h1 _] := hy (second_index k); have /andP[_ h2] := h (second_index k).
    move: h1 h2; rewrite /box_lower_half /box_upper eqxx /=; lra.
pose q : V := [ffun i => (box_lower_half i + box_upper 1 i) / 2].
have hq : q \in ~` [set (0 : E)].
  apply: mem_set=> /= h0; have := congr1 (fun z : V => z ord0) h0.
  rewrite /q ffunE /box_lower_half /box_lower /box_upper /= ffunE; lra.
pose q0 : X := exist _ q hq.
have hq0 : Q q0.
  move=> i; rewrite /= /q ffunE /box_lower_half /box_lower /box_upper.
  case: (eqVneq i (second_index k))=> [hj|hj].
  - have hi : second_index k != ord0 by [].
    by rewrite hj (negbTE hi); apply/andP; split; lra.
  - case: (i == ord0); by apply/andP; split; lra.
have hcover x : exists g, (punctured_action g @` Q) x.
  have [g hg] := general_linear_transitive q0 x.
  by exists g; exists q0.
pose gx (x : X) := sval (cid (hcover x)).
have hgx x : (punctured_action (gx x) @` Q) x := svalP (cid (hcover x)).
pose Qbox := [set x : E | forall i, box_lower_half i < x i < box_upper 1 i].
pose U (x : X) : set E := (sval (gx x) : E -> E) @` Qbox.
have hUo x : open (U x).
  have hg := svalP (gx x).
  have [h [hgh hhg]] := euclidean_linear_inverse ((euclidean_det_injective (sval (gx x))).1 hg).
  apply: (homeomorphism_with_inverse_open_map (euclidean_linear_homeomorphism hgh hhg)).
  exact: euclidean_open_box_open.
have hQbox0 w : Qbox w -> w \in ~` [set (0 : E)].
  move=> hw; apply: mem_set=> /= h0; have := hw ord0; rewrite h0 ffunE.
  by rewrite /box_lower_half /box_lower /box_upper eqxx /=; lra.
have hK (C : set X) : compact C -> xi C = 0%E.
  move=> hC.
  have hCE : compact (set_val @` C).
    apply: continuous_compact=> //; apply: continuous_subspaceT=> y.
    exact: set_type_val_continuous.
  move: hCE; rewrite compact_cover=> hCE.
  have hcov : set_val @` C `<=` \bigcup_(x in setT) U x.
    move=> e [y hy <-]; exists y=> //.
    have [z hz hzy] := hgx y; exists (set_val z)=> //.
    exact: (congr1 set_val hzy).
  have [D _ hD] := hCE X setT U (fun x _ => hUo x) hcov.
  have hCD : C `<=` \bigcup_(x in [set` D]) punctured_action (gx x) @` Q.
    move=> y hy; have [x hx [w hw hwy]] := hD (set_val y) (ex_intro2 _ _ y hy erefl).
    exists x=> //; exists (exist _ w (hQbox0 w hw))=> //.
    by apply: val_inj.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: le_trans (@measure_mono R X xi hm _ _ hCD) _.
  rewrite (measure_null_countable_union hm (D := [set` D])) //.
  by move=> x _; rewrite hinv.
have hT : xi setT = 0%E.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  by apply: (radon_inner_least hr openT)=> C hC _; rewrite hK.
move=> T; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -hT.
exact: (@measure_mono R X xi hm T setT (subsetT T)).
Qed.

End InvariantRadon.
