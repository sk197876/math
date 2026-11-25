(** Federer (1969), 2.7.16, printed p. 134: "Then we see that composition of
    linear maps is a continuous operation because f o g - h o k = (f - h) o
    g + h o (g - k), ||f o g|| <= ||f|| . ||g|| whenever f, g, h, k in
    Hom(V, V). Moreover the automorphisms form a dense open subset of Hom(V,
    V), called the linear group of V, and inversion is a continuous
    operation because f^{-1} - g^{-1} = f^{-1} o (g - f) o g^{-1}, hence
    ||f^{-1}|| . (1 - ||g - f|| . ||g^{-1}||) <= ||g^{-1}||, whenever f, g
    are linear automorphisms of V", and "It should be clear from the
    preceding remarks that the topological assumptions of our general theory
    are satisfied". Here V is a vector space with an inner product and a
    finite basis, Hom(V, V) carries the topology of HomSpaceTopology.v, and
    the linear group of V is the set of univalent members of Hom(V, V),
    which are the automorphisms of V because V has finite dimension. The
    linear group is the type of its members with the relative topology
    (set_type, as for the isotropy groups of IsotropyGroupTopology.v). Its
    group structure is specified by the predicate is_linear_group_structure:
    the inclusion carries the multiplication to composition, the identity to
    1_V and the inversion to inverse maps. Such a structure exists and is
    unique; the operations used later are those of the sealed module
    LinearGroupOperations. With these operations the linear group is a
    locally compact Hausdorff topological group in the sense of 2.7.1, p.
    121: continuity of composition and inversion follows from the displayed
    estimates (LinearGroupEstimates.v), local compactness from the openness
    of the linear group in the locally compact space Hom(V, V). The density
    of the linear group is also proved. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module ring lra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology InnerBoundedness LinearBasis FiniteIndependence FiniteBasisComparison
  FiniteBasisCriterion FiniteDimension Annihilator FiniteDualDimension TensorUP Hom HomInner
  OperatorNormUP OperatorNorm LinearGroupEstimates SubtypeCompactHausdorff IsotropyGroupTopology
  TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomSpaceTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FiniteAutomorphisms.
Variable R : fieldType.
Variable V : lmodType R.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [finite_injective_surjective]: a univalent linear
    endomorphism of a finite dimensional space maps onto it, by the
    dimension count of Federer 1.1.2 and 1.3.2; hence the univalent
    members of Hom(V, V) are "the automorphisms" of 2.7.16, p. 134.
    Supporting lemma, generalising euclidean_injective_surjective. *)
Lemma finite_injective_surjective (f : {linear V -> V}) :
  injective f -> forall y, exists x, f x = y.
Proof.
move=> hi.
have hfe := finite_independent_map hi (finite_basis_independent hb).
pose U := finite_basis_vect hb.
have hb' : is_basis (fun i => f (b i)).
  apply: (@finite_independent_basis R U n (fun i => f (b i))) => //.
  by rewrite /U finite_basis_dimension card_ord.
move=> y; exists (\sum_i dual_basis hb' i y *: b i).
rewrite linear_sum; under eq_bigr do rewrite linearZ.
exact: esym (basis_vector_expansion hb' y).
Qed.

End FiniteAutomorphisms.

Section LinearGroup.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation onorm := (hom_operator_norm hB hB hb).

(** Source for [hom_identity]: the identity map 1_V as a member of
    Hom(V, V), Federer 2.7.16, p. 133 ("L(f) = 1_V"). Definition. *)
Definition hom_identity : Hom V V := hom_of_linear (linear_id V).

(** Source for [hom_identityE]: 1_V(x) = x, Federer 2.7.16, p. 133.
    Supporting lemma. *)
Lemma hom_identityE (x : V) : hom_identity x = x.
Proof. by []. Qed.

(** Source for [linear_group]: "the automorphisms form a dense open
    subset of Hom(V, V), called the linear group of V", Federer 2.7.16,
    p. 134: the univalent members of Hom(V, V), which are the
    automorphisms since dim V < oo (linear_group_inverse_exists).
    Definition. *)
Definition linear_group : set H := [set f | injective (f : Hom V V)].

Local Notation GL := (set_type linear_group).

(** Source for [linear_group_inverse_exists]: each member f of the
    linear group of Federer 2.7.16, p. 134, is an automorphism: there is
    g in Hom(V, V) with g o f = 1_V = f o g. Supporting lemma. *)
Lemma linear_group_inverse_exists (f : H) : linear_group f ->
  exists g : Hom V V, cancel (f : Hom V V) g /\ cancel g (f : Hom V V).
Proof.
move=> hf.
have hs := finite_injective_surjective hb (f := hom_as_linear f) hf.
exists (hom_of_linear (GRing.Linear.clone _ _ _ _ (linear_inverse hf hs) _)); split.
- exact: (linear_inverseKV hf hs).
- exact: (linear_inverseK hf hs).
Qed.

(** Source for [linear_group_comp]: composition preserves the linear
    group, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma linear_group_comp (f g : H) :
  linear_group f -> linear_group g -> linear_group (hom_comp (f : Hom V V) (g : Hom V V) : H).
Proof. by move=> hf hg x y; rewrite !hom_compE=> /hf /hg. Qed.

(** Source for [linear_group_identity]: 1_V belongs to the linear group,
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma linear_group_identity : linear_group (hom_identity : H).
Proof. by move=> x y. Qed.

(** Source for [hom_operator_norm_comp]: "||f o g|| <= ||f|| . ||g||",
    Federer 2.7.16, p. 134, for members of Hom(V, V); from
    operator_norm_composition. Supporting lemma. *)
Lemma hom_operator_norm_comp (f g : Hom V V) : onorm (hom_comp f g) <= onorm f * onorm g.
Proof.
have he : onorm (hom_comp f g) =
    linear_operator_norm hB hB hb (linear_comp (hom_as_linear f) (hom_as_linear g)).
  by apply: linear_operator_norm_ext.
by rewrite he; exact: operator_norm_composition.
Qed.

(** Source for [hom_operator_norm_difference]: the norm of g - f in
    Hom(V, V) is that of the map linear_difference_map g f of
    LinearGroupEstimates.v, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma hom_operator_norm_difference (f g : Hom V V) :
  onorm (g - f) = linear_operator_norm hB hB hb
    (linear_difference_map (hom_as_linear g) (hom_as_linear f)).
Proof. by apply: linear_operator_norm_ext. Qed.

(** Source for [linear_group_set_open]: "the automorphisms form a ...
    open subset of Hom(V, V)", Federer 2.7.16, p. 134: if g is an
    automorphism and ||f - g|| ||g^{-1}|| < 1, then f is univalent
    (linear_group_open). Direct formalisation. *)
Theorem linear_group_set_open : open linear_group.
Proof.
rewrite openE=> g hg; rewrite /interior.
have [g' [hgg' hg'g]] := linear_group_inverse_exists hg.
apply/hom_space_nbhs_operator.
have hc : 0 < onorm g' + 1.
  by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
exists (onorm g' + 1)^-1; first by rewrite invr_gt0.
move=> f hf; apply: (@linear_group_open R V B hB n b hb (hom_as_linear f) (hom_as_linear g)
  (hom_as_linear g') hgg').
rewrite -hom_operator_norm_difference hom_operator_norm_distC.
apply: (@le_lt_trans _ _ (onorm (f - g) * (onorm g' + 1))).
  by rewrite ler_wpM2l ?hom_operator_norm_nonnegative // lerDl.
by rewrite -ltr_pdivlMr // div1r.
Qed.

(** Source for [linear_group_set_dense]: "the automorphisms form a dense
    ... subset of Hom(V, V)", Federer 2.7.16, p. 134, in the sense that
    every nonempty open set meets the linear group (linear_group_dense).
    Direct formalisation. *)
Theorem linear_group_set_dense : dense linear_group.
Proof.
move=> O [f hf] hO.
have /hom_space_nbhs_operator [r hr hA] : nbhs (f : H) O.
  by apply: open_nbhs_nbhs; split.
have [f' [hi hlt]] := @linear_group_dense R V B hB n b hb (hom_as_linear f) r hr.
exists (hom_of_linear f' : H); split; last exact: hi.
apply: hA; rewrite hom_operator_norm_difference.
by rewrite (linear_operator_norm_ext hB hB hb (g := linear_difference_map f' (hom_as_linear f))).
Qed.

(** Source for [is_linear_group_structure]: the group structure of "the
    linear group of V", Federer 2.7.16, p. 134, whose multiplication is
    functional composition and whose identity is 1_V. Definition by the
    laws carried by the inclusion of the linear group into Hom(V, V):
    composition, the left inverse law and the identity. *)
Record is_linear_group_structure (mul : GL -> GL -> GL) (inv : GL -> GL) (e : GL) : Prop := {
  (** Source for [linear_group_mulE]: the multiplication of the linear
      group is functional composition, Federer 2.7.16, p. 134. *)
  linear_group_mulE : forall a c, set_val (mul a c) = hom_comp (set_val a : Hom V V) (set_val c);
  (** Source for [linear_group_invE]: g^{-1} o g = 1_V, Federer 2.7.16,
      p. 134. *)
  linear_group_invE : forall a, hom_comp (set_val (inv a) : Hom V V) (set_val a) = hom_identity;
  (** Source for [linear_group_unitE]: the identity of the linear group
      is 1_V, Federer 2.7.16, p. 134. *)
  linear_group_unitE : set_val e = hom_identity
}.

(** Source for [linear_group_structure_exists]: the operations of "the
    linear group of V", Federer 2.7.16, p. 134, exist. Existence proof
    for is_linear_group_structure; the inverse is chosen by
    linear_group_inverse_exists. *)
Theorem linear_group_structure_exists :
  exists (mul : GL -> GL -> GL) (inv : GL -> GL) (e : GL), is_linear_group_structure mul inv e.
Proof.
exists (fun a c => exist _ (hom_comp (set_val a : Hom V V) (set_val c) : H)
  (mem_set (linear_group_comp (set_valP a) (set_valP c)))).
have hinv (a : GL) : exists2 g : H, linear_group g & hom_comp (g : Hom V V) (set_val a) = hom_identity.
  have [g [hag hga]] := linear_group_inverse_exists (set_valP a).
  exists (g : H); last by apply: hom_ext=> x; rewrite hom_compE hag.
  by move=> x y hxy; rewrite -(hga x) -(hga y) hxy.
pose inv (a : GL) : GL := let w := cid2 (hinv a) in exist _ (s2val w) (mem_set (s2valP w)).
exists inv, (exist _ (hom_identity : H) (mem_set linear_group_identity)).
split=> // a; rewrite /inv /=.
by case: (cid2 (hinv a))=> g /= _ ->.
Qed.

Section Laws.
Variables (mul : GL -> GL -> GL) (inv : GL -> GL) (e : GL).
Hypothesis hG : is_linear_group_structure mul inv e.

(** Source for [linear_group_invE_right]: g o g^{-1} = 1_V, Federer
    2.7.16, p. 134: g is univalent and g(g^{-1}(g(x))) = g(x).
    Supporting lemma. *)
Lemma linear_group_invE_right a : hom_comp (set_val a : Hom V V) (set_val (inv a)) = hom_identity.
Proof.
have [g [hag hga]] := linear_group_inverse_exists (set_valP a).
have hl x : (set_val (inv a) : Hom V V) ((set_val a : Hom V V) x) = x.
  by have := congr1 (fun h : Hom V V => h x) (linear_group_invE hG a); rewrite hom_compE.
apply: hom_ext=> x; rewrite hom_compE hom_identityE.
by rewrite -{1}(hga x) hl hga.
Qed.

(** Source for [linear_group_inv_cancel]: g^{-1}(g(x)) = x and
    g(g^{-1}(x)) = x, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma linear_group_inv_cancel a :
  cancel (set_val a : Hom V V) (set_val (inv a) : Hom V V) /\
  cancel (set_val (inv a) : Hom V V) (set_val a : Hom V V).
Proof.
split=> x.
- by have := congr1 (fun h : Hom V V => h x) (linear_group_invE hG a); rewrite hom_compE.
- by have := congr1 (fun h : Hom V V => h x) (linear_group_invE_right a); rewrite hom_compE.
Qed.

(** Source for [linear_group_group_laws]: the group laws of the linear
    group of V, Federer 2.7.16, p. 134, as required in 2.7.1, p. 121.
    Supporting lemma. *)
Lemma linear_group_group_laws : is_group_laws mul inv e.
Proof.
have [hm hi hu] := hG.
split.
- move=> a c d; apply: val_inj; rewrite /= -!set_valE !hm.
  by apply: hom_ext=> x; rewrite !hom_compE.
- move=> a; apply: val_inj; rewrite /= -!set_valE hm hu.
  by apply: hom_ext=> x; rewrite hom_compE hom_identityE.
- by move=> a; apply: val_inj; rewrite /= -!set_valE hm hi hu.
Qed.

(** Source for [hom_composition_continuous]: "composition of linear maps
    is a continuous operation because f o g - h o k = (f - h) o g +
    h o (g - k), ||f o g|| <= ||f|| . ||g||", Federer 2.7.16, p. 134:
    composition is continuous on Hom(V, V) x Hom(V, V). Direct
    formalisation. *)
Theorem hom_composition_continuous :
  continuous (fun p : H * H => (hom_comp (p.1 : Hom V V) (p.2 : Hom V V) : H)).
Proof.
move=> [f g] A /hom_space_nbhs_operator [r hr hA].
pose c := onorm f + onorm g + 1.
have hc : 0 < c.
  by apply: ltr_wpDl; [rewrite addr_ge0 ?hom_operator_norm_nonnegative|exact: ltr01].
pose d := Num.min 1 (r / c).
have hd : 0 < d by rewrite /d lt_min ltr01 divr_gt0.
have hd1 : d <= 1 by rewrite /d ge_min lexx.
have hdc : d * c <= r by rewrite -ler_pdivlMr // /d ge_min lexx orbT.
exists ([set h : H | onorm (h - f) < d], [set k : H | onorm (k - g) < d]).
  by split; exact: hom_space_operator_ball_nbhs.
move=> [h k] [/= hh hk]; apply: hA.
have he : (hom_comp (h : Hom V V) k : H) - hom_comp (f : Hom V V) g =
    hom_comp (h - f : H) k + hom_comp (f : Hom V V) (k - g : H).
  apply: hom_ext=> x; rewrite hom_addE !hom_compE.
  have -> : ((hom_comp (h : Hom V V) k : H) - hom_comp (f : Hom V V) g : Hom V V) x =
    h (k x) - f (g x) by [].
  have -> : ((h - f : H) : Hom V V) (k x) = h (k x) - f (k x) by [].
  have -> : ((k - g : H) : Hom V V) x = k x - g x by [].
  rewrite (linearB (hom_as_linear f)) /=.
  by rewrite addrA subrK.
rewrite he; apply: le_lt_trans (hom_operator_norm_add hB hB hb _ _) _.
have hkn : onorm k <= onorm g + 1.
  apply: le_trans (hom_operator_norm_sub_bound hB hB hb g k) _; rewrite lerD2l.
  exact: le_trans (ltW hk) hd1.
apply: (@lt_le_trans _ _ (d * c)); last exact: hdc.
apply: (@le_lt_trans _ _ (onorm (h - f) * (onorm g + 1) + onorm f * onorm (k - g))).
  apply: lerD; first apply: le_trans (hom_operator_norm_comp _ _) _.
    by rewrite ler_wpM2l ?hom_operator_norm_nonnegative.
  exact: hom_operator_norm_comp.
rewrite (_ : d * c = d * (onorm g + 1) + d * onorm f); last by rewrite /c; ring.
have hg1 : 0 < onorm g + 1.
  by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
apply: ltr_leD; first by rewrite ltr_pM2r.
by rewrite mulrC ler_wpM2r ?hom_operator_norm_nonnegative // ltW.
Qed.

(** Source for [linear_group_mul_continuous]: composition is continuous
    on the linear group of V, Federer 2.7.16, p. 134, with the relative
    topology. Supporting lemma. *)
Lemma linear_group_mul_continuous : continuous (fun p : GL * GL => mul p.1 p.2).
Proof.
apply: set_type_continuous_into.
have -> : set_val \o (fun p : GL * GL => mul p.1 p.2) =
    (fun q : H * H => (hom_comp (q.1 : Hom V V) (q.2 : Hom V V) : H)) \o
      (fun p : GL * GL => (set_val p.1, set_val p.2)).
  by apply: funext=> p; rewrite /= (linear_group_mulE hG).
have hv := @set_type_val_continuous H linear_group.
have hp : continuous (fun p : GL * GL => (set_val p.1, set_val p.2)).
  apply: (@topological_pair_continuous (GL * GL)%type H H).
  - move=> q; exact: continuous_comp (@first_projection_continuous GL GL q) (hv q.1).
  - move=> q; exact: continuous_comp (@second_projection_continuous GL GL q) (hv q.2).
by move=> p; apply: continuous_comp; [exact: hp|exact: hom_composition_continuous].
Qed.

(** Source for [linear_group_inv_continuous]: "inversion is a
    continuous operation because f^{-1} - g^{-1} = f^{-1} o (g - f) o
    g^{-1}, hence ||f^{-1}|| . (1 - ||g - f|| . ||g^{-1}||) <= ||g^{-1}||",
    Federer 2.7.16, p. 134: if ||g - f|| ||g^{-1}|| <= 1/2, then
    ||f^{-1}|| <= 2 ||g^{-1}|| and ||f^{-1} - g^{-1}|| <=
    2 ||g^{-1}||^2 ||g - f||. Direct formalisation. *)
Theorem linear_group_inv_continuous : continuous inv.
Proof.
apply: set_type_continuous_into=> a A /hom_space_nbhs_operator [r hr hA].
pose g := (set_val a : Hom V V); pose g' := (set_val (inv a) : Hom V V).
pose c := onorm g' + 1.
have hc : 0 < c.
  by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
pose d := Num.min (c * 2)^-1 (r / (c * c * 2)).
have hc2 : 0 < c * 2 by rewrite mulr_gt0 ?ltr0n.
have hcc2 : 0 < c * c * 2 by rewrite !mulr_gt0 ?ltr0n.
have hd : 0 < d by rewrite /d lt_min invr_gt0 hc2 divr_gt0.
have hdc : d * c <= 2^-1.
  rewrite -ler_pdivlMr // /d ge_min; apply/orP; left.
  by rewrite invfM mulrC.
have hdr : d * (c * c * 2) <= r by rewrite -ler_pdivlMr // /d ge_min lexx orbT.
have hN : nbhs a (set_val @^-1` [set f : H | onorm (f - set_val a) < d]).
  exact: (@set_type_val_continuous H linear_group a _ (hom_space_operator_ball_nbhs _ hd)).
apply: filterS hN=> q /= hq; apply: hA.
pose f := (set_val q : Hom V V); pose f' := (set_val (inv q) : Hom V V).
have [hff' hf'f] := linear_group_inv_cancel q.
have [hgg' hg'g] := linear_group_inv_cancel a.
have hgf : onorm (g - f) < d by rewrite /g /f hom_operator_norm_distC.
have hgf' : onorm (g - f) * onorm g' <= 2^-1.
  apply: le_trans hdc; apply: ler_pM; rewrite ?hom_operator_norm_nonnegative //.
    exact: ltW.
  by rewrite /c lerDl ler01.
have hest := @operator_norm_inverse_estimate R V B hB n b hb (hom_as_linear f) (hom_as_linear g)
  (hom_as_linear f') (hom_as_linear g') hff' hg'g.
rewrite -hom_operator_norm_difference in hest.
have hf'n : onorm f' <= c * 2.
  have h12 : 2^-1 <= 1 - onorm (g - f) * onorm g'.
    by move: hgf'; lra.
  have h2 : (0 : R) < 2^-1 by rewrite invr_gt0 ltr0n.
  have : onorm f' * 2^-1 <= onorm g'.
    apply: le_trans hest; apply: ler_wpM2l; first exact: hom_operator_norm_nonnegative.
    exact: h12.
  rewrite -ler_pdivlMr // invrK => h; apply: le_trans h _.
  by rewrite ler_wpM2r ?ler0n // /c lerDl ler01.
have hdiff := @operator_norm_inverse_difference R V B hB n b hb (hom_as_linear f) (hom_as_linear g)
  (hom_as_linear f') (hom_as_linear g') hff' hg'g.
rewrite -!hom_operator_norm_difference in hdiff.
apply: le_lt_trans hdiff _.
apply: (@le_lt_trans _ _ (c * 2 * onorm (g - f) * c)).
  apply: ler_pM; rewrite ?mulr_ge0 ?hom_operator_norm_nonnegative //.
    by apply: ler_pM; rewrite ?hom_operator_norm_nonnegative.
  by rewrite /c lerDl ler01.
apply: lt_le_trans hdr.
rewrite (_ : c * 2 * onorm (g - f) * c = onorm (g - f) * (c * c * 2)); last by ring.
by rewrite ltr_pM2r.
Qed.

(** Source for [linear_group_locally_compact]: the linear group of V is
    locally compact, Federer 2.7.16, p. 134: it is open in the locally
    compact Hausdorff space Hom(V, V), so each point has a closed ball
    {g : |g - f| <= r} of Hom(V, V) inside the linear group, which is a
    compact neighbourhood in the relative topology. Supporting
    theorem. *)
Theorem linear_group_locally_compact : locally_compact [set: GL].
Proof.
move=> a _; rewrite withinET.
have /nbhs_ballP [r hr hsub] : nbhs (set_val a : H) linear_group.
  by apply: open_nbhs_nbhs; split; [exact: linear_group_set_open|exact: set_valP].
pose C : set H := [set g : H | `|g - set_val a| <= r / 2].
have hCsub : C `<=` linear_group.
  move=> g hg; apply: hsub; rewrite -ball_normE /= distrC.
  apply: le_lt_trans hg _; by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have hCc : compact C by exact: (hom_space_closed_ball_compact hb).
have hCcl : closed C.
  have he : C = closed_ball_ Num.norm (set_val a : H) (r / 2).
    by rewrite /C; apply/seteqP; split=> g /=; rewrite /closed_ball_ distrC.
  rewrite he; exact: closed_closed_ball_.
exists (set_val @^-1` C : set GL); last split.
- apply: (@set_type_val_continuous H linear_group a).
  apply: (@filterS _ _ _ (ball (set_val a : H) (r / 2))); last by apply: nbhsx_ballx; rewrite divr_gt0.
  by move=> g; rewrite -ball_normE /= distrC=> h; exact: ltW.
- exact: set_type_compact_preimage.
- by apply: preimage_closed hCcl=> c _; exact: set_type_val_continuous.
Qed.

(** Source for [linear_group_lch_group]: "the topological assumptions of
    our general theory are satisfied", Federer 2.7.16, p. 134, for the
    linear group of V: with functional composition, inversion and 1_V
    it is a locally compact Hausdorff topological group in the sense of
    2.7.1, p. 121. Direct formalisation. *)
Theorem linear_group_lch_group : is_locally_compact_hausdorff_group mul inv e.
Proof.
split.
- split; [exact: linear_group_group_laws|exact: linear_group_mul_continuous|
    exact: linear_group_inv_continuous].
- apply: set_type_hausdorff; exact: hom_space_hausdorff.
- exact: linear_group_locally_compact.
Qed.

End Laws.

(** Source for [linear_group_structure_unique]: the operations of "the
    linear group of V", Federer 2.7.16, p. 134, are unique. Supporting
    lemma. *)
Lemma linear_group_structure_unique mul inv e mul' inv' e' :
  is_linear_group_structure mul inv e -> is_linear_group_structure mul' inv' e' ->
  [/\ mul = mul', inv = inv' & e = e'].
Proof.
move=> h h'.
have hgl := linear_group_group_laws h; have hgl' := linear_group_group_laws h'.
have he : e = e' by apply: val_inj; rewrite /= -!set_valE (linear_group_unitE h) (linear_group_unitE h').
have hm : mul = mul'.
  apply: funext=> a; apply: funext=> c; apply: val_inj.
  by rewrite /= -!set_valE (linear_group_mulE h) (linear_group_mulE h').
split=> //; apply: funext=> a.
apply: (@group_mul_left_cancel _ mul' inv' e' hgl' a).
rewrite (group_mulgV hgl') -hm.
apply: val_inj; rewrite /= -!set_valE (linear_group_mulE h) (linear_group_unitE h').
exact: (linear_group_invE_right h a).
Qed.

End LinearGroup.

Arguments linear_group {R V B} hB {n b} hb.
Arguments hom_identity {R} V.
