(** Federer (1969), 2.7.16, example (2), printed pp. 136–137: "In case U =
    V, phi is a left |det|^{-n} covariant measure over G. According to 2.7.9
    we can define a left Haar integral lambda of G by the formula lambda(u)
    = int u . |det|^{-n} dphi whenever u in K(G)" (the exponent -n as
    corrected by the erratum, p. 3, book p. 136 line 29; the book prints
    |det|^n). "We also know that phi is right Delta_G |det|^n covariant over
    G. On the other hand the linear isomorphism wedge^1: Hom(V, V) ~
    Hom(wedge^1 V, wedge^1 V) maps G onto the group G' of all linear
    automorphisms of wedge^1 V, and (wedge^1)_# phi is a Haar measure of the
    additive group of Hom(wedge^1 V, wedge^1 V), hence (wedge^1)_# phi is a
    left |det|^{-n} covariant measure over G'. For each g in G the diagram
    [right multiplication by g^{-1} on G, left multiplication by (wedge^1
    g)^{-1} on G'] is commutative, with |det(wedge^1 g)^{-1}|^{-n} = |det
    g|^n; therefore phi is right |det|^n covariant. We conclude that Delta_G
    = 1, G is unimodular." Here V has an inner product and a finite base, X
    = Hom(V, V) has the topology of HomSpaceTopology.v, G is the linear
    group of V with the sealed operations of LinearGroupSealed.v, a locally
    compact Hausdorff group, and phi is a Haar measure of the additive group
    of X with integral mu. Since G is open in X, every u in K(G) extended by
    0 to X belongs to K(X), and phi over G is represented by the integral
    nu(u) = mu(u') (OpenSubspaceExtension.v). The module proves that nu is a
    nonzero monotone Daniell integral on K(G) which is left |det|^{-n}
    covariant (linear_group_haar_left_covariant), that lambda(u) = nu(u .
    |det|^{-n}) is a left Haar integral of G
    (linear_group_left_haar_integral), that nu is right Delta_G |det|^n
    covariant (2.7.9(3); linear_group_haar_right_modular), that nu is right
    |det|^n covariant (linear_group_haar_right_covariant) and that Delta_G =
    1 (linear_group_modular_unit), so that G is unimodular in the sense of
    2.7.12, p. 129 (linear_group_unimodular). The right covariance is
    obtained from the covariance factor |det R|^{-1} of the linear
    automorphism R(f) = f o g^{-1} of X (FiniteHaarLinear.v) and det R =
    (det wedge^1 g^{-1})^n = (det g)^{-n} (HomCompositionDeterminant.v): R
    acts as (wedge^1 g)^{-1} on each of the n copies of wedge^1 V in X,
    which is the content of Federer's commutative diagram; the image measure
    (wedge^1)_# phi is not formed. The covariance over G is stated for the
    integral nu associated with phi over G; the identification of phi over G
    with the K(G) regular measure associated with nu is not formalised. The
    instance V = R^n is euclidean_linear_group_unimodular. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit ExtendedPositiveWeightLimit
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric
  InnerNormedTopology LinearBasis Hom HomInner FunctionLatticeUP DaniellIntegralUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum CompactSupportFunctionUP CompactSupportProducts
  CompactCutoffUP CompactCutoff CovariantIntegralUP HaarIntegralUP TopologicalGroupUP TopologicalGroupLaws
  HaarIntegralExistence InvariantIntegralPositivity ModularFunctionUP ModularFunction
  CovariantHaarCharacterisation UnimodularGroupUP UnimodularGroups SubtypeCompactHausdorff
  IsotropyGroupTopology HomSpaceTopology LinearGroupTopology LinearGroupSealed OpenSubspaceExtension
  EuclideanLinearMaps HomCompositionDeterminant HomHaarCovariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeightedIntegral.
Variable R : realType.
Variable Y : topologicalType.
Local Notation K := (@compactly_supported_continuous_functions R Y).
Variable nu : (Y -> R) -> R.
Hypothesis hnu : is_monotone_daniell_integral K nu.
Variable w : Y -> R.
Hypothesis hwc : continuous (w : Y -> real_line_metric R).
Hypothesis hwp : forall y, 0 < w y.

(** Source for [weighted_member]: u w belongs to K(Y) whenever u in
    K(Y), as presupposed by "lambda(u) = int u . |det|^{-n} dphi whenever
    u in K(G)", Federer 2.7.16, p. 136, and 2.7.9, p. 127. Supporting
    lemma. *)
Lemma weighted_member u : K u -> K (fun y => u y * w y).
Proof.
move=> hu; have -> : (fun y => u y * w y) = (fun y => w y * u y) by apply: funext=> y; exact: mulrC.
exact: compact_support_continuous_multiplier hwc hu.
Qed.

(** Source for [weighted_monotone_daniell]: u |-> nu(u w) is a monotone
    Daniell integral on K(Y) for a monotone Daniell integral nu and a
    positive continuous w, Federer 2.5.2, p. 92; supporting the left
    Haar integral lambda of 2.7.16, p. 136. Supporting lemma. *)
Lemma weighted_monotone_daniell : is_monotone_daniell_integral K (fun u => nu (fun y => u y * w y)).
Proof.
have [hadd hscale hmono hinc] := hnu.
split.
- move=> f g hf hg.
  rewrite -(hadd _ _ (weighted_member hf) (weighted_member hg)).
  by congr (nu _); apply: funext=> y; rewrite mulrDl.
- move=> c f hc hf; rewrite -(hscale c _ hc (weighted_member hf)).
  by congr (nu _); apply: funext=> y; rewrite mulrA.
- move=> f g hf hg hfg; apply: hmono; try exact: weighted_member.
  by move=> y; rewrite ler_wpM2r ?(ltW (hwp y)) //; exact: hfg.
- move=> f g hf hg hfg; apply: hinc; first by move=> k; exact: weighted_member.
    exact: weighted_member.
  move=> y; have := extended_positive_weight_increases (hwp y) (hfg y).
  have -> : (fun k => ((w y)%:E * (f k y)%:E)%E) = (fun k => (f k y * w y)%:E).
    by apply: funext=> k; rewrite -EFinM mulrC.
  by rewrite -EFinM mulrC.
Qed.

End WeightedIntegral.

Section Unimodular.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation hGc := (linear_group_operations_lch hB hb).
Local Notation KG := (@compactly_supported_continuous_functions R GL).
Local Notation KH := (@compactly_supported_continuous_functions R H).
Local Notation det := (linear_group_det hB hb).
(** Source for [hH]: X = Hom(V, V) is Hausdorff, Federer 2.7.16,
    p. 134. *)
Let hH : hausdorff_space H := @hom_space_hausdorff R V V B B hB hB n b hb.
(** Source for [hGo]: G is open in Hom(V, V), Federer 2.7.16, p. 134. *)
Let hGo : open (linear_group hB hb) := @linear_group_set_open R V B hB n b hb.
(** Source for [hGl]: the group laws of G, Federer 2.7.1, p. 121. *)
Let hGl := linear_group_group_laws hG.

(** Source for [linear_group_character]: chi(g) = |det g|^{-n}, the
    character of "phi is a left |det|^{-n} covariant measure over G",
    Federer 2.7.16, p. 136. Definition. *)
Definition linear_group_character (g : GL) : R := `|det g| ^- n.

Local Notation chi := linear_group_character.

(** Source for [linear_group_character_mul]: chi(g h) = chi(g) chi(h),
    Federer 1.3.4, p. 16, as required of chi in 2.7.9, p. 126.
    Supporting lemma. *)
Lemma linear_group_character_mul (g h : GL) : chi (mul g h) = chi g * chi h.
Proof. by rewrite /chi linear_group_det_mul normrM exprMn invfM. Qed.

(** Source for [linear_group_character_nonzero]: chi(g) <> 0, as
    required of chi in 2.7.9, p. 126. Supporting lemma. *)
Lemma linear_group_character_nonzero (g : GL) : chi g != 0.
Proof. by rewrite /chi invr_eq0 expf_neq0 // normr_eq0 linear_group_det_nonzero. Qed.

(** Source for [linear_group_character_positive]: chi(g) > 0,
    supporting "lambda(u) = int u . |det|^{-n} dphi", Federer 2.7.16,
    p. 136. Supporting lemma. *)
Lemma linear_group_character_positive (g : GL) : 0 < chi g.
Proof. by rewrite /chi invr_gt0 exprn_gt0 // normr_gt0 linear_group_det_nonzero. Qed.

(** Source for [linear_group_character_continuous]: chi is continuous,
    as required in 2.7.9, p. 126. Supporting lemma. *)
Lemma linear_group_character_continuous : continuous (chi : GL -> real_line_metric R).
Proof. exact: linear_group_det_power_continuous. Qed.

(** Source for [linear_group_character_inverse]: chi(g)^{-1} = |det g|^n,
    Federer 2.7.16, p. 136, "right Delta_G |det|^n covariant".
    Supporting lemma. *)
Lemma linear_group_character_inverse (g : GL) : (chi g)^-1 = `|det g| ^+ n.
Proof. by rewrite /chi invrK. Qed.

(** Source for [extension_left_multiplication]: (u o L_g)' = u' o A_g,
    where L_g is left multiplication by g on G and A_g(f) = g o f on
    Hom(V, V): g o f belongs to G if and only if f does; supporting
    "phi is a left |det|^{-n} covariant measure over G", Federer 2.7.16,
    p. 136. Supporting lemma. *)
Lemma extension_left_multiplication (u : GL -> R) (g : GL) :
  open_extension (u \o left_multiplication_action mul g) =
    open_extension u \o hom_linear_group_action hB hb hB hb g.
Proof.
apply: funext=> f /=; rewrite /hom_linear_group_action.
case: (pselect (linear_group hB hb f))=> hf.
- pose y : GL := exist _ f (mem_set hf).
  have hgf : linear_group hB hb (hom_comp (set_val g : Hom V V) f : H).
    exact: (linear_group_comp (set_valP g) hf).
  rewrite -[f]/(set_val y) open_extensionE /left_multiplication_action.
  have -> : (hom_comp (set_val g : Hom V V) (set_val y) : H) = set_val (mul g y).
    by rewrite (linear_group_mulE hG).
  by rewrite open_extensionE.
- rewrite !open_extension_out //.
  by move=> hgf; apply: hf=> x x' hx; apply: hgf; rewrite !hom_compE hx.
Qed.

(** Source for [extension_right_multiplication]: (u o R_g)' = u' o S,
    where R_g(x) = x g^{-1} on G and S(f) = f o g^{-1} on Hom(V, V):
    f o g^{-1} belongs to G if and only if f does; supporting "phi is
    right |det|^n covariant", Federer 2.7.16, p. 137. Supporting
    lemma. *)
Lemma extension_right_multiplication (u : GL -> R) (g : GL) :
  open_extension (u \o right_multiplication_action mul inv g) =
    open_extension u \o (fun f : H => (hom_comp (f : Hom V V) (set_val (inv g)) : H)).
Proof.
have [hgi hig] := linear_group_inv_cancel hG g.
apply: funext=> f /=.
case: (pselect (linear_group hB hb f))=> hf.
- pose y : GL := exist _ f (mem_set hf).
  rewrite -[f]/(set_val y) open_extensionE /right_multiplication_action.
  have -> : (hom_comp (set_val y : Hom V V) (set_val (inv g)) : H) = set_val (mul y (inv g)).
    by rewrite (linear_group_mulE hG).
  by rewrite open_extensionE.
- rewrite !open_extension_out //.
  move=> hfg; apply: hf=> x x' hx; apply: (can_inj hgi); apply: hfg.
  by rewrite !hom_compE !hgi.
Qed.

Section HaarIntegral.
Variable mu : (H -> R) -> R.
Hypothesis hmu : is_left_haar_integral (fun f g : H => f + g) mu.

(** Source for [linear_group_restricted]: nu(u) = int u' dphi for u in
    K(G), the integral over G of a Haar measure phi of the additive
    group of Hom(V, V), Federer 2.7.16, p. 136 ("phi ... over G").
    Definition. *)
Definition linear_group_restricted : (GL -> R) -> R := open_restricted_integral mu.

Local Notation nu := linear_group_restricted.

(** Source for [linear_group_restricted_monotone]: nu is a monotone
    Daniell integral on K(G), Federer 2.5.2, p. 92, supporting 2.7.16,
    p. 136. Supporting lemma. *)
Lemma linear_group_restricted_monotone : is_monotone_daniell_integral KG nu.
Proof. exact: (open_restricted_monotone hH hGo (nonzero_invariant_integral_monotone hmu)). Qed.

(** Source for [linear_group_restricted_daniell]: nu is a Daniell
    integral on K(G), Federer 2.5.2, p. 92. Supporting lemma. *)
Lemma linear_group_restricted_daniell : is_daniell_integral KG nu.
Proof. exact: monotone_daniell_integral_is_daniell linear_group_restricted_monotone. Qed.

(** Source for [linear_group_cutoff_positive]: for a cutoff function
    u0 in K(G)+ with u0(1_V) = 1 (2.5.13, p. 106) and a positive
    continuous w on G, nu(u0 w) > 0, because (u0 w)' in K(X)+ does not
    vanish at 1_V and Haar integrals are positive on K(X)+ ~ {0}
    (InvariantIntegralPositivity.v); supporting "phi is a ... measure
    over G" and "a left Haar integral lambda of G", Federer 2.7.16,
    p. 136. Supporting lemma. *)
Lemma linear_group_cutoff_positive (w : GL -> R) :
  continuous (w : GL -> real_line_metric R) -> (forall g, 0 < w g) ->
  exists2 u0, KG u0 & 0 < nu (fun x => u0 x * w x) /\ 0 < nu u0.
Proof.
move=> hwc hwp.
pose u0 := compact_cutoff R (lch_group_hausdorff hGc) (lch_group_locally_compact hGc) (@compact_set1 GL unit).
have hu := compact_cutoff_specification R (lch_group_hausdorff hGc) (lch_group_locally_compact hGc)
  (@compact_set1 GL unit).
have hu0 : KG u0 := compact_cutoff_function hu.
have hpos (v : GL -> R) : KG v -> (forall x, 0 <= v x) -> v unit <> 0 -> 0 < nu v.
  move=> hv hv0 hv1; apply: (left_haar_integral_positive (hom_additive_topological_group hB hB hb) hmu).
  - have hh := open_extension_compact hH hGo hv; exact hh.
  - move=> f; rewrite /open_extension; case: pselect=> // h; exact: hv0.
  - by exists (set_val unit); rewrite open_extensionE.
have hu1 : u0 unit = 1 by exact: compact_cutoff_on_set hu unit erefl.
have hur x : 0 <= u0 x by have /andP[] := compact_cutoff_range hu x.
exists u0=> //; split.
- apply: hpos; first exact: weighted_member.
  + by move=> x; rewrite mulr_ge0 // ltW.
  + by rewrite hu1 mul1r; apply/eqP; rewrite gt_eqF.
- by apply: hpos=> //; rewrite hu1; apply/eqP; exact: oner_neq0.
Qed.

(** Source for [linear_group_haar_left_covariant]: "In case U = V, phi
    is a left |det|^{-n} covariant measure over G", Federer 2.7.16,
    p. 136, for the integral nu of phi over G: nu(u o L_g) =
    |det g|^{-n} nu(u) whenever u in K(G), g in G, by the covariance of
    phi with respect to the action of G on Hom(V, V) (m = n).
    Direct formalisation for the associated integral. *)
Theorem linear_group_haar_left_covariant : is_left_covariant_integral mul chi nu.
Proof.
split; first exact: linear_group_restricted_daniell.
move=> u g hu; rewrite /nu /linear_group_restricted /open_restricted_integral.
rewrite extension_left_multiplication.
have h := covariant_integral_law (hom_haar_integral_covariant hB hb hB hb hmu) g
  (open_extension_compact hH hGo hu).
exact h.
Qed.

(** Source for [linear_group_haar_right_covariant]: "therefore phi is
    right |det|^n covariant", Federer 2.7.16, p. 137, for the integral
    nu of phi over G: nu(u o R_g) = |det g|^n nu(u), where
    R_g(x) = x g^{-1}; the factor is |det(f |-> f o g^{-1})|^{-1} =
    |det g^{-1}|^{-n} = |det g|^n. Direct formalisation; the proof
    computes the determinant of right multiplication instead of
    transporting phi by wedge^1. *)
Theorem linear_group_haar_right_covariant :
  is_right_covariant_integral mul inv (fun g => `|det g| ^+ n) nu.
Proof.
split; first exact: linear_group_restricted_daniell.
move=> u g hu; rewrite /nu /linear_group_restricted /open_restricted_integral.
rewrite extension_right_multiplication.
have hi : injective (set_val (inv g) : Hom V V) := set_valP (inv g).
rewrite (hom_haar_integral_right hB hb hB hb hmu hi (open_extension_compact hH hGo hu)).
congr (_ * _).
change (`|linear_group_det hB hb (inv g)| ^- n = `|det g| ^+ n).
by rewrite linear_group_det_inv normrV ?unitfE ?linear_group_det_nonzero // exprVn invrK.
Qed.

(** Source for [linear_group_haar_right_modular]: "We also know that
    phi is right Delta_G |det|^n covariant over G", Federer 2.7.16,
    p. 136, by 2.7.9(3), p. 127, from the left |det|^{-n} covariance,
    for any modular function Delta of G (2.7.8, p. 126). Direct
    formalisation for the integral nu. *)
Theorem linear_group_haar_right_modular (Delta : GL -> R) :
  is_modular_function mul inv Delta ->
  is_right_covariant_integral mul inv (fun g => Delta g * `|det g| ^+ n) nu.
Proof.
move=> hD.
have h := (left_covariant_modular_characterisation hGc linear_group_restricted_daniell
  linear_group_character_mul linear_group_character_nonzero linear_group_character_continuous hD).1
  linear_group_haar_left_covariant.
have -> : (fun g => Delta g * `|det g| ^+ n) = (fun g => Delta g * (chi g)^-1).
  by apply: funext=> g; rewrite linear_group_character_inverse.
exact: h.
Qed.

(** Source for [linear_group_left_haar_integral]: "According to 2.7.9
    we can define a left Haar integral lambda of G by the formula
    lambda(u) = int u . |det|^{-n} dphi whenever u in K(G)", Federer
    2.7.16, p. 136, with the exponent -n of the erratum, p. 3, book
    p. 136 line 29 (the book prints |det|^n): lambda(u) = nu(u chi) is
    the left invariant integral sigma of the proof of 2.7.9(1), p. 127,
    and it is monotone and nonzero. Direct formalisation; erratum
    correction. *)
Theorem linear_group_left_haar_integral :
  is_left_haar_integral mul (fun u => nu (fun x => u x * `|det x| ^- n)).
Proof.
split.
- exact: ((left_covariant_weight_invariant hGc linear_group_restricted_daniell
    linear_group_character_mul linear_group_character_nonzero linear_group_character_continuous).1
    linear_group_haar_left_covariant).
- exact: (weighted_monotone_daniell linear_group_restricted_monotone linear_group_character_continuous
    linear_group_character_positive).
- have [u0 hu0 [hpos _]] := linear_group_cutoff_positive linear_group_character_continuous
    linear_group_character_positive.
  by exists u0=> //; apply/eqP; rewrite gt_eqF.
Qed.

End HaarIntegral.

(** Source for [linear_group_modular_unit]: "We conclude that
    Delta_G = 1", Federer 2.7.16, p. 137: for any modular function
    Delta of G (2.7.8, p. 126), nu is right Delta |det|^n covariant and
    right |det|^n covariant, with nu(u0) <> 0 for a cutoff u0, so that
    Delta(g) |det g|^n = |det g|^n. A Haar integral of the additive group
    of Hom(V, V) exists by 2.7.5, p. 125. Direct formalisation. *)
Theorem linear_group_modular_unit (Delta : GL -> R) :
  is_modular_function mul inv Delta -> forall g, Delta g = 1.
Proof.
move=> hD g.
have [mu hmu] := left_haar_integral_exists R (hom_additive_lch_group hB hB hb hb).
have [u0 hu0 [_ hpos]] := linear_group_cutoff_positive hmu (@linear_group_character_continuous)
  linear_group_character_positive.
have h1 := covariant_integral_law (linear_group_haar_right_modular hmu hD) g hu0.
have h2 := covariant_integral_law (linear_group_haar_right_covariant hmu) g hu0.
rewrite h1 in h2.
have h3 := mulIf (lt0r_neq0 hpos) h2.
have hd : `|det g| ^+ n != 0 by rewrite expf_neq0 // normr_eq0 linear_group_det_nonzero.
by apply: (mulIf hd); rewrite mul1r.
Qed.

(** Source for [linear_group_unimodular]: "G is unimodular", Federer
    2.7.16, p. 137, in the sense of 2.7.12, p. 129: the left and right
    Haar integrals of the linear group of V coincide, since Delta_G = 1
    (2.7.12, "equivalent to the condition that the modular function
    Delta_G is constant with value 1"). Direct formalisation, for the
    sealed operations of LinearGroupSealed.v. *)
Theorem linear_group_unimodular : is_unimodular R mul inv.
Proof.
have [D hD] := modular_function_exists R hGc.
apply/(unimodular_iff_modular_unit hGc hD).
exact: linear_group_modular_unit hD.
Qed.

End Unimodular.

Arguments linear_group_character {R V B} hB {n b} hb g.
Arguments linear_group_restricted {R V B} hB {n b} hb mu u.

Section Euclidean.
Variable R : realType.
Variable n : nat.
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Local Notation GL := (set_type (linear_group hB hb)).

(** Source for [euclidean_linear_group_modular_unit]: Delta_G = 1 for
    G = GL(n, R), the linear group of R^n, Federer 2.7.16, p. 137; used
    in 2.7.16(3)–(5), pp. 137–138. Direct formalisation of the
    instance. *)
Corollary euclidean_linear_group_modular_unit (Delta : GL -> R) :
  is_modular_function (linear_group_mul hB hb) (linear_group_inv hB hb) Delta ->
  forall g, Delta g = 1.
Proof. exact: linear_group_modular_unit. Qed.

(** Source for [euclidean_linear_group_unimodular]: "G is unimodular"
    for G = GL(n, R), Federer 2.7.16, p. 137, in the sense of 2.7.12,
    p. 129. Direct formalisation of the instance. *)
Corollary euclidean_linear_group_unimodular :
  is_unimodular R (linear_group_mul hB hb) (linear_group_inv hB hb).
Proof. exact: linear_group_unimodular. Qed.

(** Source for [euclidean_linear_group_det]: for V = R^n with the
    standard base, the determinant of the linear group of
    HomHaarCovariance.v is general_linear_det of
    GeneralLinearPunctured.v, Federer 2.7.16, p. 135; both are det of
    1.3.4, p. 16, for the standard base. Supporting lemma. *)
Lemma euclidean_linear_group_det (g : GL) :
  linear_group_det hB hb g = euclidean_det (hom_as_linear (set_val g : Hom (R_n R n) (R_n R n))).
Proof. by []. Qed.

End Euclidean.

Arguments linear_group_unimodular {R V B} hB {n b} hb _.
Arguments linear_group_modular_unit {R V B} hB {n b} hb {Delta} _ g.
Arguments linear_group_haar_left_covariant {R V B} hB {n b} hb {mu} _.
Arguments linear_group_left_haar_integral {R V B} hB {n b} hb {mu} _.
Arguments linear_group_haar_right_modular {R V B} hB {n b} hb {mu} _ {Delta} _.
Arguments linear_group_haar_right_covariant {R V B} hB {n b} hb {mu} _.
Arguments euclidean_linear_group_unimodular : clear implicits.
Arguments euclidean_linear_group_modular_unit {R n Delta} _ g.
