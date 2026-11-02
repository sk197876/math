(** Federer (1969), 2.7.16, printed pp. 133–134: "If dim V < oo, then dim
    A(V, V) < oo and all norms on A(V, V) induce the same locally compact
    topology. In particular we can choose an inner product on V and norm
    Hom(V, V) as in 1.7.6. ... Using the maps L, M, tau we infer that
    functional composition is a continuous operation in A(V, V), and that
    inversion is continuous on the affine group of V, the open dense subset
    of univalent maps in A(V, V), which equals L^{-1}(linear group of V)."
    Here V carries an inner product and a finite basis, A(V, V) is any space
    (A, ev) satisfying is_affine_map_space of AffineMapSpaceUP.v, and N is
    any norm on A in the sense of 1.10.5, p. 48, with the topology of its
    metric (real_norm_metric_space, 2.2.7, p. 64). Hom(V, V) carries the
    topology of HomSpaceTopology.v and Hom(V, V) x V the product topology.
    Federer's sketch is completed as follows. The function N'(f) = |L(f)| +
    |f(0)| is a norm on A, and N is equivalent to N' by
    FiniteNormEquivalence.v; hence M and M^{-1} are Lipschitz in each factor
    and M is a homeomorphism of A onto Hom(V, V) x V
    (affine_space_iso_homeomorphism): the topology of every norm is the
    topology transported by M. Composition is continuous because M(f o g) =
    (L(f) o L(g), f(0) + L(f)(g(0))), by the continuity of composition and
    evaluation on Hom(V, V) (LinearGroupTopology.v, HomSpaceTopology.v). The
    univalent members form the set L^{-1}(linear group of V) (AffineMaps.v),
    which is open by the continuity of L and dense because g |-> M^{-1}(g,
    f(0)) is continuous and the linear group is dense. Restricted to this
    set, M is a homeomorphism onto the product of the linear group and V,
    the representation of the affine group in AffineGroupTopology.v; so the
    relative topology of the affine group in A(V, V) is the topology used
    there, inversion is continuous, and the affine group is a locally
    compact Hausdorff topological group in the sense of 2.7.1, p. 121.
    Composition and inversion are specified by their values
    (is_affine_composition, is_affine_inversion, is_affine_group_structure),
    and every statement holds for every operation with the specification. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity NormMetricScaleContinuity
  InnerProductUP InnerNorm InnerNormInequalities InnerMetric InnerNormedTopology LinearBasis TensorUP
  Hom HomInner
  HomSpaceTopology LinearGroupTopology TopologicalProductMaps IsotropyGroupTopology
  TopologicalGroupUP HomeomorphismUP AffineMaps AffineGroupTopology AffineMapSpaceUP
  HilbertFormCompactness FiniteNormEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FactorMaps.
Variables X Y Z : topologicalType.

(** Source for [first_factor_continuous]: (x, y) |-> f(x) is continuous
    for continuous f, supporting the continuity of composition in
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma first_factor_continuous (f : X -> Z) : continuous f -> continuous (fun p : X * Y => f p.1).
Proof.
move=> hf p; apply: (@continuous_comp (X * Y)%type X Z fst f p).
  exact: first_projection_continuous.
exact: hf.
Qed.

(** Source for [second_factor_continuous]: (x, y) |-> f(y) is
    continuous for continuous f, supporting the continuity of
    composition in Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma second_factor_continuous (f : Y -> Z) : continuous f -> continuous (fun p : X * Y => f p.2).
Proof.
move=> hf p; apply: (@continuous_comp (X * Y)%type Y Z snd f p).
  exact: second_projection_continuous.
exact: hf.
Qed.

End FactorMaps.

Section Transport.
Variables G G' : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Variables (mul' : G' -> G' -> G') (inv' : G' -> G') (e' : G').
Variables (phi : G -> G') (psi : G' -> G).
Hypothesis hphi : is_homeomorphism_with_inverse phi psi.
Hypothesis hmul : forall p q, phi (mul p q) = mul' (phi p) (phi q).
Hypothesis hinv : forall p, phi (inv p) = inv' (phi p).
Hypothesis hunit : phi e = e'.

(** Source for [lch_group_transport]: a homeomorphism phi which carries
    multiplication, inversion and identity of G to those of G' carries
    the structure of a locally compact Hausdorff topological group of
    2.7.1, p. 121, to G'; supporting "inversion is continuous on the
    affine group of V", Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma lch_group_transport :
  is_locally_compact_hausdorff_group mul inv e -> is_locally_compact_hausdorff_group mul' inv' e'.
Proof.
have [hc hci hpp hpp'] := hphi.
have hmul' a c : mul' a c = phi (mul (psi a) (psi c)) by rewrite hmul !hpp'.
have hinv' a : inv' a = phi (inv (psi a)) by rewrite hinv hpp'.
case=> [[[hA h1 hV] hm hi] hH hL].
split; first split; first split.
- by move=> a c d; rewrite !hmul' !hpp hA.
- by move=> a; rewrite hmul' -hunit hpp h1 hpp'.
- by move=> a; rewrite hmul' hinv' hpp hV hunit.
- have -> : (fun p : G' * G' => mul' p.1 p.2) =
      phi \o ((fun q : G * G => mul q.1 q.2) \o (fun p : G' * G' => (psi p.1, psi p.2))).
    by apply: funext=> p; rewrite /= hmul'.
  have hpair : continuous (fun p : G' * G' => (psi p.1, psi p.2)).
    apply: topological_pair_continuous=> q.
    + exact: continuous_comp (@first_projection_continuous G' G' q) (hci _).
    + exact: continuous_comp (@second_projection_continuous G' G' q) (hci _).
  move=> p; apply: (continuous_comp _ (hc _)).
  exact: (continuous_comp (hpair p) (hm _)).
- have -> : inv' = phi \o (inv \o psi) by apply: funext=> a; rewrite /= hinv'.
  move=> a; apply: (continuous_comp _ (hc _)).
  exact: continuous_comp (hci a) (hi _).
- move=> a c hcl; rewrite -(hpp' a) -(hpp' c); congr phi; apply: hH=> A C hA' hC'.
  have [y [hyA hyC]] := hcl _ _ (hci a A hA') (hci c C hC').
  by exists (psi y).
- move=> a _; have [K hK [hKc hKcl]] := hL (psi a) I; rewrite withinET in hK.
  exists (psi @^-1` K); first by rewrite withinET; exact: hci a K hK.
  split.
  + rewrite -(homeomorphism_with_inverse_image K hphi).
    by apply: continuous_compact hKc; apply: continuous_subspaceT.
  + by apply: preimage_closed hKcl=> y _; exact: hci y.
Qed.

End Transport.

Section AffineSpaceTopology.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable A : lmodType R.
Variable ev : A -> V -> V.
Hypothesis hA : is_affine_map_space ev.
Variable N : A -> R.
Hypothesis hN : is_real_norm N.
Local Notation MA := (real_norm_metric_space hN).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation L := (affine_space_hom hA).
Local Notation M := (affine_space_iso hA).
Local Notation Minv := (affine_space_iso_inv hA).
Local Notation hnorm := (inner_norm (hom_inner_productP hB hB hb)).

(** Source for [affine_space_homD]: L(f + g) = L(f) + L(g), "the linear
    epimorphism L", Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_homD (f g : A) : L (f + g) = L f + L g.
Proof.
apply: hom_ext=> v; rewrite hom_addE !affine_space_homE !(affine_space_evalD hA).
by rewrite opprD addrACA.
Qed.

(** Source for [affine_space_homZ]: L(c f) = c L(f), Federer 2.7.16,
    p. 133. Supporting lemma. *)
Lemma affine_space_homZ (c : R) (f : A) : L (c *: f) = c *: L f.
Proof. by apply: hom_ext=> v; rewrite hom_scaleE !affine_space_homE !(affine_space_evalZ hA) scalerBr. Qed.

(** Source for [affine_space_homB]: L(f - g) = L(f) - L(g), Federer
    2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_homB (f g : A) : L (f - g) = L f - L g.
Proof. by rewrite affine_space_homD -scaleN1r affine_space_homZ scaleN1r. Qed.

(** Source for [affine_space_hom0]: L(0) = 0, Federer 2.7.16, p. 133.
    Supporting lemma. *)
Lemma affine_space_hom0 : L 0 = 0.
Proof. by apply: hom_ext=> v; rewrite hom_zeroE affine_space_homE !(affine_space_eval0 hA) subrr. Qed.

(** Source for [affine_space_iso_invB]: M^{-1} preserves differences,
    Federer 2.7.16, p. 133, "the linear isomorphism M". Supporting
    lemma. *)
Lemma affine_space_iso_invB (p q : (Hom V V * V)%type) : Minv p - Minv q = Minv (p - q).
Proof.
have h := affine_space_iso_inv_linear hA (-1) q p; rewrite !scaleN1r in h.
by rewrite addrC -h addrC.
Qed.

(** Source for [affine_space_reference_norm]: the norm
    N'(f) = |L(f)| + |f(0)| of A(V, V), with |L(f)| the norm of 1.7.9,
    p. 35, and |f(0)| the norm of V; supporting "all norms on A(V, V)
    induce the same locally compact topology", Federer 2.7.16, p. 134.
    Definition. *)
Definition affine_space_reference_norm (f : A) : R := hnorm (L f) + inner_norm hB (ev f 0).

Local Notation N' := affine_space_reference_norm.

(** Source for [affine_space_reference_normP]: N' is a norm in the sense
    of 1.10.5, p. 48, since M is a linear isomorphism, Federer 2.7.16,
    pp. 133–134. Supporting lemma. *)
Lemma affine_space_reference_normP : is_real_norm N'.
Proof.
split; first split.
- by move=> f; rewrite addr_ge0 ?inner_norm_nonnegative.
- move=> c f; rewrite /N' affine_space_homZ (affine_space_evalZ hA).
  by rewrite (inner_normZ (hom_inner_productP hB hB hb)) (inner_normZ hB) mulrDr.
- move=> f g; rewrite /N' affine_space_homD (affine_space_evalD hA) addrACA.
  by apply: lerD; [exact: (inner_norm_triangle (hom_inner_productP hB hB hb))|exact: inner_norm_triangle].
- move=> f /eqP; rewrite /N' paddr_eq0 ?inner_norm_nonnegative // => /andP [/eqP h1 /eqP h2].
  have hL0 : L f = 0.
    by apply/eqP; rewrite -(inner_norm_eq0 (hom_inner_productP hB hB hb)) h1.
  have hz : ev f 0 = 0 by apply/eqP; rewrite -(inner_norm_eq0 hB) h2.
  rewrite -(affine_space_isoK hA f) -[RHS](affine_space_isoK hA 0).
  by rewrite /affine_space_iso hL0 hz affine_space_hom0 (affine_space_eval0 hA).
Qed.

(** Source for [affine_space_finite_basis]: "dim A(V, V) < oo", Federer
    2.7.16, p. 134: the base of AffineMapSpaceUP.v. Supporting lemma. *)
Lemma affine_space_finite_basis : is_basis (affine_space_basis hA hb b).
Proof. exact: (@affine_space_basisP R V V A ev hA n n b hb b hb). Qed.

(** Source for [affine_space_reference_upper]: N' <= C N for some
    C > 0, by the equivalence of norms on A(V, V), Federer 2.7.16,
    p. 134. Supporting lemma. *)
Lemma affine_space_reference_upper : exists2 C : R, 0 < C & forall f, N' f <= C * N f.
Proof.
exact: (@finite_norm_comparison R A N N' hN affine_space_reference_normP _ _ affine_space_finite_basis).
Qed.

(** Source for [affine_space_reference_lower]: N <= D N' for some
    D > 0, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_space_reference_lower : exists2 D : R, 0 < D & forall f, N f <= D * N' f.
Proof.
exact: (@finite_norm_comparison R A N' N affine_space_reference_normP hN _ _ affine_space_finite_basis).
Qed.

(** Source for [affine_space_hom_continuous]: L: A(V, V) -> Hom(V, V) is
    continuous for the topology of N, Federer 2.7.16, p. 134, "Using the
    maps L, M, tau". Supporting lemma. *)
Lemma affine_space_hom_continuous : continuous (fun f : MA => (L f : H)).
Proof.
have [C hC hu] := affine_space_reference_upper.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of MA] [the metricType R of H] _ C (ltW hC)).
move=> f g; rewrite inner_metric_distanceE real_norm_metric_distanceE.
have -> : ((L f : H) - (L g : H) : H) = L (f - g) by rewrite affine_space_homB.
by apply: le_trans (hu (f - g)); rewrite /N' lerDl inner_norm_nonnegative.
Qed.

(** Source for [affine_space_value_continuous]: f |-> f(0) is
    continuous for the topology of N, Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma affine_space_value_continuous : continuous (fun f : MA => (ev f 0 : VT)).
Proof.
have [C hC hu] := affine_space_reference_upper.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of MA] [the metricType R of VT] _ C (ltW hC)).
move=> f g; rewrite inner_metric_distanceE real_norm_metric_distanceE.
have -> : ((ev f 0 : VT) - (ev g 0 : VT) : VT) = ev (f - g) 0 by rewrite (affine_space_evalB hA).
by apply: le_trans (hu (f - g)); rewrite /N' lerDr inner_norm_nonnegative.
Qed.

(** Source for [affine_space_iso_continuous]: M is continuous from
    A(V, V) with the topology of N into Hom(V, V) x V, Federer 2.7.16,
    p. 134. Supporting lemma. *)
Lemma affine_space_iso_continuous : continuous (fun f : MA => (M f : H * VT)).
Proof.
exact: (@topological_pair_continuous MA H VT _ _ affine_space_hom_continuous affine_space_value_continuous).
Qed.

(** Source for [affine_space_iso_inv_first_continuous]: g |-> M^{-1}(g, 0)
    is continuous from Hom(V, V) into A(V, V) with the topology of N,
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_space_iso_inv_first_continuous : continuous (fun g : H => (Minv ((g : Hom V V), 0) : MA)).
Proof.
have [D hD hl] := affine_space_reference_lower.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of H] [the metricType R of MA] _ D (ltW hD)).
move=> g h; rewrite inner_metric_distanceE real_norm_metric_distanceE.
rewrite affine_space_iso_invB.
have -> : (((g : Hom V V), (0 : V)) - ((h : Hom V V), (0 : V)) : (Hom V V * V)%type) =
    (((g - h : H) : Hom V V), 0).
  by apply: injective_projections; [by []|exact: subrr].
apply: le_trans (hl _) _; rewrite /N' affine_space_hom_onto (affine_space_iso_inv_zero hA).
by rewrite inner_norm0 addr0.
Qed.

(** Source for [affine_space_iso_inv_second_continuous]: z |-> M^{-1}(0, z)
    is continuous from V into A(V, V) with the topology of N, Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma affine_space_iso_inv_second_continuous : continuous (fun z : VT => (Minv (0, (z : V)) : MA)).
Proof.
have [D hD hl] := affine_space_reference_lower.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of VT] [the metricType R of MA] _ D (ltW hD)).
move=> y z; rewrite inner_metric_distanceE real_norm_metric_distanceE.
rewrite affine_space_iso_invB.
have -> : (((0 : Hom V V), (y : V)) - ((0 : Hom V V), (z : V)) : (Hom V V * V)%type) =
    (0, ((y - z : VT) : V)).
  by apply: injective_projections; [exact: subrr|by []].
apply: le_trans (hl _) _; rewrite /N' affine_space_hom_onto (affine_space_iso_inv_zero hA).
by rewrite inner_norm0 add0r.
Qed.

(** Source for [affine_space_iso_inv_continuous]: M^{-1} is continuous
    from Hom(V, V) x V into A(V, V) with the topology of N, Federer
    2.7.16, p. 134: M^{-1}(g, z) = M^{-1}(g, 0) + M^{-1}(0, z).
    Supporting lemma. *)
Lemma affine_space_iso_inv_continuous : continuous (fun p : H * VT => (Minv p : MA)).
Proof.
have -> : (fun p : H * VT => (Minv p : MA)) =
    (fun q : MA * MA => (q.1 + q.2 : MA)) \o
    (fun p : H * VT => ((Minv ((p.1 : Hom V V), 0) : MA), (Minv (0, (p.2 : V)) : MA))).
  apply: funext=> -[g z] /=.
  have h := affine_space_iso_inv_linear hA 1 ((g : Hom V V), 0) (0, (z : V)).
  rewrite !scale1r in h; rewrite -h.
  congr Minv; apply: injective_projections; [exact: (esym (addr0 _))|exact: (esym (add0r _))].
move=> p; apply: continuous_comp; last exact: real_norm_metric_add_continuous.
apply: (@topological_pair_continuous (H * VT)%type MA MA).
- exact: (@first_factor_continuous H VT MA _ affine_space_iso_inv_first_continuous).
- exact: (@second_factor_continuous H VT MA _ affine_space_iso_inv_second_continuous).
Qed.

(** Source for [affine_space_iso_homeomorphism]: "all norms on A(V, V)
    induce the same locally compact topology ... Using the maps L, M,
    tau", Federer 2.7.16, p. 134: for every norm N on A(V, V), the
    linear isomorphism M(f) = (L(f), f(0)) is a homeomorphism of A(V, V)
    with the topology of N onto Hom(V, V) x V with the product topology,
    in the sense of 2.7.1, p. 121; so the topology of N is the one
    transported by M. Direct formalisation; supplied proof. *)
Theorem affine_space_iso_homeomorphism :
  is_homeomorphism_with_inverse (fun f : MA => (M f : H * VT)) (fun p : H * VT => (Minv p : MA)).
Proof.
split.
- exact: affine_space_iso_continuous.
- exact: affine_space_iso_inv_continuous.
- exact: (affine_space_isoK hA).
- exact: (affine_space_iso_invK hA).
Qed.

(** Source for [affine_space_norm_locally_compact]: "all norms on
    A(V, V) induce the same locally compact topology", Federer 2.7.16,
    p. 134: the topology of N is locally compact. Direct
    formalisation. *)
Theorem affine_space_norm_locally_compact : locally_compact [set: MA].
Proof. exact: (@finite_norm_locally_compact R A _ _ affine_space_finite_basis N hN). Qed.

(** Source for [affine_space_norm_hausdorff]: the topology of N on
    A(V, V) is Hausdorff, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_space_norm_hausdorff : hausdorff_space MA.
Proof. exact: finite_norm_hausdorff. Qed.

(** Source for [is_affine_composition]: "functional composition ... in
    A(V, V)", Federer 2.7.16, p. 134: comp(f, g) is the member of
    A(V, V) with values f(g(v)). Definition of the operation by its
    values. *)
Definition is_affine_composition (comp : A -> A -> A) : Prop :=
  forall f g, ev (comp f g) = ev f \o ev g.

(** Source for [affine_map_comp_affine]: the composition of affine maps
    is affine, Federer 2.7.16, pp. 133–134. Supporting lemma. *)
Lemma affine_map_comp_affine (f g : V -> V) : is_affine_map f -> is_affine_map g -> is_affine_map (f \o g).
Proof. by move=> hf hg v w s t hst; rewrite /= hg // hf. Qed.

(** Source for [affine_composition_exists]: functional composition is
    an operation in A(V, V), Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_composition_exists : exists comp : A -> A -> A, is_affine_composition comp.
Proof.
exists (fun f g => projT1 (cid (affine_space_eval_onto hA
  (affine_map_comp_affine (affine_space_eval_affine hA f) (affine_space_eval_affine hA g))))).
by move=> f g; case: cid.
Qed.

(** Source for [affine_space_iso_comp]: M(f o g) = (L(f) o L(g),
    f(0) + L(f)(g(0))), from "L preserves functional composition",
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_space_iso_comp (comp : A -> A -> A) : is_affine_composition comp ->
  forall f g, M (comp f g) = (hom_comp (L f) (L g), ev f 0 + L f (ev g 0)).
Proof.
move=> hc f g; rewrite /affine_space_iso; congr pair; last first.
  by rewrite hc /= (affine_space_decomposition hA f).
apply: hom_ext=> v; rewrite hom_compE !affine_space_homE hc /=.
rewrite (affine_space_decomposition hA f (ev g v)) (affine_space_decomposition hA f (ev g 0)).
rewrite opprD addrACA subrr add0r.
by rewrite -(linearB (hom_as_linear (L f))).
Qed.

(** Source for [affine_composition_continuous]: "functional composition
    is a continuous operation in A(V, V)", Federer 2.7.16, p. 134, for
    the topology of any norm N on A(V, V) and every composition
    operation. Direct formalisation; the proof follows Federer's
    reduction through M to the continuity of composition and evaluation
    on Hom(V, V). *)
Theorem affine_composition_continuous (comp : A -> A -> A) : is_affine_composition comp ->
  continuous (fun p : MA * MA => (comp p.1 p.2 : MA)).
Proof.
move=> hc.
have -> : (fun p : MA * MA => (comp p.1 p.2 : MA)) =
    (fun q : H * VT => (Minv q : MA)) \o
    (fun p : MA * MA => ((hom_comp (L p.1) (L p.2) : H), (ev p.1 0 + L p.1 (ev p.2 0) : VT))).
  apply: funext=> -[f g] /=.
  by rewrite -(affine_space_iso_comp hc) affine_space_isoK.
move=> p; apply: continuous_comp; last exact: affine_space_iso_inv_continuous.
have hL1 : continuous (fun q : MA * MA => (L q.1 : H)).
  exact: (@first_factor_continuous MA MA H _ affine_space_hom_continuous).
have hL2 : continuous (fun q : MA * MA => (L q.2 : H)).
  exact: (@second_factor_continuous MA MA H _ affine_space_hom_continuous).
have hz1 : continuous (fun q : MA * MA => (ev q.1 0 : VT)).
  exact: (@first_factor_continuous MA MA VT _ affine_space_value_continuous).
have hz2 : continuous (fun q : MA * MA => (ev q.2 0 : VT)).
  exact: (@second_factor_continuous MA MA VT _ affine_space_value_continuous).
apply: (@topological_pair_continuous (MA * MA)%type H VT).
- move=> q; apply: (@continuous_comp (MA * MA)%type (H * H)%type H
    (fun q : MA * MA => ((L q.1 : H), (L q.2 : H)))
    (fun r : H * H => (hom_comp (r.1 : Hom V V) (r.2 : Hom V V) : H))).
    exact: (@topological_pair_continuous (MA * MA)%type H H _ _ hL1 hL2).
  exact: hom_composition_continuous.
- move=> q; apply: (@continuous_comp (MA * MA)%type (VT * VT)%type VT
    (fun q : MA * MA => ((ev q.1 0 : VT), ((L q.1 : Hom V V) (ev q.2 0) : VT)))
    (fun r : VT * VT => r.1 + r.2)); last exact: add_continuous.
  apply: (@topological_pair_continuous (MA * MA)%type VT VT _ _ hz1).
  exact: (@hom_evaluation_continuous_comp R V B hB n b hb (MA * MA)%type _ _ hL1 hz2).
Qed.

(** Source for [affine_space_group]: "the affine group of V, the ...
    subset of univalent maps in A(V, V)", Federer 2.7.16, p. 134.
    Definition. *)
Definition affine_space_group : set MA := [set f | injective (ev f)].

Local Notation GA := (set_type affine_space_group).

(** Source for [affine_space_groupE]: the affine group "equals
    L^{-1}(linear group of V)", Federer 2.7.16, p. 134. Direct
    formalisation, from affine_univalent_iff. *)
Theorem affine_space_groupE : affine_space_group = (fun f : MA => (L f : H)) @^-1` linear_group hB hb.
Proof.
apply/seteqP; split=> f /=; rewrite /affine_space_group /linear_group /=.
- by move/affine_univalent_iff.
- by move=> h; apply/affine_univalent_iff.
Qed.

(** Source for [affine_space_group_open]: the affine group is an "open
    ... subset of univalent maps in A(V, V)", Federer 2.7.16, p. 134,
    for the topology of any norm N on A(V, V). Direct formalisation:
    the inverse image of the open linear group under the continuous
    map L. *)
Theorem affine_space_group_open : open affine_space_group.
Proof.
rewrite affine_space_groupE.
by move/continuousP: affine_space_hom_continuous; apply; exact: linear_group_set_open.
Qed.

(** Source for [affine_space_iso_inv_slice_continuous]: g |-> M^{-1}(g, z)
    is continuous from Hom(V, V) into A(V, V), Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma affine_space_iso_inv_slice_continuous (z : V) :
  continuous (fun g : H => (Minv ((g : Hom V V), z) : MA)).
Proof.
move=> g; apply: (@continuous_comp H (H * VT)%type MA (fun g : H => (g, (z : VT)))
  (fun p : H * VT => (Minv p : MA))); last exact: affine_space_iso_inv_continuous.
apply: (@topological_pair_continuous H H VT); [by move=> x; exact: cvg_id|exact: cst_continuous].
Qed.

(** Source for [affine_space_group_dense]: the affine group is a
    "dense subset of univalent maps in A(V, V)", Federer 2.7.16, p. 134,
    for the topology of any norm N on A(V, V). Direct formalisation:
    a nonempty open set O containing f meets the affine group at
    M^{-1}(g, f(0)) for some g of the linear group, because the linear
    group is dense in Hom(V, V). *)
Theorem affine_space_group_dense : dense affine_space_group.
Proof.
move=> O [f hf] hO.
pose s (g : H) : MA := Minv ((g : Hom V V), ev f 0).
have hs : continuous s by exact: affine_space_iso_inv_slice_continuous.
have hU : open (s @^-1` O) by move/continuousP: hs; apply.
have hfU : (s @^-1` O) (L f : H).
  by rewrite /s /= -/(affine_space_iso hA f) affine_space_isoK.
have [g [hgU hgG]] := linear_group_set_dense (ex_intro _ _ hfU) hU.
exists (s g); split=> //.
by rewrite affine_space_groupE /= /s affine_space_hom_onto.
Qed.

(** Source for [affine_space_group_map_proof]: M^{-1}(g, z) is
    univalent for g in the linear group, Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma affine_space_group_map_proof (p : AG) :
  affine_space_group (Minv ((set_val p.1 : Hom V V), (p.2 : V)) : MA).
Proof. by rewrite affine_space_groupE /= affine_space_hom_onto; exact: set_valP. Qed.

(** Source for [affine_space_group_map]: the univalent affine map
    M^{-1}(g, z) = tau_z o g for g in the linear group, Federer 2.7.16,
    p. 134, as a member of the affine group of A(V, V). Definition. *)
Definition affine_space_group_map (p : AG) : GA :=
  exist _ (Minv ((set_val p.1 : Hom V V), (p.2 : V)) : MA) (mem_set (@affine_space_group_map_proof p)).

(** Source for [affine_space_group_mapE]: M^{-1}(g, z) = tau_z o g,
    Federer 2.7.16, p. 134: the member of A(V, V) attached to (g, z) has
    the values of affine_group_map of AffineGroupTopology.v. Supporting
    lemma. *)
Lemma affine_space_group_mapE (p : AG) : ev (set_val (affine_space_group_map p)) = affine_group_map hB hb p.
Proof. by rewrite /= affine_space_iso_invE. Qed.

(** Source for [affine_space_group_coordinates_proof]: L(f) belongs to
    the linear group for f in the affine group, Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma affine_space_group_coordinates_proof (a : GA) : linear_group hB hb (L (set_val a) : H).
Proof.
have h : injective (ev (set_val a)) := set_valP a.
by move/affine_univalent_iff: h.
Qed.

(** Source for [affine_space_group_coordinates]: M(f) = (L(f), f(0))
    for f in the affine group, with L(f) in the linear group, Federer
    2.7.16, p. 134. Definition. *)
Definition affine_space_group_coordinates (a : GA) : AG :=
  (exist _ (L (set_val a) : H) (mem_set (@affine_space_group_coordinates_proof a)), (ev (set_val a) 0 : VT)).

(** Source for [affine_space_group_homeomorphism]: the relative
    topology of the affine group in A(V, V), for any norm N, is the
    topology of AffineGroupTopology.v: (g, z) |-> M^{-1}(g, z) is a
    homeomorphism of the product of the linear group and V onto the
    affine group, with inverse f |-> M(f), Federer 2.7.16, p. 134, in
    the sense of 2.7.1, p. 121. Direct formalisation of the
    identification. *)
Theorem affine_space_group_homeomorphism :
  is_homeomorphism_with_inverse affine_space_group_map affine_space_group_coordinates.
Proof.
split.
- apply: set_type_continuous_into.
  have -> : set_val \o affine_space_group_map =
      (fun q : H * VT => (Minv q : MA)) \o (fun p : AG => ((set_val p.1 : H), p.2)) by [].
  move=> p; apply: continuous_comp; last exact: affine_space_iso_inv_continuous.
  apply: (@topological_pair_continuous AG H VT).
  + exact: (@first_factor_continuous GL VT H _ (@set_type_val_continuous H (linear_group hB hb))).
  + exact: second_projection_continuous.
- apply: (@topological_pair_continuous GA GL VT).
  + apply: set_type_continuous_into.
    have -> : set_val \o (fun a : GA => (affine_space_group_coordinates a).1) =
        (fun f : MA => (L f : H)) \o set_val by [].
    move=> a; apply: continuous_comp; last exact: affine_space_hom_continuous.
    exact: set_type_val_continuous.
  + move=> a; apply: (@continuous_comp GA MA VT set_val (fun f : MA => (ev f 0 : VT))).
      exact: set_type_val_continuous.
    exact: affine_space_value_continuous.
- move=> [g z]; rewrite /affine_space_group_coordinates /=; congr pair.
    by apply: val_inj; rewrite /= affine_space_hom_onto.
  exact: (affine_space_iso_inv_zero hA).
- move=> a; apply: val_inj; rewrite /=.
  exact: (affine_space_isoK hA (set_val a)).
Qed.

(** Source for [affine_space_group_map_coordinates]: every member f of
    the affine group is M^{-1}(L(f), f(0)), Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma affine_space_group_map_coordinates (a : GA) :
  ev (set_val a) = affine_group_map hB hb (affine_space_group_coordinates a).
Proof.
rewrite -affine_space_group_mapE.
by rewrite (homeomorphism_right_inverse affine_space_group_homeomorphism a).
Qed.

(** Source for [is_affine_inversion]: "inversion ... on the affine group
    of V", Federer 2.7.16, p. 134: inv(f) is the member of the affine
    group with values f^{-1}. Definition of the operation by its
    values. *)
Definition is_affine_inversion (inv : GA -> GA) : Prop :=
  forall a, cancel (ev (set_val a)) (ev (set_val (inv a))) /\ cancel (ev (set_val (inv a))) (ev (set_val a)).

(** Source for [affine_space_group_inverse]: the inverse of f in the
    affine group is M^{-1} of the inverse in the representation of
    AffineGroupTopology.v, Federer 2.7.16, p. 134. Definition. *)
Definition affine_space_group_inverse (a : GA) : GA :=
  affine_space_group_map (affine_group_inv hB hb (affine_space_group_coordinates a)).

(** Source for [affine_space_group_inverseP]: the inverse of a
    univalent affine map is affine, Federer 2.7.16, p. 134: the map
    affine_space_group_inverse is an inversion of the affine group.
    Supporting lemma. *)
Lemma affine_space_group_inverseP : is_affine_inversion affine_space_group_inverse.
Proof.
move=> a; rewrite /affine_space_group_inverse affine_space_group_mapE affine_space_group_map_coordinates.
exact: affine_group_map_inv.
Qed.

(** Source for [affine_inversion_exists]: inversion is an operation on
    the affine group of V, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_inversion_exists : exists inv : GA -> GA, is_affine_inversion inv.
Proof. by exists affine_space_group_inverse; exact: affine_space_group_inverseP. Qed.

(** Source for [affine_inversion_unique]: the inverse map is unique,
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_inversion_unique (inv : GA -> GA) : is_affine_inversion inv -> inv =1 affine_space_group_inverse.
Proof.
move=> hi a; apply: val_inj; apply: (affine_space_eval_inj hA); apply: funext=> x.
have [h1 _] := hi a; have [_ h2] := affine_space_group_inverseP a.
by rewrite -[x in LHS]h2 h1.
Qed.

(** Source for [affine_inversion_continuous]: "inversion is continuous
    on the affine group of V", Federer 2.7.16, p. 134, for the relative
    topology of the affine group in A(V, V) with the topology of any
    norm N, and every inversion operation. Direct formalisation, by the
    homeomorphism with the representation of AffineGroupTopology.v. *)
Theorem affine_inversion_continuous (inv : GA -> GA) : is_affine_inversion inv -> continuous inv.
Proof.
move=> hi; rewrite (funext (affine_inversion_unique hi)).
have [hc hci _ _] := affine_space_group_homeomorphism.
have hgi := @affine_group_inv_continuous R V B hB n b hb.
have -> : affine_space_group_inverse =
    affine_space_group_map \o (affine_group_inv hB hb \o affine_space_group_coordinates) by [].
move=> a; apply: (continuous_comp _ (hc _)).
exact: continuous_comp (hci a) (hgi _).
Qed.

(** Source for [is_affine_group_structure]: the affine group of V with
    functional composition, inversion and 1_V, Federer 2.7.16, p. 134.
    The operations are specified by their values. *)
Definition is_affine_group_structure (mul : GA -> GA -> GA) (inv : GA -> GA) (e : GA) : Prop :=
  [/\ forall a c, ev (set_val (mul a c)) = ev (set_val a) \o ev (set_val c), is_affine_inversion inv &
    ev (set_val e) = id].

(** Source for [affine_group_structure_exists]: the operations of the
    affine group of V exist, Federer 2.7.16, p. 134. Supporting
    lemma. *)
Lemma affine_group_structure_exists : exists mul inv e, is_affine_group_structure mul inv e.
Proof.
exists (fun a c => affine_space_group_map
  (affine_group_mul hB hb (affine_space_group_coordinates a) (affine_space_group_coordinates c))).
exists affine_space_group_inverse, (affine_space_group_map (affine_group_unit hB hb)).
split.
- move=> a c; rewrite affine_space_group_mapE affine_group_map_mul.
  by rewrite -!affine_space_group_map_coordinates.
- exact: affine_space_group_inverseP.
- by rewrite affine_space_group_mapE affine_group_map_unit.
Qed.

(** Source for [affine_space_group_lch]: "It should be clear from the
    preceding remarks that the topological assumptions of our general
    theory are satisfied", Federer 2.7.16, p. 134, for the affine group
    of V with the relative topology of A(V, V) for any norm N: it is a
    locally compact Hausdorff topological group in the sense of 2.7.1,
    p. 121. Direct formalisation, transported from affine_group_lch of
    AffineGroupTopology.v by the homeomorphism M. *)
Theorem affine_space_group_lch (mul : GA -> GA -> GA) (inv : GA -> GA) (e : GA) :
  is_affine_group_structure mul inv e -> is_locally_compact_hausdorff_group mul inv e.
Proof.
move=> [hm hi he].
apply: (lch_group_transport affine_space_group_homeomorphism _ _ _ (affine_group_lch hB hb)).
- move=> p q; apply: val_inj; apply: (affine_space_eval_inj hA).
  rewrite hm !affine_space_group_mapE.
  exact: affine_group_map_mul.
- move=> p; rewrite (affine_inversion_unique hi) /affine_space_group_inverse.
  by rewrite (homeomorphism_left_inverse affine_space_group_homeomorphism).
- apply: val_inj; apply: (affine_space_eval_inj hA).
  by rewrite he affine_space_group_mapE affine_group_map_unit.
Qed.

End AffineSpaceTopology.

Section NormIndependence.
Variable R : realType.
Variable V : lmodType R.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable A : lmodType R.
Variable ev : A -> V -> V.
Hypothesis hA : is_affine_map_space ev.

(** Source for [affine_space_norms_same_nbhs]: "If dim V < oo, then
    dim A(V, V) < oo and all norms on A(V, V) induce the same ...
    topology", Federer 2.7.16, p. 134: for any two norms N_1, N_2 on
    A(V, V), a set S is a neighbourhood of f for the metric of N_1 if
    and only if it is one for the metric of N_2. Direct formalisation;
    no inner product on V is needed. *)
Theorem affine_space_norms_same_nbhs (N1 N2 : A -> R) (h1 : is_real_norm N1) (h2 : is_real_norm N2)
    (f : A) (S : set A) :
  nbhs (f : real_norm_metric_space h1) S <-> nbhs (f : real_norm_metric_space h2) S.
Proof. exact: (@finite_norms_same_nbhs R A _ _ (@affine_space_basisP R V V A ev hA n n b hb b hb)). Qed.

End NormIndependence.
