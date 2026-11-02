(** Federer (1969), 2.5.15, pp. 108-109: Example. Let Y={y: -1<=y<=1}, J
    uncountable, X=Y^J with the Cartesian product topology, p_j the
    projections, xi the point with p_j(xi)=0 for all j, lambda the Daniell
    integral on K(X) with lambda(f)=f(xi), and phi the K(X) regular measure
    associated with lambda. The compact set {xi} is not phi measurable
    because phi(X)=phi({xi})=phi(X minus {xi})=1. The last equation uses
    that every f in K(X), and every limit of a sequence in K(X), depends
    only on countably many coordinates; this is proved here from compactness
    instead of the Weierstrass-Stone theorem cited by Federer. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology subtype_topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP MonotoneDaniellIntegralUP
  DaniellCoverUP ExtendedRealBoundsUP MeasureUP MeasureBasic MeasureSplit
  RealIntegralFunctionalUP FunctionLatticeRegularityUP RegularDaniellRepresentation
  RegularDaniellEnvelope CompactSupportFunctionUP CompactSupportFunctionLattice
  DaniellEnvelopeBounds PointMassMeasure SubtypeCompactHausdorff ProductCoordinateNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Example.
Variable R : realType.
Variable J : choiceType.
Hypothesis hJ : ~ countable (@setT J).

(** Source for [closed_unit_segment]: the set Y={y: -1<=y<=1} of
    Federer 2.5.15, p. 108. *)
Definition closed_unit_segment : set R := `[(-1)%R, 1%R]%classic.

(** Source for [segment_space]: Y as a topological space, with the
    topology induced from the real line, Federer 2.5.15, p. 108. *)
Definition segment_space : Type := set_type closed_unit_segment.

(** Source for [segment_zero_member]: zero belongs to Y, Federer
    2.5.15, p. 108, giving the coordinates of xi. *)
Lemma segment_zero_member : closed_unit_segment 0%R.
Proof. by rewrite /closed_unit_segment /= in_itv /= lerN10 ler01. Qed.

(** Source for [segment_one_member]: one belongs to Y, supporting the
    point used to show phi(X minus {xi})=1 in Federer 2.5.15, p. 109. *)
Lemma segment_one_member : closed_unit_segment 1%R.
Proof. by rewrite /closed_unit_segment /= in_itv /= lexx andbT; exact (le_trans (@lerN10 R) (@ler01 R)). Qed.

(** Source for [segment_zero]: the element zero of Y, Federer 2.5.15,
    p. 108. *)
Definition segment_zero : segment_space := exist _ (0%R : R) (mem_set segment_zero_member).

(** Source for [segment_one]: the element one of Y, Federer 2.5.15,
    p. 109. *)
Definition segment_one : segment_space := exist _ (1%R : R) (mem_set segment_one_member).

HB.instance Definition _ := Topological.copy segment_space (set_type closed_unit_segment).
HB.instance Definition _ := isPointed.Build segment_space segment_zero.

(** Source for [product_space]: X=Y^J with the Cartesian product
    topology, Federer 2.5.15, p. 108. *)
Definition product_space : Type := prod_topology (fun _ : J => segment_space).

HB.instance Definition _ := Topological.copy product_space (prod_topology (fun _ : J => segment_space)).
HB.instance Definition _ := isPointed.Build product_space (fun _ : J => segment_zero).

(** Source for [base_point]: the point xi with p_j(xi)=0 for all j,
    Federer 2.5.15, p. 108. *)
Definition base_point : product_space := fun _ => segment_zero.

(** Source for [segment_space_compact]: Y is compact, Federer 2.5.15,
    p. 108, from compactness of the real segment. *)
Lemma segment_space_compact : compact [set: segment_space].
Proof. exact (set_type_compact_whole (@segment_compact R (-1)%R 1%R)). Qed.

(** Source for [segment_space_hausdorff]: Y is Hausdorff, Federer
    2.5.15, p. 108. *)
Lemma segment_space_hausdorff : hausdorff_space segment_space.
Proof. exact: set_type_hausdorff (@Rhausdorff R). Qed.

(** Source for [product_space_compact]: X is compact by Tychonoff's
    theorem, Federer 2.5.15, p. 108; general-topology background. *)
Lemma product_space_compact : compact [set: product_space].
Proof.
have h := @tychonoff J (fun _ : J => segment_space) (fun _ => setT) (fun _ => segment_space_compact).
by apply: (subclosed_compact closedT h)=> f _ i.
Qed.

(** Source for [product_space_hausdorff]: X is Hausdorff, Federer
    2.5.15, p. 108. *)
Lemma product_space_hausdorff : hausdorff_space product_space.
Proof. exact: hausdorff_product (fun _ => segment_space_hausdorff). Qed.

(** Source for [product_space_locally_compact]: X is locally compact,
    as required by the lattice K(X) of Federer 2.5.13, p. 106, in
    2.5.15, p. 108. *)
Lemma product_space_locally_compact : locally_compact [set: product_space].
Proof. exact: compact_space_locally_compact product_space_compact. Qed.

Local Notation KX := (@compactly_supported_continuous_functions R product_space).

(** Source for [evaluation_functional]: the Daniell integral lambda on
    K(X) with lambda(f)=f(xi), Federer 2.5.15, p. 108. *)
Definition evaluation_functional (f : product_space -> R) : R := f base_point.

(** Source for [evaluation_monotone_daniell]: lambda is a monotone
    Daniell integral in the sense of Federer 2.5.2, p. 92, as required
    for its K(X) regular measure in 2.5.15, p. 108. *)
Lemma evaluation_monotone_daniell : is_monotone_daniell_integral KX evaluation_functional.
Proof.
constructor; rewrite /evaluation_functional.
- by [].
- by [].
- by move=> f g _ _ hfg; exact: hfg.
- by move=> f g _ _ hfg; exact: hfg.
Qed.

(** Source for [product_space_lattice_member]: every continuous real
    function on the compact space X belongs to K(X), Federer 2.5.15,
    p. 108, since closed subsets of X are compact. *)
Lemma product_space_lattice_member (f : product_space -> R) :
  continuous (f : product_space -> real_line_metric R) -> KX f.
Proof.
move=> hf; split=> //.
exact (subclosed_compact (@real_function_support_closed R _ f) product_space_compact (subsetT _)).
Qed.

(** Source for [constant_one_positive_member]: the constant one belongs
    to K(X)+, giving phi(X) <= lambda(1)=1 in Federer 2.5.15, p. 108. *)
Lemma constant_one_positive_member : positive_function_lattice KX (fun _ : product_space => 1%R).
Proof.
split; last by move=> x; exact: ler01.
exact: product_space_lattice_member (@cst_continuous _ _ _).
Qed.

(** Source for [evaluation_regular_measure_exists]: existence of the
    K(X) regular measure phi associated with lambda, Federer 2.5.15,
    p. 108, by 2.5.3, p. 94. *)
Theorem evaluation_regular_measure_exists : exists phi : set product_space -> \bar R,
  is_measure phi /\ is_real_integral_functional phi KX evaluation_functional /\
  is_function_lattice_regular KX phi.
Proof.
have [phi [hm [hi [hr _]]]] := monotone_daniell_regular_representation
  (@compactly_supported_continuous_functions_lattice R product_space)
  evaluation_monotone_daniell (ex_intro _ _ constant_one_positive_member.1).
by exists phi.
Qed.

(** Source for [off_base_point_exists_coordinate]: supporting choice of
    a coordinate i in J minus S for a countable S, Federer 2.5.15,
    p. 109, using that J is uncountable. *)
Lemma off_base_point_exists_coordinate (S : set J) : countable S -> exists i, ~ S i.
Proof.
move=> hS; apply: contrapT=> hn; apply: hJ.
apply: sub_countable _ hS; apply: subset_card_le=> i _.
by apply: contrapT=> h; apply: hn; exists i.
Qed.

(** Source for [modified_base_point_values]: the point x with
    p_i(x)=1 and p_j(x)=0 for j<>i, Federer 2.5.15, p. 109: it
    differs from xi and agrees with xi off i. *)
Lemma modified_base_point_values (i : J) :
  let x : product_space := fun j => if j == i then segment_one else base_point j in
  x <> base_point /\ forall j, j <> i -> x j = base_point j.
Proof.
move=> x; split.
- move=> h; have := congr1 (fun y : product_space => val (y i)) h.
  rewrite /x eqxx /= => /eqP; rewrite /segment_one /base_point /segment_zero /=.
  by apply/negP; exact: oner_neq0.
- by move=> j hji; rewrite /x; case: eqP=> // hj; case: hji.
Qed.

Section Measure.
Variable phi : set product_space -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hA : is_real_integral_functional phi KX evaluation_functional.
Hypothesis hr : is_function_lattice_regular KX phi.

(** Source for [evaluation_envelope]: the suiting-sequence envelope law
    of 2.5.2, p. 92, for phi, Federer 2.5.15, p. 108. *)
Lemma evaluation_envelope : is_daniell_cover_envelope KX evaluation_functional phi.
Proof.
exact (regular_representing_measure_envelope
  (@compactly_supported_continuous_functions_lattice R product_space) hm hA hr).
Qed.

(** Source for [phi_whole_upper]: phi(X) <= 1, since the constant one
    suits X and lambda(1)=1, Federer 2.5.15, p. 108. *)
Lemma phi_whole_upper : phi setT <= 1.
Proof.
exact: daniell_envelope_hull_bound evaluation_envelope setT _
  constant_one_positive_member (fun x _ => lexx 1).
Qed.

(** Source for [point_mass_le_phi]: the point mass at xi is dominated by
    phi, Federer 2.5.15, p. 108, by the lower envelope estimate of
    2.5.2, p. 92. *)
Lemma point_mass_le_phi (S : set product_space) : point_mass R base_point S <= phi S.
Proof.
apply: (daniell_envelope_dominates (@compactly_supported_continuous_functions_lattice R product_space)
  evaluation_monotone_daniell evaluation_envelope (point_mass_is_measure R base_point)).
- by move=> f t hf ht; exact: point_mass_level_bound (hf.2 base_point) ht.
- by move=> V c _ hc; exact: point_mass_increasing_union hc.
Qed.

(** Source for [phi_whole]: phi(X)=1, Federer 2.5.15, p. 108. *)
Theorem phi_whole : phi setT = 1.
Proof.
apply/le_anti/andP; split; first exact: phi_whole_upper.
by rewrite -(point_mass_in R (S := setT) (x0 := base_point) Logic.I); exact: point_mass_le_phi.
Qed.

(** Source for [phi_base_point]: phi({xi})=1, Federer 2.5.15, p. 108. *)
Theorem phi_base_point : phi [set base_point] = 1.
Proof.
apply/le_anti/andP; split.
- exact: le_trans (measure_mono hm (subsetT _)) phi_whole_upper.
- by rewrite -(point_mass_in R (S := [set base_point]) (x0 := base_point) erefl); exact: point_mass_le_phi.
Qed.

(** Source for [suiting_sequence_coordinates]: a suiting sequence of
    X minus {xi} gives, by countable dependence on coordinates, a point
    x<>xi with f_n(x)=f_n(xi) for all n, Federer 2.5.15, p. 109. *)
Lemma suiting_sequence_coordinates (f : nat -> product_space -> R) :
  (forall n, positive_function_lattice KX (f n)) ->
  exists x : product_space, x <> base_point /\ forall n, f n x = f n base_point.
Proof.
move=> hf.
have hdet : forall n, exists S : set J, countable S /\
    forall y z, (forall j, S j -> y j = z j) -> f n y = f n z.
  move=> n; exact: compact_product_continuous_countably_determined
    product_space_compact (hf n).1.1.
pose Sn := fun n => sval (cid (hdet n)).
have hS : countable (\bigcup_n Sn n).
  by apply: bigcup_countable=> // n _; exact: (svalP (cid (hdet n))).1.
have [i hi] := off_base_point_exists_coordinate hS.
have [hne hagree] := modified_base_point_values i.
exists ((fun j => if j == i then segment_one else base_point j)); split=> // n.
apply: (svalP (cid (hdet n))).2=> j hj; apply: hagree=> hji.
by apply: hi; exists n=> //; rewrite -hji.
Qed.

(** Source for [phi_complement_base_point]: phi(X minus {xi})=1, Federer
    2.5.15, pp. 108-109: if X minus {xi} is contained in {x: f(x)>=1}
    for the limit f of a suiting sequence, then f(xi)>=1. *)
Theorem phi_complement_base_point : phi (setT `\` [set base_point]) = 1.
Proof.
apply/le_anti/andP; split.
- exact: le_trans (measure_mono hm (subsetT _)) phi_whole_upper.
- apply: (daniell_cover_greatest evaluation_envelope)=> f c [hpos [_ hlim]] hcost.
  have hfc : forall n, (f n base_point)%:E <= c.
    by move=> n; apply: (extended_real_supremum_upper hcost); exists n.
  have [x [hx hfx]] := suiting_sequence_coordinates hpos.
  have hlt : forall r : R, (r < 1)%R -> r%:E < c.
    move=> r hr1; have [n hn] := hlim x (conj Logic.I hx) r hr1.
    rewrite hfx in hn.
    have hn' : r%:E < (f n base_point)%:E by rewrite lte_fin.
    exact: lt_le_trans hn' (hfc n).
  have hc0 : 0 <= c.
    apply: le_trans (hfc 0%N); rewrite lee_fin; exact: (hpos 0%N).2.
  case: c hfc hlt hc0 {hcost}=> [c0 hfc hlt hc0|_ _ _|_ _ h]; last by rewrite leeNy_eq in h.
  - rewrite lee_fin leNgt; apply/negP=> hc1.
    by have := hlt c0 hc1; rewrite ltxx.
  - exact: leey.
Qed.

(** Source for [base_point_not_measurable]: the compact set {xi} is not
    phi measurable, Federer 2.5.15, p. 108, because
    phi(X)=phi({xi})=phi(X minus {xi})=1. *)
Theorem base_point_not_measurable : ~ measure_measurable phi [set base_point].
Proof.
move=> h; have := h setT; rewrite setTI phi_whole phi_base_point phi_complement_base_point.
by rewrite -EFinD=> /eqP; rewrite eqe eq_sym -subr_eq0 addrK oner_eq0.
Qed.

(** Source for [base_point_compact]: {xi} is compact, Federer 2.5.15,
    p. 108; thus phi is not a Radon measure. *)
Lemma base_point_compact : compact [set base_point].
Proof. exact: compact_set1. Qed.

End Measure.
End Example.
