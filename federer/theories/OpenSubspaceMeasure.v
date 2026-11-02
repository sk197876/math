(** The restriction of a measure to an open subspace, supporting Federer
    (1969), 2.7.16, examples (2) and (3), printed pp. 136–138: "In case U =
    V, phi is a left |det|^{-n} covariant measure over G", "phi is right
    Delta_G |det|^n covariant over G", "every Haar measure gamma of X is
    right Delta_G chi^{-1} covariant over G". There a Haar measure of the
    additive group of a vector space X is regarded as a measure over the
    open subset G of X. Let T be a locally compact Hausdorff metric space
    with a countable base, S an open subset of T with the relative topology
    (set_type), phi a measure over T which is K(T) regular and represents a
    monotone Daniell integral mu on K(T) (2.5.2–2.5.3, pp. 92–94). The
    restriction of phi to S is the measure T' |-> phi(T') over S
    (open_subspace_measure). This module proves that it is the K(S) regular
    measure associated with the monotone Daniell integral nu(u) = mu(u') on
    K(S), u' the extension of u by 0 (OpenSubspaceExtension.v), and that it
    is a Radon measure (open_subspace_measure_associated). Consequently it
    is a chi covariant measure in the sense of 2.7.1, p. 122, whenever nu is
    chi covariant (open_subspace_covariant_measure). The proof generalises
    PuncturedLebesgueCovariance.v. The image of the restriction under the
    inclusion of S is the restriction phi L S of 2.1.2, p. 54, so that int u
    d(phi over S) = int u' d(phi L S) = int u' dphi by 2.4.18, p. 90, and
    2.4.10, p. 85, since S is phi measurable (phi is a Radon measure by
    2.5.14, p. 107). The restriction is Borel regular; the K(S) regular
    measure representing nu is a Radon measure by 2.5.14, hence Borel
    regular, and the two coincide by RepresentingMeasureComparison.v (2.2.3,
    p. 61), because S is a locally compact metric space with a countable
    base covered by countably many open sets with compact closure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover MeasureRestriction MeasurePushforward
  TopologicalBorel ContinuousBorelPreimages BorelRegularMeasureUP CountableOpenBaseUP
  RadonMeasureUP RadonBorelRegularity CompactSupportFunctionUP CompactSupportFunctionLattice
  FunctionLatticeUP FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness
  RealIntegralFunctionalUP MonotoneDaniellIntegralUP CovariantIntegralUP RegularDaniellRepresentation
  CompactSupportCountableRadon RepresentingMeasureComparison ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension
  PartialFunctionPrecomposition MeasureIntegralUP MeasurableFunctionUP SummableRealFunctionUP
  MeasureIntegralGraphEquivalence RestrictedIntegralIdentity PushforwardIntegral
  PushforwardMeasurabilityTransfer CovariantMeasureImage SubtypeCompactHausdorff IsotropyGroupTopology
  OpenSubspaceExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_subspace_measure]: phi over G, T' |-> phi(T') for
    subsets T' of the open set G, in "phi is a left |det|^{-n} covariant
    measure over G", Federer 2.7.16, p. 136, and "gamma ... over G",
    p. 137, for an arbitrary subset S of the space. Definition. *)
Definition open_subspace_measure (R : realType) (T : Type) (S : set T) (phi : set T -> \bar R)
    (A : set (set_type S)) : \bar R :=
  phi (set_val @` A).

Section CompactNeighbourhoods.
Variable R : realType.
Variable T : pseudoMetricType R.
Hypothesis hl : locally_compact [set: T].
Variable S : set T.
Hypothesis hS : open S.
Local Notation Y := (set_type S).

(** Source for [closure_half_ball]: the closure of the ball of radius
    r/2 about a lies in the ball of radius r about a; metric background
    for the local compactness of the open set G, Federer 2.7.16,
    pp. 134–137. Supporting lemma. *)
Lemma closure_half_ball (a : T) (r : R) : 0 < r -> closure (ball a (r / 2)) `<=` ball a r.
Proof.
move=> hr y hy.
have hr2 : 0 < r / 2 by rewrite divr_gt0.
have [z [hz1 hz2]] := hy _ (nbhsx_ballx y _ hr2).
rewrite [r]splitr; exact: ball_triangle hz1 (ball_sym hz2).
Qed.

(** Source for [open_compact_neighbourhood]: every point a of an open
    subset S of a locally compact metric space has a compact closed
    neighbourhood C with C a subset of S; general topology supporting
    the local compactness of G and of the set of monomorphisms, Federer
    2.7.16, pp. 134–137. Supporting lemma. *)
Lemma open_compact_neighbourhood (a : T) : S a ->
  exists C : set T, [/\ nbhs a C, compact C, closed C & C `<=` S].
Proof.
move=> ha.
have [N hN [hNc hNcl]] := @hl a I; rewrite withinET in hN.
have hSN : nbhs a (S `&` N) by apply: filterI=> //; apply: open_nbhs_nbhs; split.
have /nbhs_ballP [r hr hsub] := hSN.
have hr2 : 0 < r / 2 by rewrite divr_gt0.
have hsub' : closure (ball a (r / 2)) `<=` S `&` N.
  by move=> y hy; apply: hsub; exact: closure_half_ball hy.
exists (closure (ball a (r / 2))); split.
- apply: filterS (nbhsx_ballx a _ hr2); exact: subset_closure.
- apply: (subclosed_compact (@closed_closure _ _) hNc)=> y hy; exact: (hsub' y hy).2.
- exact: closed_closure.
- by move=> y hy; exact: (hsub' y hy).1.
Qed.

(** Source for [pseudometric_open_subspace_locally_compact]: an open
    subset S of a locally compact metric space is locally compact in the
    relative topology, as required of G in Federer 2.7.1, p. 121, and
    used in 2.7.16, pp. 134–137. Supporting lemma. *)
Lemma pseudometric_open_subspace_locally_compact : locally_compact [set: Y].
Proof.
move=> a _; rewrite withinET.
have [C [hC hCc hCcl hCS]] := open_compact_neighbourhood (set_valP a).
exists (set_val @^-1` C : set Y); last split.
- exact: (@set_type_val_continuous T S a).
- exact: set_type_compact_preimage.
- by apply: preimage_closed hCcl=> c _; exact: set_type_val_continuous.
Qed.

Variable U : nat -> set T.
Hypothesis hU : is_countable_open_base U.

(** Source for [open_subspace_countable_open_base]: an open subset of a
    space with a countable base has a countable base, the traces of the
    base, as needed for 2.5.14, p. 107, in Federer 2.7.16, pp. 136–138.
    Supporting lemma. *)
Lemma open_subspace_countable_open_base : is_countable_open_base (fun j => set_val @^-1` U j : set Y).
Proof.
split.
- move=> j; apply: open_comp; last exact: (countable_base_open hU j).
  by move=> x _; exact: set_type_val_continuous.
- by rewrite (countable_base_empty hU) preimage_set0.
- move=> W [O hO <-] x hx.
  have [i [hi hiO]] := countable_base_refines hU hO hx.
  by exists i; split=> // y hy; exact: hiO.
Qed.

(** Source for [open_subspace_cover_set]: the trace on S of the j-th
    member of the base if that member lies in a compact subset of S,
    and the empty set otherwise; supporting the hypotheses of
    RepresentingMeasureComparison.v used for Federer 2.7.16,
    pp. 136–138. Definition. *)
Definition open_subspace_cover_set (j : nat) : set Y :=
  [set y | U j (set_val y) /\ exists C : set T, [/\ compact C, U j `<=` C & C `<=` S]].

(** Source for [open_subspace_compact_cover]: S is covered by the open
    sets open_subspace_cover_set j, each contained in a compact subset of
    S, supporting the hypotheses of 2.5.14, p. 107, and 2.2.3, p. 61, in
    Federer 2.7.16, pp. 136–138. Supporting lemma. *)
Lemma open_subspace_compact_cover :
  [/\ forall j, open (open_subspace_cover_set j),
    forall j, exists2 C, compact C & open_subspace_cover_set j `<=` C &
    forall y : Y, exists j, open_subspace_cover_set j y].
Proof.
split.
- move=> j; case: (pselect (exists C : set T, [/\ compact C, U j `<=` C & C `<=` S]))=> hP.
  + have -> : open_subspace_cover_set j = set_val @^-1` U j by apply/seteqP; split=> y //= [].
    apply: open_comp; last exact: (countable_base_open hU j).
    by move=> x _; exact: set_type_val_continuous.
  + have -> : open_subspace_cover_set j = set0 by apply/seteqP; split=> y //= [_ h]; exact: hP.
    exact: open0.
- move=> j; case: (pselect (exists C : set T, [/\ compact C, U j `<=` C & C `<=` S]))=> hP.
  + have [C [hC hUC hCS]] := hP.
    exists (set_val @^-1` C); first exact: set_type_compact_preimage.
    by move=> y [hy _]; exact: hUC.
  + exists set0; first exact: compact0.
    by move=> y [_ h]; exact: hP.
- move=> y; have [C [hC hCc hCcl hCS]] := open_compact_neighbourhood (set_valP y).
  have [j [hj hjC]] := countable_base_refines hU (@open_interior _ C) hC.
  exists j; split=> //; exists C; split=> //.
  by move=> x hx; exact: interior_subset (hjC x hx).
Qed.

End CompactNeighbourhoods.

Section OpenSubspaceMeasure.
Variable R : realType.
Variable T : pseudoMetricType R.
Hypothesis hT : hausdorff_space T.
Hypothesis hl : locally_compact [set: T].
Variable U : nat -> set T.
Hypothesis hU : is_countable_open_base U.
Variable S : set T.
Hypothesis hS : open S.
Local Notation Y := (set_type S).
Local Notation KT := (@compactly_supported_continuous_functions R T).
Local Notation KY := (@compactly_supported_continuous_functions R Y).

(** Source for [open_subspace_measure_is_measure]: the restriction of a
    measure phi over T to subsets of S is a measure over S, Federer
    2.1.2, p. 54, by the countable covering law; supporting 2.7.16,
    pp. 136–137. Supporting lemma. *)
Lemma open_subspace_measure_is_measure (phi : set T -> \bar R) :
  is_measure phi -> is_measure (open_subspace_measure (S := S) phi).
Proof.
move=> hm; split; first by move=> A; exact: (measure_nonnegative hm).
move=> A F hF hc.
apply: (measure_indexed_cover hm (D := F) (F := fun B : set Y => set_val @` B) hF).
move=> _ [y hy <-]; have [B hB hyB] := hc y hy.
by exists B=> //; exists y.
Qed.

(** Source for [open_subspace_measure_pushforward]: the image of the
    restriction of phi to S under the inclusion of S is phi L S, Federer
    2.1.2, p. 54; supporting 2.7.16, pp. 136–137. Supporting lemma. *)
Lemma open_subspace_measure_pushforward (phi : set T -> \bar R) :
  measure_pushforward (set_val : Y -> T) (open_subspace_measure phi) = measure_restrict phi S.
Proof.
apply: funext=> B; rewrite /measure_pushforward /open_subspace_measure /measure_restrict.
congr phi; apply/seteqP; split.
- by move=> _ [y hy <-]; split=> //; exact: set_valP.
- by move=> x [hxS hxB]; exists (exist _ x (mem_set hxS)).
Qed.

(** Source for [open_subspace_preimage_measurable]: the trace on S of a
    phi measurable set is measurable for the restriction of phi to S,
    Federer 2.1.2, p. 54. Supporting lemma. *)
Lemma open_subspace_preimage_measurable (phi : set T -> \bar R) (M : set T) :
  measure_measurable phi M -> measure_measurable (open_subspace_measure (S := S) phi) (set_val @^-1` M).
Proof.
move=> hM A; rewrite /open_subspace_measure (hM (set_val @` A)).
have h1 : set_val @` (A `&` set_val @^-1` M) = (set_val @` A) `&` M.
  apply/seteqP; split.
  - by move=> y [x [hxA hxM] <-]; split=> //; exists x.
  - by move=> y [[x hxA hxy] hyM]; exists x=> //; split=> //; rewrite /= hxy.
have h2 : set_val @` (A `\` set_val @^-1` M) = (set_val @` A) `\` M.
  apply/seteqP; split.
  - by move=> y [x [hxA hxM] <-]; split=> //; exists x.
  - by move=> y [[x hxA hxy] hyM]; exists x=> //; split=> //; rewrite /= hxy.
by rewrite h1 h2.
Qed.

(** Source for [open_subspace_borel_regular]: the restriction to S of a
    Borel regular measure is Borel regular, Federer 2.2.3, p. 61: open
    subsets of S are traces of open subsets of T, and the trace of a
    Borel hull of T' in T is a Borel hull of T' in S. Supporting
    lemma. *)
Lemma open_subspace_borel_regular (phi : set T -> \bar R) :
  is_measure phi -> is_borel_regular_measure phi ->
  is_borel_regular_measure (open_subspace_measure (S := S) phi).
Proof.
move=> hm hbr.
have hmY := open_subspace_measure_is_measure hm.
split.
- move=> W [O hO <-]; apply: open_subspace_preimage_measurable.
  exact: (borel_regular_borel_measurable hm hbr (open_borel_set hO)).
- move=> A; have [B' [hAB [hB hAe]]] := borel_regular_cover hbr (set_val @` A).
  exists (set_val @^-1` B'); split; [|split].
  + by move=> x hx; apply: hAB; exists x.
  + apply: (@continuous_borel_preimage Y T set_val); last exact: hB.
    exact: set_type_val_continuous.
  + apply/eqP; rewrite eq_le; apply/andP; split.
    * apply: (measure_mono hmY)=> x hx; apply: hAB; by exists x.
    * rewrite /open_subspace_measure hAe; apply: (measure_mono hm).
      by move=> _ [x hx <-].
Qed.

(** Source for [open_subspace_measure_represents]: the restriction of
    phi to S represents nu(u) = int u' dphi on K(S): by 2.4.18, p. 90,
    int u d(phi over S) = int u' d(phi L S), and by 2.4.10, p. 85, and
    2.5.10, p. 101, int u' d(phi L S) = int u' dphi, since u' vanishes
    outside the phi measurable set S; supporting Federer 2.7.16,
    pp. 136–137. Supporting lemma. *)
Lemma open_subspace_measure_represents (phi : set T -> \bar R) (mu : (T -> R) -> R) :
  is_measure phi -> is_borel_regular_measure phi -> is_real_integral_functional phi KT mu ->
  is_real_integral_functional (open_subspace_measure (S := S) phi) KY (open_restricted_integral mu).
Proof.
move=> hm hbr hA u hu.
have hue := open_extension_compact hT hS hu.
have hI := hA _ hue.
have hSm : measure_measurable phi S := borel_regular_borel_measurable hm hbr (open_borel_set hS).
have hZ : is_measure_integral phi
    (partial_function_zero_extension (0 : extended_real_line R) S (real_total_integrand (open_extension u)))
    (mu (open_extension u))%:E.
  apply: (measure_integral_graph_equivalent _ hI)=> x y.
  rewrite partial_function_zero_extension_graph real_total_integrand_graph.
  split.
  - move=> h; case: (pselect (S x))=> hx.
      by left; split=> //; exact/real_total_integrand_graph.
    by right; split=> //; rewrite -h open_extension_out.
  - case=> [[_ /real_total_integrand_graph] //|[hx ->]].
    by rewrite open_extension_out.
have hR := (restricted_integral_zero_extension_iff hm (real_total_integrand (open_extension u))
  (mu (open_extension u))%:E hSm).2 hZ.
rewrite -open_subspace_measure_pushforward in hR.
have hmY := open_subspace_measure_is_measure hm.
have hinj : injective (set_val : Y -> T) by move=> a b h; apply: val_inj.
have hmeas : is_measure_measurable_function (open_subspace_measure (S := S) phi)
    (partial_function_precompose set_val (real_total_integrand (open_extension u))).
  exact: measurable_function_pushforward_precompose hinj hR.1.
have hP := (measure_pushforward_integral_iff hmY hmeas _).2 hR.
apply: (measure_integral_graph_equivalent _ hP)=> x y.
have he : open_extension u \o set_val = u by apply: funext=> z; exact: open_extensionE.
by rewrite (precompose_total_integrand_graph set_val (open_extension u) x y) he.
Qed.

(** Source for [open_subspace_measure_associated]: the restriction of
    phi to the open set S is the K(S) regular measure associated with
    the monotone Daniell integral nu(u) = int u' dphi on K(S), and it is
    a Radon measure; this is the identification behind "phi is a left
    |det|^{-n} covariant measure over G" and "gamma ... over G", Federer
    2.7.16, pp. 136–137, with 2.5.3, p. 94, and 2.5.14, p. 107.
    Supporting theorem: the K(S) regular measure psi representing nu is
    a Radon measure, hence Borel regular, and two Borel regular measures
    representing nu coincide (RepresentingMeasureComparison.v); every K(S)
    regular measure representing nu equals the restriction. *)
Theorem open_subspace_measure_associated (phi : set T -> \bar R) (mu : (T -> R) -> R) :
  is_measure phi -> is_real_integral_functional phi KT mu -> is_function_lattice_regular KT phi ->
  is_monotone_daniell_integral KT mu ->
  [/\ is_monotone_daniell_integral KY (open_restricted_integral mu),
    is_measure (open_subspace_measure (S := S) phi),
    is_real_integral_functional (open_subspace_measure (S := S) phi) KY (open_restricted_integral mu),
    is_function_lattice_regular KY (open_subspace_measure (S := S) phi) &
    is_radon_measure (open_subspace_measure (S := S) phi) /\
    forall psi, is_measure psi -> is_real_integral_functional psi KY (open_restricted_integral mu) ->
      is_function_lattice_regular KY psi -> psi = open_subspace_measure (S := S) phi].
Proof.
move=> hm hA hr hmu.
have hrad := compact_support_regular_countable_base_radon hm hA hr hT hl hU.
have hbr := radon_borel_regular hm hrad.
have hL := @compactly_supported_continuous_functions_lattice R Y.
have hne : exists f, KY f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have hnu := open_restricted_monotone hT hS hmu.
have [psi [hpsi [hpsiA [hpsir _]]]] := monotone_daniell_regular_representation hL hnu hne.
have hUY := open_subspace_countable_open_base S hU.
have hHY : hausdorff_space Y := set_type_hausdorff hT.
have hlY := pseudometric_open_subspace_locally_compact hl hS.
have hradY := compact_support_regular_countable_base_radon hpsi hpsiA hpsir hHY hlY hUY.
have hpb := radon_borel_regular hpsi hradY.
have [hWo hWc hWT] := open_subspace_compact_cover hl hS hU.
have hmY := open_subspace_measure_is_measure hm.
have hAY := open_subspace_measure_represents hm hbr hA.
have he := represented_borel_regular_scaled hHY hlY hUY hWo hWc hWT hmY hpsi
  (open_subspace_borel_regular hm hbr) hpb hAY hpsiA ltr01 (fun f _ => esym (mul1r _)).
have hpe : open_subspace_measure (S := S) phi = psi by apply: funext=> A; rewrite he mul1e.
split=> //; first by rewrite hpe.
split; first by rewrite hpe.
move=> psi' hpsi' hA' hr'; apply: funext=> A; rewrite hpe.
exact: (function_lattice_regular_representation_unique hL hpsi' hpsi hA' hpsiA hr' hpsir A).
Qed.

(** Source for [open_subspace_covariant_measure]: if the integral
    nu(u) = int u' dphi over the open set S satisfies
    nu(u o A_g) = chi(g) nu(u), then the restriction of phi to S is a
    chi covariant measure in the sense of Federer 2.7.1, p. 122;
    supporting "phi is a left |det|^{-n} covariant measure over G" and
    "gamma ... right Delta_G chi^{-1} covariant over G", 2.7.16,
    pp. 136–137. Supporting theorem. *)
Theorem open_subspace_covariant_measure (G : Type) (A : G -> Y -> Y) (chi : G -> R)
    (phi : set T -> \bar R) (mu : (T -> R) -> R) :
  is_measure phi -> is_real_integral_functional phi KT mu -> is_function_lattice_regular KT phi ->
  is_monotone_daniell_integral KT mu -> is_covariant_on KY A chi (open_restricted_integral mu) ->
  is_covariant_measure A chi (open_subspace_measure (S := S) phi).
Proof.
move=> hm hA hr hmu hcov.
have [hnu hmY hAY hrY _] := open_subspace_measure_associated hm hA hr hmu.
by exists (open_restricted_integral mu); split.
Qed.

End OpenSubspaceMeasure.

Arguments open_subspace_measure {R T S} phi A.
