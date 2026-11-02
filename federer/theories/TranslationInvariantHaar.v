(** Federer (1969), 2.7.16, pp. 134–135: "If z in R^n and T a subset of R^n,
    then f_#(L^n)[z + T] = ... = f_#(L^n)[T]; thus f_#(L^n) is a Haar
    measure of R^n". This module proves the general principle used in that
    sentence, and the uniqueness statement of example (1), for a commutative
    locally compact Hausdorff metric group G with a countable base which is
    covered by countably many open sets with compact closure (R and R^n are
    the cases of 2.7.16). Let phi be a Borel regular measure over G, finite
    on compact sets and invariant under all translations. Every member of
    K(G) is phi summable, and u |-> int u dphi is a monotone Daniell
    integral on K(G) (2.5.1, p. 92) which is invariant by the image-measure
    formula 2.4.18, p. 90, as used in 2.5.19, p. 113. phi is K(G) regular,
    because it coincides with the K(G) regular measure associated with that
    integral (2.5.3, p. 94, and RepresentingMeasureComparison.v). If phi is
    positive on some compact set, phi is therefore a left and right Haar
    measure in the sense of 2.7.2, p. 122. By 2.7.7, p. 125, every left or
    right Haar measure is c phi with 0 < c < oo. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP
  FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactCutoffUP CompactCutoff FunctionLatticeRegularityUP
  RealIntegralFunctionalUP RealIntegralFunctional MeasureUP MeasureBasic MeasurePushforward
  TopologicalBorel BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity CountableOpenBaseUP
  CompactSupportCountableRadon RegularDaniellRepresentation CharacteristicFunctionUP
  CharacteristicFunctionSealed MeasureCharacteristicIntegral MeasureIntegralComparison
  RealTotalCharacteristicBounds SummableRealFunctionUP MeasureIntegralUP ProperMapUP
  DaniellSpacePushforward EquivariantPushforward CovariantIntegralUP HaarIntegralUP
  HaarIntegralUniqueness CompactSupportSummability RepresentingMeasureComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_invariant_borel_measure]: the hypotheses on f_#(L^n)
    verified in Federer 2.7.16, p. 135, before "thus f_#(L^n) is a Haar
    measure": a Borel regular measure (2.2.3, p. 61), finite on compact
    sets, with phi[z + T] = phi[T] for every translation. Definition by
    these laws; the invariance is phi(tau_z^{-1}(T)) = phi(T). *)
Record is_invariant_borel_measure (R : realType) (G : topologicalType) (add : G -> G -> G)
    (phi : set G -> \bar R) : Prop := {
  (** Source for [invariant_borel_measure_law]: phi is a measure,
      Federer 2.1.2, p. 53. *)
  invariant_borel_measure_law : is_measure phi;
  (** Source for [invariant_borel_regular_law]: phi is Borel regular,
      Federer 2.2.3, p. 61. *)
  invariant_borel_regular_law : is_borel_regular_measure phi;
  (** Source for [invariant_borel_compact_finite_law]: compact sets
      have finite measure, Federer 2.2.5, p. 62. *)
  invariant_borel_compact_finite_law : forall C, compact C -> phi C < +oo;
  (** Source for [invariant_borel_translation_law]: "phi[z + T] =
      phi[T]", Federer 2.7.16, p. 135, as tau_z#(phi) = phi. *)
  invariant_borel_translation_law : forall z, measure_pushforward (add z) phi = phi
}.

Section InvariantHaar.
Variable R : realType.
Variable G : pseudoMetricType R.
Variables (add : G -> G -> G) (neg : G -> G) (zero : G).
Hypothesis hG : is_locally_compact_hausdorff_group add neg zero.
Hypothesis hcomm : forall x y, add x y = add y x.
Variable U : nat -> set G.
Hypothesis hU : is_countable_open_base U.
Variable W : nat -> set G.
Hypothesis hWo : forall k, open (W k).
Hypothesis hWc : forall k, exists2 C, compact C & W k `<=` C.
Hypothesis hWT : forall x, exists k, W k x.
Local Notation K := (@compactly_supported_continuous_functions R G).

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121. *)
Let hT := lch_group_topological hG.
(** Source for [hGl]: the group laws of G, Federer 2.7.1, p. 121. *)
Let hGl := topological_group_laws hT.
(** Source for [hH]: G is Hausdorff, Federer 2.7.1, p. 121. *)
Let hH := lch_group_hausdorff hG.
(** Source for [hlc]: G is locally compact, Federer 2.7.1, p. 121. *)
Let hlc := lch_group_locally_compact hG.

(** Source for [invariant_borel_summable]: supporting lemma for Federer
    2.7.16, p. 135: every member of K(G) is summable for an invariant
    Borel measure, by 2.5.13, p. 106. *)
Lemma invariant_borel_summable (phi : set G -> \bar R) :
  is_invariant_borel_measure add phi -> K `<=` summable_real_functions phi.
Proof.
move=> [hm hr hc _] u hu.
apply: (compactly_supported_summable hm _ hc hu).
exact: borel_regular_borel_measurable hm hr.
Qed.

(** Source for [invariant_borel_integral]: the integral u |-> int u dphi
    on K(G), Federer 2.5.1, p. 92, for an invariant Borel measure phi,
    supporting 2.7.16, p. 135. Definition through the sealed integral map
    of RealIntegralFunctional.v. *)
Definition invariant_borel_integral (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi) :=
  lattice_measure_integral (invariant_borel_summable h).

(** Source for [invariant_borel_integral_represents]: phi represents
    its integral on K(G), Federer 2.5.1, p. 92. Supporting lemma. *)
Lemma invariant_borel_integral_represents (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi) :
  is_real_integral_functional phi K (invariant_borel_integral h).
Proof. exact: lattice_measure_integral_specification. Qed.

(** Source for [invariant_borel_integral_monotone]: the integral is a
    monotone Daniell integral on K(G), Federer 2.5.1, p. 92. Supporting
    lemma. *)
Lemma invariant_borel_integral_monotone (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi) :
  is_monotone_daniell_integral K (invariant_borel_integral h).
Proof.
exact: (@summable_sublattice_integral_laws R G phi (invariant_borel_measure_law h) K
  (invariant_borel_summable h) (@compactly_supported_continuous_functions_lattice R G)).
Qed.

(** Source for [translation_proper]: translations are proper continuous
    maps, as required for the image measures of Federer 2.5.19, p. 113.
    Supporting lemma. *)
Lemma translation_proper (z : G) : continuous (add z) /\ is_proper_map (add z).
Proof.
split; first exact: left_translation_continuous hT z.
exact: homeomorphism_with_inverse_proper (left_translation_homeomorphism hT z).
Qed.

(** Source for [invariant_borel_integral_translation]: Federer 2.7.16,
    p. 135, invariance of the integral: int u(z + x) dphi x = int u dphi
    whenever u in K(G), by 2.4.18, p. 90, and tau_z#(phi) = phi.
    Supporting lemma. *)
Lemma invariant_borel_integral_translation (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (u : G -> R) (z : G) :
  K u -> invariant_borel_integral h (u \o add z) = invariant_borel_integral h u.
Proof.
move=> hu; have [hzc hzp] := translation_proper z.
have hp := daniell_pushforward_integral hzc hzp (invariant_borel_measure_law h)
  (invariant_borel_integral_represents h).
rewrite (invariant_borel_translation_law h z) in hp.
exact: real_integral_functional_unique_on_lattice hp (invariant_borel_integral_represents h) u hu.
Qed.

(** Source for [invariant_borel_integral_left_invariant]: the integral
    of phi is a left invariant integral in the sense of Federer 2.7.2,
    p. 122, supporting 2.7.16, p. 135. *)
Lemma invariant_borel_integral_left_invariant (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi) :
  is_left_invariant_integral add (invariant_borel_integral h).
Proof.
constructor; first exact: monotone_daniell_integral_is_daniell (invariant_borel_integral_monotone h).
move=> u g hu; rewrite GRing.mul1r; exact: invariant_borel_integral_translation.
Qed.

(** Source for [right_left_translation]: for a commutative group the
    right multiplication action of Federer 2.7.2, p. 122, A(g,x) =
    x g^{-1}, is translation by g^{-1}. Supporting lemma. *)
Lemma right_left_translation (g : G) :
  right_multiplication_action add neg g = add (neg g).
Proof. by apply: funext=> x; rewrite /right_multiplication_action hcomm. Qed.

(** Source for [invariant_borel_integral_right_invariant]: the integral
    of phi is a right invariant integral, Federer 2.7.2, p. 122, for the
    commutative groups of 2.7.16, p. 134. Supporting lemma. *)
Lemma invariant_borel_integral_right_invariant (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi) :
  is_right_invariant_integral add neg (invariant_borel_integral h).
Proof.
constructor; first exact: monotone_daniell_integral_is_daniell (invariant_borel_integral_monotone h).
move=> u g hu; rewrite GRing.mul1r right_left_translation; exact: invariant_borel_integral_translation.
Qed.

(** Source for [invariant_borel_function_lattice_regular]: Federer
    2.7.16, p. 135, an invariant Borel measure is the K(G) regular
    measure associated with its integral: the regular measure of 2.5.3,
    p. 94, is Radon by 2.5.14, p. 107, hence Borel regular, and it
    coincides with phi by RepresentingMeasureComparison.v. Supporting
    theorem. *)
Theorem invariant_borel_function_lattice_regular (phi : set G -> \bar R)
    (h : is_invariant_borel_measure add phi) : is_function_lattice_regular K phi.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R G.
have hne : exists f, K f by exists (fun _ => 0%R); exact: compactly_supported_zero_function.
have [psi [hpsi [hpsiA [hpsir _]]]] :=
  monotone_daniell_regular_representation hL (invariant_borel_integral_monotone h) hne.
have hrad := compact_support_regular_countable_base_radon hpsi hpsiA hpsir hH hlc hU.
have hpb := radon_borel_regular hpsi hrad.
have he := represented_borel_regular_scaled hH hlc hU hWo hWc hWT (invariant_borel_measure_law h) hpsi
  (invariant_borel_regular_law h) hpb (invariant_borel_integral_represents h) hpsiA ltr01
  (fun f _ => esym (GRing.mul1r _)).
have -> : phi = psi by apply: funext=> S; rewrite he mul1e.
exact: hpsir.
Qed.

(** Source for [invariant_borel_integral_nonzero]: supporting lemma for
    Federer 2.7.16, p. 135: if phi(C) > 0 for a compact set C, the
    integral of phi does not vanish on K(G), since a cutoff u of C has
    int u dphi >= phi(C), 2.5.13, p. 106. *)
Lemma invariant_borel_integral_nonzero (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (C : set G) : compact C -> 0 < phi C ->
  exists2 u, K u & invariant_borel_integral h u <> 0%R.
Proof.
move=> hC hpos.
pose u := @compact_cutoff R G C hH hlc hC.
have hu := @compact_cutoff_specification R G C hH hlc hC.
exists u; first exact: compact_cutoff_function hu.
have hm := invariant_borel_measure_law h.
have hCm : measure_measurable phi C.
  apply: (borel_regular_borel_measurable hm (invariant_borel_regular_law h)).
  exact: closed_borel_set (compact_closed hH hC).
pose s := @CharacteristicFunction.value R G C.
have hs : is_characteristic_function C s := @CharacteristicFunction.laws R G C.
have hsi := @measure_characteristic_integral R G phi hm C s hs hCm.
have hui := invariant_borel_integral_represents h (compact_cutoff_function hu).
have hle : phi C <= (invariant_borel_integral h u)%:E.
  apply: (measure_integral_monotone hm hsi hui).
  apply: (real_total_pointwise_order_almost hm)=> x.
  case: (pselect (C x))=> hx.
  - by rewrite (characteristic_on_set hs hx) (compact_cutoff_on_set hu hx).
  - by rewrite (characteristic_off_set hs hx); exact: (andP (compact_cutoff_range hu x)).1.
move=> h0; move: hle; rewrite h0 leNgt; by rewrite hpos.
Qed.

(** Source for [invariant_borel_left_haar]: Federer 2.7.16, p. 135,
    "thus f_#(L^n) is a Haar measure": an invariant Borel measure that is
    positive on some compact set is a left Haar measure of G in the sense
    of 2.7.2, p. 122. Direct formalisation of the general principle. *)
Theorem invariant_borel_left_haar (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (C : set G) : compact C -> 0 < phi C -> is_left_haar_measure add phi.
Proof.
move=> hC hpos; exists (invariant_borel_integral h); split.
- split.
  + exact: invariant_borel_integral_left_invariant.
  + exact: invariant_borel_integral_monotone.
  + exact: invariant_borel_integral_nonzero hC hpos.
- exact: invariant_borel_measure_law h.
- exact: invariant_borel_integral_represents.
- exact: invariant_borel_function_lattice_regular.
Qed.

(** Source for [invariant_borel_right_haar]: Federer 2.7.16, p. 134,
    "(left and right) Haar measure": for the commutative groups of
    2.7.16 the same measure is a right Haar measure, 2.7.2, p. 122.
    Direct formalisation. *)
Theorem invariant_borel_right_haar (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (C : set G) : compact C -> 0 < phi C -> is_right_haar_measure add neg phi.
Proof.
move=> hC hpos; exists (invariant_borel_integral h); split.
- split.
  + exact: invariant_borel_integral_right_invariant.
  + exact: invariant_borel_integral_monotone.
  + exact: invariant_borel_integral_nonzero hC hpos.
- exact: invariant_borel_measure_law h.
- exact: invariant_borel_integral_represents.
- exact: invariant_borel_function_lattice_regular.
Qed.

(** Source for [haar_measure_borel_regular]: supporting lemma for
    Federer 2.7.16, p. 134: a K(G) regular measure representing a
    monotone Daniell integral on K(G) is Radon by 2.5.14, p. 107, since G
    has a countable base, hence Borel regular (2.2.5, p. 62). *)
Lemma haar_measure_borel_regular (psi : set G -> \bar R) (J : (G -> R) -> R) :
  is_measure psi -> is_real_integral_functional psi K J -> is_function_lattice_regular K psi ->
  is_borel_regular_measure psi.
Proof.
move=> hm hJ hr.
have hrad := compact_support_regular_countable_base_radon hm hJ hr hH hlc hU.
exact: radon_borel_regular hm hrad.
Qed.

(** Source for [right_haar_integral_left]: for a commutative group a
    right Haar integral is a left Haar integral, Federer 2.7.2, p. 122,
    since A(g,x) = x g^{-1} = g^{-1} x. Supporting lemma. *)
Lemma right_haar_integral_left (J : (G -> R) -> R) :
  is_right_haar_integral add neg J -> is_left_haar_integral add J.
Proof.
move=> [[hd hlaw] hmon hnz]; split=> //; split=> // u g hu.
have he : u \o left_multiplication_action add g = u \o right_multiplication_action add neg (neg g).
  by rewrite right_left_translation (group_invK hGl).
by rewrite he; exact: hlaw.
Qed.

(** Source for [left_haar_measure_multiple]: Federer 2.7.16, p. 134,
    "the unique (left and right) Haar measure" up to the normalisation:
    every left Haar measure psi of G is c phi with 0 < c < oo, by
    2.7.7, p. 125, and the comparison of RepresentingMeasureComparison.v.
    Direct formalisation of the uniqueness. *)
Theorem left_haar_measure_multiple (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (C : set G) (psi : set G -> \bar R) : compact C -> 0 < phi C ->
  is_left_haar_measure add psi -> exists2 c : R, (0 < c)%R & forall S, psi S = c%:E * phi S.
Proof.
move=> hC hpos [J [hJ hpsim hpsiJ hpsir]].
have hI : is_left_haar_integral add (invariant_borel_integral h).
  split.
  - exact: invariant_borel_integral_left_invariant.
  - exact: invariant_borel_integral_monotone.
  - exact: invariant_borel_integral_nonzero hC hpos.
have [c hc hJI] := left_haar_integral_unique hG hJ hI.
exists c=> //.
exact: (represented_borel_regular_scaled hH hlc hU hWo hWc hWT hpsim (invariant_borel_measure_law h)
  (haar_measure_borel_regular hpsim hpsiJ hpsir) (invariant_borel_regular_law h) hpsiJ
  (invariant_borel_integral_represents h) hc hJI).
Qed.

(** Source for [right_haar_measure_multiple]: Federer 2.7.16, p. 134,
    the right half of "(left and right) Haar measure": every right Haar
    measure of the commutative group G is c phi with 0 < c < oo.
    Direct formalisation. *)
Theorem right_haar_measure_multiple (phi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (C : set G) (psi : set G -> \bar R) : compact C -> 0 < phi C ->
  is_right_haar_measure add neg psi -> exists2 c : R, (0 < c)%R & forall S, psi S = c%:E * phi S.
Proof.
move=> hC hpos [J [hJ hpsim hpsiJ hpsir]].
apply: (left_haar_measure_multiple h hC hpos).
by exists J; split=> //; exact: right_haar_integral_left.
Qed.

(** Source for [invariant_borel_multiple]: Federer 2.7.16, p. 135,
    "f_#(L^n) is a Haar measure of R^n, hence f_#(L^n) = chi(f) L^n with
    chi(f) > 0": an invariant Borel measure psi which is positive on some
    compact set is c phi with 0 < c < oo. Direct formalisation of the
    general step. *)
Theorem invariant_borel_multiple (phi psi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (hpsi : is_invariant_borel_measure add psi) (C D : set G) :
  compact C -> 0 < phi C -> compact D -> 0 < psi D ->
  exists2 c : R, (0 < c)%R & forall S, psi S = c%:E * phi S.
Proof.
move=> hC hpos hD hposD.
have hl := invariant_borel_left_haar hpsi hD hposD.
exact: (left_haar_measure_multiple h hC hpos hl).
Qed.

(** Source for [invariant_borel_integral_multiple]: Federer 2.7.16,
    p. 135, "f_#(L^n) = chi(f) L^n with chi(f) > 0", together with the
    corresponding identity of integrals: for invariant Borel measures
    phi and psi positive on compact sets there is c > 0 with
    int u dpsi = c int u dphi for u in K(G) and psi = c phi, by 2.7.7,
    p. 125. Supporting theorem. *)
Theorem invariant_borel_integral_multiple (phi psi : set G -> \bar R) (h : is_invariant_borel_measure add phi)
    (hpsi : is_invariant_borel_measure add psi) (C D : set G) :
  compact C -> 0 < phi C -> compact D -> 0 < psi D ->
  exists c : R, [/\ (0 < c)%R,
    forall u, K u -> invariant_borel_integral hpsi u = (c * invariant_borel_integral h u)%R &
    forall S, psi S = c%:E * phi S].
Proof.
move=> hC hpos hD hposD.
have hI : is_left_haar_integral add (invariant_borel_integral h).
  split.
  - exact: invariant_borel_integral_left_invariant.
  - exact: invariant_borel_integral_monotone.
  - exact: invariant_borel_integral_nonzero hC hpos.
have hJ : is_left_haar_integral add (invariant_borel_integral hpsi).
  split.
  - exact: invariant_borel_integral_left_invariant.
  - exact: invariant_borel_integral_monotone.
  - exact: invariant_borel_integral_nonzero hD hposD.
have [c hc hJI] := left_haar_integral_unique hG hJ hI.
exists c; split=> //.
exact: (represented_borel_regular_scaled hH hlc hU hWo hWc hWT (invariant_borel_measure_law hpsi)
  (invariant_borel_measure_law h) (invariant_borel_regular_law hpsi) (invariant_borel_regular_law h)
  (invariant_borel_integral_represents hpsi) (invariant_borel_integral_represents h) hc hJI).
Qed.

End InvariantHaar.
