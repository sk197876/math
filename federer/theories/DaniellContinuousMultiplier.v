(** Federer (1969), 2.7.9, printed p. 127: "To verify (1) we define sigma(u)
    = nu(u chi) whenever u in K(G)". Federer uses without comment that sigma
    is a Daniell integral on K(G), as is needed for the variations sigma+
    and sigma- of 2.5.5, p. 96. This file proves the general fact: if X is a
    locally compact Hausdorff space, nu is a Daniell integral on K(X) and f:
    X -> R is continuous, then u |-> nu(u f) is a Daniell integral on K(X).
    The functional is linear because nu is linear on K(X) (2.5.13, p. 106)
    and u f belongs to K(X). For u in K(X)+ and k in K(X) with 0 <= k <= u,
    the function k f vanishes outside spt u and |k f| <= |u f| <= M, where M
    bounds |u f|; the bound of 2.5.13 for Daniell integrals on functions
    vanishing outside the compact set spt u
    (compact_daniell_fixed_support_bound) gives nu(k f) <= (M + 1) C. Hence
    the functional is bounded above on the positive order intervals and is a
    Daniell integral by the first assertion of 2.5.13
    (compact_support_order_bounded_daniell). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeSeminormUP
  DaniellIntegralUP CompactSupportFunctionUP CompactSupportProducts CompactSupportUniformBound
  CompactDaniellUniformBound DaniellSpaceCompactness CompactSupportRieszRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ContinuousMultiplier.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hX : hausdorff_space X.
Hypothesis hlX : locally_compact [set: X].
Local Notation K := (@compactly_supported_continuous_functions R X).
Variable nu : (X -> R) -> R.
Hypothesis hnu : is_daniell_integral K nu.
Variable f : X -> R.
Hypothesis hf : continuous (f : X -> real_line_metric R).

(** Source for [continuous_multiplier_member]: u f belongs to K(X)
    whenever u in K(X), as presupposed by "sigma(u) = nu(u chi) whenever
    u in K(G)", Federer 2.7.9, p. 127. Supporting lemma. *)
Lemma continuous_multiplier_member u : K u -> K (fun x => u x * f x).
Proof.
move=> hu; have h := compact_support_continuous_multiplier hf hu.
have -> : (fun x => u x * f x) = (fun x => f x * u x) by apply: funext=> x; exact: mulrC.
exact: h.
Qed.

(** Source for [continuous_multiplier_linear]: u |-> nu(u f) is linear
    on K(X), supporting "sigma(u) = nu(u chi)", Federer 2.7.9, p. 127,
    by the linearity of Daniell integrals on K(X), 2.5.13, p. 106. *)
Lemma continuous_multiplier_linear :
  is_linear_functional_on_functions K (fun u => nu (fun x => u x * f x)).
Proof.
have hlin := daniell_compact_support_linear hnu.
split.
- move=> u v hu hv /=.
  have -> : (fun x => (u x + v x) * f x) = (fun x => u x * f x + v x * f x).
    by apply: funext=> x; exact: mulrDl.
  exact: hlin.1 _ _ (continuous_multiplier_member hu) (continuous_multiplier_member hv).
- move=> c u hu /=.
  have -> : (fun x => c * u x * f x) = (fun x => c * (u x * f x)).
    by apply: funext=> x; rewrite mulrA.
  exact: hlin.2 c _ (continuous_multiplier_member hu).
Qed.

(** Source for [continuous_multiplier_order_bounded]: u |-> nu(u f)
    is bounded above on every positive order interval of K(X), the third
    hypothesis of Federer 2.5.5, p. 96, supporting "sigma(u) =
    nu(u chi)", 2.7.9, p. 127. The bound comes from 2.5.13, p. 107, for
    functions vanishing outside spt u. *)
Lemma continuous_multiplier_order_bounded u : positive_function_lattice K u ->
  exists b, forall k, lattice_positive_order_interval K u k -> nu (fun x => k x * f x) <= b.
Proof.
move=> [hu hu0].
have [C [hC hb]] := compact_daniell_fixed_support_bound hX hlX hu.2 hnu.
have [M [hM hMb]] := compact_support_uniform_bound (continuous_multiplier_member hu).
exists ((M + 1) * C)=> k [hk [hk0 hku]].
have hM1 : 0 < M + 1 by rewrite ltr_wpDl.
have hz x : ~ real_function_support u x -> k x * f x = 0.
  move=> hx; have hux := real_function_zero_off_support hx.
  have hkx : k x = 0 by apply/eqP; rewrite eq_le hk0 andbT -hux; exact: hku x.
  by rewrite hkx mul0r.
have hbd x : real_function_support u x -> `|k x * f x| <= M + 1.
  move=> _.
  have h1 : `|k x * f x| <= `|u x * f x|.
    rewrite !normrM ler_wpM2r ?normr_ge0 //.
    by rewrite (ger0_norm (hk0 x)) (ger0_norm (hu0 x)); exact: hku x.
  have h2 : `|u x * f x| <= M + 1 by apply: le_trans (hMb x) _; rewrite lerDl; exact: ler01.
  exact: le_trans h1 h2.
have h := hb _ (continuous_multiplier_member hk) hz (M + 1) hM1 hbd.
exact: le_trans (ler_norm _) h.
Qed.

(** Source for [continuous_multiplier_daniell]: "sigma(u) = nu(u chi)
    whenever u in K(G)" defines a Daniell integral on K(G), Federer
    2.7.9, p. 127, in the general form for a continuous f on a locally
    compact Hausdorff space X. Supporting theorem, by the first
    assertion of 2.5.13, p. 106; Federer does not state it. *)
Theorem continuous_multiplier_daniell : is_daniell_integral K (fun u => nu (fun x => u x * f x)).
Proof.
apply: (compact_support_order_bounded_daniell hX hlX continuous_multiplier_linear).
exact: continuous_multiplier_order_bounded.
Qed.

End ContinuousMultiplier.
