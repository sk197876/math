(** Federer (1969), 2.7.11, printed pp. 128–129, second half of the proof of
    (1): "Next, to prove the other half of (1), we assume Weil's condition
    and use 2.7.9 to choose a left chi covariant and right Delta_G chi^{-1}
    covariant integral lambda on K(G). For any u in K(G) we obtain from
    2.7.10 a w in K(G)+ such that mu^x(w)(g x) = 1 whenever g in spt u, and
    apply 2.7.8(3) in computing lambda_g[w(g) . mu^x(u)(g x)] = mu_s
    lambda_g[w(g) u(g s)] = mu_s(Delta_G(s)^{-1} chi(s) lambda_g[w(g s^{-1})
    u(g)]) = lambda_g(u(g) mu_s[Delta_{G^x}(s^{-1}) w(g s^{-1})]) =
    lambda_g[u(g) . mu^x(w)(g x)] = lambda(u). Therefore ker mu^x subset ker
    lambda, there exists a linear function nu: K(X) -> R with nu o mu^x =
    lambda, and we see from 2.7.10(5), (6) that nu is a chi covariant
    integral." This file proves the part of this argument that follows the
    choice of lambda. The integral lambda is any Daniell integral on K(G)
    which is right psi covariant for a continuous function psi with psi(t) =
    Delta_{G^x}(t) for t in G^x; with Weil's condition, the function psi =
    Delta_G chi^{-1} has this property (WeilCondition.v). The two
    interchanges of mu_s and lambda_g are Fubini's theorem for Daniell
    integrals on K(G x G^x) (compact_daniell_iterations_commute, 2.6.4 and
    2.6.6, pp. 119–120); the functions (g,s) |-> w(g) u(g s) and (g,s) |->
    psi(s^{-1}) w(g s^{-1}) u(g) belong to K(G x G^x) because both vanish
    unless g and s lie in the compact set spt w cup spt u cup {a^{-1} b: a
    in spt w, b in spt u}. The second equation is the right psi covariance
    of lambda applied to g |-> w(g s^{-1}) u(g) and the element s^{-1}; the
    fourth is 2.7.8(3) for mu. The function w is obtained from a cutoff
    function v in K(X) equal to 1 on the compact set A^x(spt u) (2.5.13, p.
    106) and the surjectivity of mu^x (2.7.10); its nonnegativity is not
    needed. The linear function nu is defined by choosing, for each v in
    K(X), some u in K(G) with mu^x(u) = v. "We see from 2.7.10(5), (6) that
    nu is a chi covariant integral": by 2.7.10(5), every k in K(X) with spt
    k subset spt f equals mu^x[((k / mu^x(phi)) o A^x) . phi] for a fixed
    phi in K(G)+ chosen for f, so that the bound of lambda on the positive
    order interval of ((f / mu^x(phi)) o A^x) . phi bounds nu on that of f;
    the order-bounded criterion of 2.5.13, p. 106
    (compact_support_order_bounded_daniell) then shows that nu is a Daniell
    integral, and the covariance follows from 2.7.10(4). The standing
    hypotheses are those of 2.7.1, p. 121: G is a locally compact Hausdorff
    topological group and X a locally compact Hausdorff homogeneous space of
    G. Neither. The local erratum has no entry for pp. 128–129. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground TopologicalProductMaps ProperMapUP
  FunctionLatticeUP FunctionLatticeSeminormUP DaniellIntegralUP MonotoneDaniellIntegralUP DaniellIntegralNegation
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportProducts
  DaniellSpaceCompactness CompactCutoffUP CompactCutoff TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous ModularFunctionUP ModularFunction SubtypeCompactHausdorff IsotropyGroupTopology
  CosetIntegralUP CosetIntegralLaws CompactDaniellIterationCommutation
  CompactSupportRieszRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SubgroupProductSupport.
Variable R : realType.
Variable G : topologicalType.
Variable S : set G.
Hypothesis hH : hausdorff_space G.
Hypothesis hSc : closed S.

(** Source for [subgroup_product_compactly_supported]: membership in
    K(G x G^x) of the integrands (g,s) |-> w(g) u(g s) and
    (g,s) |-> Delta_{G^x}(s^{-1}) w(g s^{-1}) u(g) to which Fubini's
    theorem is applied in Federer 2.7.11, proof, p. 129. Supporting
    lemma: a continuous function h on G x S vanishing unless g and s
    lie in a compact set C of G has compact support, since
    C x (S cap C) is compact and closed. *)
Lemma subgroup_product_compactly_supported (h : G * S -> R) (C : set G) :
  continuous (h : G * S -> real_line_metric R) -> compact C ->
  (forall g (s : S), h (g, s) <> 0 -> C g /\ C (set_val s)) ->
  @compactly_supported_continuous_functions R (G * S)%type h.
Proof.
move=> hc hC hz; split=> //.
have hCc : closed C := compact_closed hH hC.
apply: (@real_function_compact_support_in_closed_set R (G * S)%type _
  (C `*` (set_val @^-1` C : set S))).
- exact: compact_setX hC (set_type_val_proper hSc hC).
- apply: closedI.
  + exact ((continuous_closedP (@fst G S)).1 (@first_projection_continuous G S) _ hCc).
  + have hv : continuous ((@set_val G S) \o (@snd G S)).
      move=> p; apply: continuous_comp; first exact: second_projection_continuous.
      exact: set_type_val_continuous.
    exact ((continuous_closedP _).1 hv _ hCc).
- by case=> g s hn; apply: contrapT=> hh; apply: hn; have [] := hz g s hh.
Qed.

End SubgroupProductSupport.

Section CosetIntegralExchange.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Variable mu : (S -> R) -> R.
Hypothesis hmu : is_left_haar_integral mulS mu.
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.
Variable DS : S -> R.
Hypothesis hDS : is_modular_function mulS invS DS.
Variable lambda : (G -> R) -> R.
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Hypothesis hl : is_daniell_integral KG lambda.
Variable psi : G -> R.
Hypothesis hpsic : continuous (psi : G -> real_line_metric R).
Hypothesis hpsiS : forall t : S, psi (set_val t) = DS t.
Hypothesis hlr : is_covariant_on KG (right_multiplication_action mul inv) psi lambda.

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hG.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hH]: G is Hausdorff, Federer 2.7.1, p. 121. *)
Let hH := lch_group_hausdorff hG.
(** Source for [hlG]: G is locally compact, Federer 2.7.1, p. 121. *)
Let hlG := lch_group_locally_compact hG.
(** Source for [hSc]: G^x is closed in G, Federer 2.7.1, pp. 121–122,
    since X is Hausdorff. *)
Let hSc : closed S := isotropy_subgroup_closed hA hX.
(** Source for [hSG]: G^x is a locally compact Hausdorff topological
    group, as presupposed by "left Haar integral mu of the isotropy
    group G^x", Federer 2.7.10, p. 127. *)
Let hSG := subgroup_restriction_locally_compact_hausdorff hR hG hSc.
(** Source for [hmuD]: mu is a Daniell integral on K(G^x), part of
    "left Haar integral", Federer 2.7.2, p. 122. *)
Let hmuD := monotone_daniell_is_daniell (nonzero_invariant_integral_monotone hmu).
(** Source for [hmuL]: mu is linear on K(G^x), Federer 2.5.13, p. 106. *)
Let hmuL := daniell_compact_support_linear hmuD.
(** Source for [hlL]: lambda is linear on K(G), Federer 2.5.13,
    p. 106. *)
Let hlL := daniell_compact_support_linear hl.

(** Source for [coset_exchange_bound]: the compact set
    spt w cup spt u cup {a^{-1} b: a in spt w, b in spt u} of G outside
    which the integrands of Fubini's theorem in Federer 2.7.11, proof,
    p. 129, vanish. Definition. *)
Definition coset_exchange_bound (u w : G -> R) : set G :=
  real_function_support w `|` real_function_support u `|`
  [set mul (inv p.1) p.2 | p in real_function_support w `*` real_function_support u].

(** Source for [coset_exchange_bound_compact]: the set
    coset_exchange_bound u w is compact for u, w in K(G), supporting the
    use of Fubini's theorem in Federer 2.7.11, proof, p. 129. *)
Lemma coset_exchange_bound_compact u w : KG u -> KG w -> compact (coset_exchange_bound u w).
Proof.
move=> hu hw; apply: compactU; first exact: compactU hw.2 hu.2.
apply: continuous_compact; last exact: compact_setX hw.2 hu.2.
apply: continuous_subspaceT; exact: division_continuous hT.
Qed.

(** Source for [coset_exchange_left_compact]: the function
    (g,s) |-> w(g) u(g s) belongs to K(G x G^x), as presupposed by
    "lambda_g[w(g) . mu^x(u)(g x)] = mu_s lambda_g[w(g) u(g s)]",
    Federer 2.7.11, proof, p. 129. Supporting lemma. *)
Lemma coset_exchange_left_compact u w : KG u -> KG w ->
  @compactly_supported_continuous_functions R (G * S)%type
    (fun p : G * S => w p.1 * u (mul p.1 (set_val p.2))).
Proof.
move=> hu hw.
apply: (subgroup_product_compactly_supported hH hSc _ (coset_exchange_bound_compact hu hw)).
- move=> p; apply: (@continuousM R (G * S)%type).
    exact: continuous_comp (@first_projection_continuous G S p) (hw.1 p.1).
  have hq : continuous (fun q : G * S => mul q.1 (set_val q.2)).
    have -> : (fun q : G * S => mul q.1 (set_val q.2)) =
        (fun r : G * G => mul r.1 r.2) \o (fun q : G * S => (q.1, set_val q.2)).
      by [].
    move=> q; apply: continuous_comp; last exact: (topological_group_mul_continuous hT).
    apply: topological_pair_continuous; first exact: first_projection_continuous.
    move=> r; apply: continuous_comp; first exact: second_projection_continuous.
    exact: set_type_val_continuous.
  exact: continuous_comp (hq p) (hu.1 _).
- move=> g s hn.
  have hwg : w g <> 0 by move=> h0; apply: hn; rewrite h0 mul0r.
  have hug : u (mul g (set_val s)) <> 0 by move=> h0; apply: hn; rewrite h0 mulr0.
  have hsw : real_function_support w g := subset_closure hwg.
  have hsu : real_function_support u (mul g (set_val s)) := subset_closure hug.
  split; first by left; left.
  right; exists (g, mul g (set_val s)); first by split.
  by rewrite /= (group_mulKg hgl).
Qed.

(** Source for [coset_exchange_right_compact]: the function
    (g,s) |-> psi(s^{-1}) w(g s^{-1}) u(g) belongs to K(G x G^x), as
    presupposed by "mu_s(Delta_G(s)^{-1} chi(s) lambda_g[w(g s^{-1})
    u(g)]) = lambda_g(u(g) mu_s[Delta_{G^x}(s^{-1}) w(g s^{-1})])",
    Federer 2.7.11, proof, p. 129. Supporting lemma. *)
Lemma coset_exchange_right_compact u w : KG u -> KG w ->
  @compactly_supported_continuous_functions R (G * S)%type
    (fun p : G * S => psi (inv (set_val p.2)) * (w (mul p.1 (inv (set_val p.2))) * u p.1)).
Proof.
move=> hu hw.
have hic : continuous inv := topological_group_inv_continuous hT.
have hvi : continuous (fun q : G * S => inv (set_val q.2)).
  move=> q; apply: continuous_comp; last exact: hic.
  apply: continuous_comp; first exact: second_projection_continuous.
  exact: set_type_val_continuous.
apply: (subgroup_product_compactly_supported hH hSc _ (coset_exchange_bound_compact hu hw)).
- move=> p; apply: (@continuousM R (G * S)%type).
    by apply: continuous_comp; [exact: hvi|exact: hpsic].
  apply: (@continuousM R (G * S)%type); last first.
    exact: continuous_comp (@first_projection_continuous G S p) (hu.1 p.1).
  have hq : continuous (fun q : G * S => mul q.1 (inv (set_val q.2))).
    have -> : (fun q : G * S => mul q.1 (inv (set_val q.2))) =
        (fun r : G * G => mul r.1 r.2) \o (fun q : G * S => (q.1, inv (set_val q.2))).
      by [].
    move=> q; apply: continuous_comp; last exact: (topological_group_mul_continuous hT).
    by apply: topological_pair_continuous; [exact: first_projection_continuous|exact: hvi].
  exact: continuous_comp (hq p) (hw.1 _).
- move=> g s hn.
  have hug : u g <> 0 by move=> h0; apply: hn; rewrite h0 !mulr0.
  have hwg : w (mul g (inv (set_val s))) <> 0 by move=> h0; apply: hn; rewrite h0 mul0r mulr0.
  have hsu : real_function_support u g := subset_closure hug.
  have hsw : real_function_support w (mul g (inv (set_val s))) := subset_closure hwg.
  split; first by left; right.
  right; exists (mul g (inv (set_val s)), g); first by split.
  by rewrite /= (group_invM hgl) (group_invK hgl) (group_mulgKV hgl).
Qed.

(** Source for [coset_integral_exchange]: the computation
    "lambda_g[w(g) . mu^x(u)(g x)] = mu_s lambda_g[w(g) u(g s)]
    = mu_s(Delta_G(s)^{-1} chi(s) lambda_g[w(g s^{-1}) u(g)])
    = lambda_g(u(g) mu_s[Delta_{G^x}(s^{-1}) w(g s^{-1})])
    = lambda_g[u(g) . mu^x(w)(g x)]", Federer 2.7.11, proof, p. 129,
    for every u, w in K(G) and every Daniell integral lambda on K(G)
    which is right psi covariant, where psi is continuous and
    psi(t) = Delta_{G^x}(t) for t in G^x; with Weil's condition,
    psi = Delta_G chi^{-1}. Direct formalisation; the first and third
    equations are Fubini's theorem, the second is the right psi
    covariance of lambda, and the fourth is 2.7.8(3) for mu. *)
Theorem coset_integral_exchange u w : KG u -> KG w ->
  lambda (fun g => w g * M u (A g x)) = lambda (fun g => u g * M w (A g x)).
Proof.
move=> hu hw.
have e1 : (fun g => w g * M u (A g x)) =
    (fun g => mu (fun s : S => (fun p : G * S => w p.1 * u (mul p.1 (set_val p.2))) (g, s))).
  apply: funext=> g; rewrite (coset_integral_value hM g hu) /=.
  by rewrite (hmuL.2 (w g) _ (coset_section_compact x hG hA hX g hu)).
have e2 : (fun g => u g * M w (A g x)) =
    (fun g => mu (fun s : S => (fun p : G * S =>
      psi (inv (set_val p.2)) * (w (mul p.1 (inv (set_val p.2))) * u p.1)) (g, s))).
  apply: funext=> g; rewrite (coset_integral_value hM g hw) /=.
  have hf := coset_section_compact x hG hA hX g hw.
  rewrite -(modular_function_left_inversion hDS hmu hf).
  have hDSc : continuous (DS : S -> real_line_metric R) := modular_function_continuous hDS.
  have hwi := weighted_inversion_compactly_supported hSG hDSc hf.
  rewrite -(hmuL.2 (u g) _ hwi); congr mu; apply: funext=> s.
  rewrite -hpsiS (subgroup_restriction_inv hR).
  by rewrite mulrCA [RHS]mulrC -mulrA.
rewrite e1 e2.
rewrite -(compact_daniell_iterations_commute hH hlG (lch_group_hausdorff hSG)
  (lch_group_locally_compact hSG) hl hmuD (coset_exchange_left_compact hu hw)).
rewrite -(compact_daniell_iterations_commute hH hlG (lch_group_hausdorff hSG)
  (lch_group_locally_compact hSG) hl hmuD (coset_exchange_right_compact hu hw)).
congr mu; apply: funext=> s /=.
pose F := fun g => w (mul g (inv (set_val s))) * u g.
have hF : KG F.
  apply: compact_support_continuous_multiplier hu.
  move=> g; apply: continuous_comp; first exact: right_translation_continuous hT (inv (set_val s)) g.
  exact: hw.1.
have hFt : (fun g => w g * u (mul g (set_val s))) =
    F \o right_multiplication_action mul inv (inv (set_val s)).
  apply: funext=> g; rewrite /F /= /right_multiplication_action (group_invK hgl).
  by rewrite (group_mulgK hgl).
rewrite hFt (hlr (inv (set_val s)) hF) -(hlL.2 _ _ hF).
by congr lambda.
Qed.

(** Source for [coset_integral_unit_section]: "For any u in K(G) we
    obtain from 2.7.10 a w in K(G)+ such that mu^x(w)(g x) = 1
    whenever g in spt u", Federer 2.7.11, proof, p. 129. Supporting
    lemma: w is a preimage under mu^x of a cutoff function equal to 1
    on the compact set A^x(spt u) (2.5.13, p. 106); the nonnegativity
    of w is not needed. *)
Lemma coset_integral_unit_section (hXl : locally_compact [set: X]) u : KG u ->
  exists2 w, KG w & forall g, real_function_support u g -> M w (A g x) = 1.
Proof.
move=> hu.
have hC : compact (orbit_map A x @` real_function_support u).
  apply: continuous_compact; last exact: hu.2.
  by apply: continuous_subspaceT; exact: orbit_map_continuous hA x.
have [hvK _ hv1] := compact_cutoff_specification R hX hXl hC.
have [w hw hMw] := coset_integral_onto hG hA hX hR hmu hM hvK.
by exists w=> // g hg; rewrite hMw; apply: hv1; exists g.
Qed.

(** Source for [coset_integral_kernel]: "Therefore ker mu^x subset
    ker lambda", Federer 2.7.11, proof, p. 129: if u in K(G) and
    mu^x(u) = 0, then lambda(u) = 0. Direct formalisation; with w from
    coset_integral_unit_section, lambda(u) = lambda_g[u(g) mu^x(w)(gx)]
    = lambda_g[w(g) mu^x(u)(gx)] = 0. *)
Theorem coset_integral_kernel (hXl : locally_compact [set: X]) u : KG u ->
  (forall y, M u y = 0) -> lambda u = 0.
Proof.
move=> hu hMu.
have [w hw hw1] := coset_integral_unit_section hXl hu.
have h := coset_integral_exchange hu hw.
have e1 : (fun g => w g * M u (A g x)) = (fun g => 0 * w g).
  by apply: funext=> g; rewrite hMu mulr0 mul0r.
have e2 : (fun g => u g * M w (A g x)) = u.
  apply: funext=> g; case: (pselect (real_function_support u g))=> hg.
    by rewrite hw1 // mulr1.
  by rewrite (real_function_zero_off_support hg) mul0r.
by rewrite e1 e2 (hlL.2 0 w hw) mul0r in h.
Qed.

(** Source for [coset_integral_factor_exists]: "there exists a linear
    function nu: K(X) -> R with nu o mu^x = lambda", Federer 2.7.11,
    proof, p. 129, from ker mu^x subset ker lambda and im mu^x = K(X).
    Existence proof: nu(v) = lambda(u) for a chosen u in K(G) with
    mu^x(u) = v; the linearity of nu is proved in
    coset_integral_factor_daniell from nu o mu^x = lambda alone. *)
Theorem coset_integral_factor_exists (hXl : locally_compact [set: X]) :
  exists nu : (X -> R) -> R, forall u, KG u -> nu (M u) = lambda u.
Proof.
have /choice [pick hpick] : forall v : X -> R, exists u : G -> R, KX v -> KG u /\ M u = v.
  move=> v; case: (pselect (KX v))=> hv.
    by have [u hu huv] := coset_integral_onto hG hA hX hR hmu hM hv; exists u.
  by exists (fun _ => 0)=> hv'; case: (hv hv').
exists (fun v => lambda (pick v))=> u hu.
have [hp hpM] := hpick _ (coset_integral_compact hM hu).
have hmu1 : KG (fun g => (-1) * u g) := compactly_supported_scale (-1) hu.
have hd : KG (fun g => pick (M u) g + (-1) * u g).
  exact: (function_lattice_add (@compactly_supported_continuous_functions_lattice R G) hp hmu1).
have hMd : forall y, M (fun g => pick (M u) g + (-1) * u g) y = 0.
  move=> y; rewrite (coset_integral_add hG hA hX hmu hM hp hmu1).
  by rewrite (coset_integral_scale hG hA hX hmu hM (-1) hu) /= hpM mulN1r subrr.
have := coset_integral_kernel hXl hd hMd.
rewrite (hlL.1 _ _ hp hmu1) (hlL.2 (-1) u hu) mulN1r=> /eqP.
by rewrite subr_eq0=> /eqP.
Qed.

(** Source for [coset_integral_factor_daniell]: "we see from
    2.7.10(5), (6) that nu is a chi covariant integral", Federer
    2.7.11, proof, p. 129, for the Daniell property: every nu with
    nu o mu^x = lambda on K(G) is a Daniell integral on K(X). Linearity
    follows from that of mu^x and lambda and from im mu^x = K(X). For
    f in K(X)+ and phi from 2.7.10(5), each k in K(X) with 0 <= k <= f
    equals mu^x[((k / mu^x(phi)) o A^x) . phi], and these functions on
    G lie in the positive order interval of
    ((f / mu^x(phi)) o A^x) . phi, on which lambda is bounded above
    (2.5.5, p. 96). The criterion of 2.5.13, p. 106, applies. *)
Theorem coset_integral_factor_daniell (hXl : locally_compact [set: X]) (nu : (X -> R) -> R) :
  (forall u, KG u -> nu (M u) = lambda u) -> is_daniell_integral KX nu.
Proof.
move=> hfac.
have hLG := @compactly_supported_continuous_functions_lattice R G.
apply: (compact_support_order_bounded_daniell hX hXl).
  split.
  - move=> f g hf hg.
    have [a ha <-] := coset_integral_onto hG hA hX hR hmu hM hf.
    have [b hb <-] := coset_integral_onto hG hA hX hR hmu hM hg.
    rewrite -(coset_integral_add hG hA hX hmu hM ha hb) !hfac //.
      exact: hlL.1.
    exact: (function_lattice_add hLG ha hb).
  - move=> c f hf.
    have [a ha <-] := coset_integral_onto hG hA hX hR hmu hM hf.
    rewrite -(coset_integral_scale hG hA hX hmu hM c ha) !hfac //.
      exact: hlL.2.
    exact: compactly_supported_scale.
move=> f [hf hf0].
have [phi hphi hsub] := coset_integral_cover x hG hA hf.
have [hphiK hphi0] := hphi.
have hMphi0 := coset_integral_nonnegative hG hA hX hmu hM hphiK hphi0.
pose T (k : X -> R) := fun g => k (A g x) / M phi (A g x) * phi g.
have hTq k : KX k -> real_function_support k `<=` real_function_support f -> KG (T k) /\ M (T k) = k.
  move=> hk hkf.
  have hks := subset_trans hkf hsub.
  split; last exact: (coset_integral_quotient hG hA hX hR hmu hM hk hphi hks).
  have [_ hqc] := coset_integral_quotient_compact hG hA hX hR hmu hM hk hphi hks.
  apply: compact_support_continuous_multiplier hphiK=> g.
  apply: (@continuous_comp G X (real_line_metric R) (orbit_map A x) (fun y => k y / M phi y) g).
    exact: orbit_map_continuous hA x g.
  exact: hqc.1.
have [hTf _] := hTq f hf (@subset_refl _ _).
have [b hb] := daniell_integral_order_bounded hl hTf.
exists b=> k [hk [hk0 hkf]].
have hkf' : real_function_support k `<=` real_function_support f.
  apply: closureS=> y /= hky hfy; apply: hky.
  by apply/eqP; rewrite eq_le -hfy hkf /= hfy hk0.
have [hTk hMTk] := hTq k hk hkf'.
rewrite -hMTk hfac //; apply: hb; split=> //; split=> g.
- by apply: mulr_ge0 (hphi0 g); apply: divr_ge0; [exact: hk0|exact: hMphi0].
- apply: ler_wpM2r; first exact: hphi0.
  by apply: ler_wpM2r; [rewrite invr_ge0; exact: hMphi0|exact: hkf].
Qed.

(** Source for [coset_integral_factor_covariant]: "we see from
    2.7.10(5), (6) that nu is a chi covariant integral", Federer
    2.7.11, proof, p. 129: if lambda is left chi covariant and
    nu o mu^x = lambda on K(G), then nu is a chi covariant integral on
    K(X). Direct formalisation; the covariance follows from 2.7.10(4)
    and im mu^x = K(X). *)
Theorem coset_integral_factor_covariant (hXl : locally_compact [set: X]) (chi : G -> R)
    (nu : (X -> R) -> R) :
  is_covariant_on KG (left_multiplication_action mul) chi lambda ->
  (forall u, KG u -> nu (M u) = lambda u) -> is_covariant_integral A chi nu.
Proof.
move=> hlc hfac; split; first exact: coset_integral_factor_daniell.
move=> v g hv; have [u hu <-] := coset_integral_onto hG hA hX hR hmu hM hv.
have hug := compactly_supported_translate hgl (left_multiplication_homogeneous hT) g hu.
rewrite -(coset_integral_translate hG hA hM g hu) !hfac //.
exact: hlc u g hu.
Qed.

(** Source for [coset_integral_factorisation]: Federer 2.7.11, proof,
    p. 129, from "For any u in K(G) we obtain from 2.7.10 a w" to
    "nu is a chi covariant integral": if lambda is a left chi covariant
    and right psi covariant Daniell integral on K(G), where psi is
    continuous with psi(t) = Delta_{G^x}(t) for t in G^x, then there is
    a chi covariant integral nu on K(X) with nu o mu^x = lambda on
    K(G). Direct formalisation. *)
Theorem coset_integral_factorisation (hXl : locally_compact [set: X]) (chi : G -> R) :
  is_covariant_on KG (left_multiplication_action mul) chi lambda ->
  exists nu : (X -> R) -> R,
    is_covariant_integral A chi nu /\ forall u, KG u -> nu (M u) = lambda u.
Proof.
move=> hlc; have [nu hfac] := coset_integral_factor_exists hXl.
by exists nu; split=> //; exact: coset_integral_factor_covariant.
Qed.

End CosetIntegralExchange.
