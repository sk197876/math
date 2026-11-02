(** Federer (1969), 2.7.3, printed p. 123: "One easily verifies that G acts
    uniformly on X if and only if for each neighborhood V of a point x in X
    there exists a neighborhood W of x such that g in G, W cap A_g(W) <>
    empty implies A_g(W) subset V; when this condition holds one may take as
    B the family of the sets U_{g in G} A_g(V) x A_g(V) corresponding to all
    nonempty open subsets V of X." Federer gives no proof. The necessity of
    the condition uses only the uniformity and the invariance of its basis:
    for a member beta of the basis with beta o beta^{-1} o beta inside a
    given entourage, the section W = {y : (x,y) in beta} has the required
    property, since A_g(W) is the section of beta at gx. For the
    sufficiency, the sets beta_V = U_g A_g(V) x A_g(V) contain the diagonal
    because the action is transitive, satisfy beta_{A_h(V)} = beta_V, which
    gives the filter base property, and the condition yields, for an open
    neighbourhood V of x, an open neighbourhood W of x with beta_W o beta_W
    subset beta_V and, for a neighbourhood N of x, one with {y : (x,y) in
    beta_W} subset N; the sections {y : (x,y) in beta_V} are open, since the
    A_g are homeomorphisms. The group laws and the definition of a
    homogeneous space (2.7.1, p. 121) are used; neither local compactness
    nor the Hausdorff property of X or G is needed. When X is empty, the
    family of the sets beta_V is empty and is not the basis of any
    uniformity, because a uniformity contains X x X; the second assertion
    therefore assumes that X is nonempty, while the equivalence holds
    without this hypothesis. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws UniformActionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope relation_scope.

Section Necessity.
Variable G : Type.
Variable X : topologicalType.
Variable A : G -> X -> X.

(** Source for [acts_uniformly_condition]: the implication "G acts
    uniformly on X ... only if for each neighborhood V of a point x in X
    there exists a neighborhood W of x such that g in G,
    W cap A_g(W) <> empty implies A_g(W) subset V", Federer 2.7.3,
    p. 123. Choose an entourage D with {y : (x,y) in D} subset V,
    entourages D1, D2 with D1 o D1 subset D and D2 o D2 subset D1, and a
    member beta of the invariant basis inside D2 cap D2^{-1}; take
    W = {y : (x,y) in beta}. If w in W cap A_g(W) and z in A_g(W), then
    (x,w), (gx,w), (gx,z) belong to beta, whence (x,gx) in D2 o D2 and
    (x,z) in D1 o D1. No property of A is used. *)
Theorem acts_uniformly_condition : acts_uniformly A -> uniform_action_condition A.
Proof.
case=> E [B [hE hnb [hBE hBb] hinv]] x V.
have hF := uniformity_filter hE.
rewrite hnb; case=> D hD hDV.
have [D1 hD1 hD1D] := uniformity_split hE hD.
have [D2 hD2 hD2D1] := uniformity_split hE hD1.
have hD2sub : D2 `<=` D1.
  case=> a b hab; apply: hD2D1; exists b=> //.
  exact: (uniformity_diagonal hE hD2) (b, b) erefl.
have hD3 : E (D2 `&` D2^-1) := @filterI _ _ hF _ _ hD2 (uniformity_inverse hE hD2).
have [beta hbeta hbetaD3] := hBb _ hD3.
exists (xsection beta x).
  by exists beta=> //; exact: hBE.
move=> g [w [/xsectionP hxw [w' /xsectionP hxw' hw']]] z [z' /xsectionP hxz' hz'].
have hgw : beta (A g x, w) by rewrite -hw'; apply/(hinv beta g x w' hbeta).
have hgz : beta (A g x, z) by rewrite -hz'; apply/(hinv beta g x z' hbeta).
apply: hDV; apply/xsectionP; apply: hD1D; exists (A g x).
- apply: hD2D1; exists w; first exact: (hbetaD3 _ hxw).1.
  exact: (hbetaD3 _ hgw).2.
- by apply: hD2sub; exact: (hbetaD3 _ hgz).1.
Qed.

End Necessity.

Section Sufficiency.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.

(** Source for [orbit_entourageP]: membership in
    U_{g in G} A_g(V) x A_g(V), Federer 2.7.3, p. 123. Supporting
    lemma. *)
Lemma orbit_entourageP (V : set X) y z :
  orbit_entourage A V (y, z) <-> exists g, (A g @` V) y /\ (A g @` V) z.
Proof. by split; [case=> g _ [hy hz]; exists g|case=> g [hy hz]; exists g]. Qed.

(** Source for [translate_image_mul]: A_g(A_h(V)) = A_{gh}(V),
    supporting Federer 2.7.3, p. 123, from A(gh,x) = A[g,A(h,x)] of
    2.7.1, p. 121. *)
Lemma translate_image_mul g h (V : set X) : A g @` (A h @` V) = A (mul g h) @` V.
Proof.
apply/seteqP; split=> y.
- by case=> _ [v hv <-] <-; exists v=> //; rewrite (homogeneous_action_compatible hA).
- by case=> v hv <-; exists (A h v); [exists v|rewrite (homogeneous_action_compatible hA)].
Qed.

(** Source for [translate_open]: A_g(V) is open for open V, as used in
    Federer 2.7.3, p. 123: A_g is a homeomorphism by 2.7.1, p. 121. *)
Lemma translate_open g (V : set X) : open V -> open (A g @` V).
Proof.
exact: homeomorphism_with_inverse_open_map (homogeneous_translation_homeomorphism hG hA g) V.
Qed.

(** Source for [orbit_entourage_invariant]: the sets
    U_{g in G} A_g(V) x A_g(V) are G invariant in the sense of Federer
    2.7.3, p. 123: (y,z) belongs to the set if and only if (gy,gz)
    does. If y, z in A_h(V) then gy, gz in A_{gh}(V); if gy, gz in
    A_h(V) then y, z in A_{g^{-1}h}(V). *)
Lemma orbit_entourage_invariant (V : set X) g y z :
  orbit_entourage A V (y, z) <-> orbit_entourage A V (A g y, A g z).
Proof.
have hback h u : (A h @` V) (A g u) -> (A (mul (inv g) h) @` V) u.
  case=> v hv hu; exists v=> //.
  by rewrite (homogeneous_action_compatible hA) hu (homogeneous_translation_inverse_left hG hA).
rewrite !orbit_entourageP; split.
- case=> h [hy hz]; exists (mul g h); rewrite -translate_image_mul.
  by split; apply: imageP.
- by case=> h [hy hz]; exists (mul (inv g) h); split; apply: hback.
Qed.

(** Source for [orbit_entourage_monotone]: V subset V' implies
    beta_V subset beta_V', supporting Federer 2.7.3, p. 123. *)
Lemma orbit_entourage_monotone (V V' : set X) :
  V `<=` V' -> orbit_entourage A V `<=` orbit_entourage A V'.
Proof.
move=> hVV' [y z] /orbit_entourageP [g [[v hv hy] [w hw hz]]].
by apply/orbit_entourageP; exists g; split; [exists v; [exact: hVV'|]|exists w; [exact: hVV'|]].
Qed.

(** Source for [orbit_entourage_diagonal]: for nonempty V the set
    U_{g in G} A_g(V) x A_g(V) contains the diagonal, supporting Federer
    2.7.3, p. 123: every y is A_g(v) for some g, by transitivity
    (im A^v = X, 2.7.1, p. 121). *)
Lemma orbit_entourage_diagonal (V : set X) : V !=set0 -> diagonal `<=` orbit_entourage A V.
Proof.
case=> v hv [y z] /diagonalP <-.
have [g hg] := homogeneous_transitive hA v y.
by apply/orbit_entourageP; exists g; split; exists v.
Qed.

(** Source for [orbit_entourage_inverse]: beta_V^{-1} subset beta_V,
    supporting Federer 2.7.3, p. 123. *)
Lemma orbit_entourage_inverse (V : set X) : (orbit_entourage A V)^-1 `<=` orbit_entourage A V.
Proof.
by case=> y z /= /orbit_entourageP [g [hz hy]]; apply/orbit_entourageP; exists g.
Qed.

(** Source for [orbit_entourage_translate]: beta_{A_h(V)} = beta_V,
    supporting Federer 2.7.3, p. 123: A_g(A_h(V)) = A_{gh}(V) and
    A_g(V) = A_{gh^{-1}}(A_h(V)). *)
Lemma orbit_entourage_translate h (V : set X) : orbit_entourage A (A h @` V) = orbit_entourage A V.
Proof.
apply/seteqP; split=> -[y z] /orbit_entourageP [g [hy hz]]; apply/orbit_entourageP.
- by exists (mul g h); rewrite -translate_image_mul.
- exists (mul g (inv h)); rewrite translate_image_mul -(group_mulA hG) (group_mulVg hG).
  by rewrite (group_mulg1 hG).
Qed.

(** Source for [orbit_entourage_filter_base]: for nonempty open
    V_1, V_2 there is a nonempty open V_3 with
    beta_{V_3} subset beta_{V_1} cap beta_{V_2}, so the family of
    Federer 2.7.3, p. 123, is a filter base. Choose v_i in V_i and h with
    A_h(v_2) = v_1, and take V_3 = V_1 cap A_h(V_2). *)
Lemma orbit_entourage_filter_base (V1 V2 : set X) :
  open V1 /\ V1 !=set0 -> open V2 /\ V2 !=set0 ->
  exists2 V3, open V3 /\ V3 !=set0 &
    orbit_entourage A V3 `<=` orbit_entourage A V1 `&` orbit_entourage A V2.
Proof.
case=> hV1 [v1 hv1] [hV2 [v2 hv2]].
have [h hh] := homogeneous_transitive hA v2 v1.
exists (V1 `&` A h @` V2).
  split; first by apply: openI=> //; exact: translate_open.
  by exists v1; split=> //; exists v2.
move=> p hp; split.
- by apply: orbit_entourage_monotone hp=> u [].
- rewrite -(orbit_entourage_translate h V2).
  by apply: orbit_entourage_monotone hp=> u [].
Qed.

(** Source for [orbit_entourage_section]: the section of
    U_{g in G} A_g(V) x A_g(V) at x is the union of the sets A_g(V)
    containing x, supporting Federer 2.7.3, p. 123. *)
Lemma orbit_entourage_section (V : set X) x :
  xsection (orbit_entourage A V) x = \bigcup_(g in [set g | (A g @` V) x]) (A g @` V).
Proof.
apply/seteqP; split=> y.
- by move=> /xsectionP /orbit_entourageP [g [hx hy]]; exists g.
- by case=> g hx hy; apply/xsectionP/orbit_entourageP; exists g.
Qed.

(** Source for [orbit_entourage_section_open]: for open V the section
    of U_{g in G} A_g(V) x A_g(V) at x is open, supporting the equality
    of topologies in Federer 2.7.3, p. 123. *)
Lemma orbit_entourage_section_open (V : set X) x : open V -> open (xsection (orbit_entourage A V) x).
Proof.
by move=> hV; rewrite orbit_entourage_section; apply: bigcup_open=> g _; exact: translate_open.
Qed.

Section Condition.
Hypothesis hc : uniform_action_condition A.

(** Source for [uniform_action_condition_open]: the neighbourhood W
    of the condition of Federer 2.7.3, p. 123, may be taken open: its
    interior has the same property. Supporting lemma. *)
Lemma uniform_action_condition_open x (V : set X) : nbhs x V ->
  exists2 W, open W /\ W x & forall g, W `&` A g @` W !=set0 -> A g @` W `<=` V.
Proof.
move=> hV; have [W hW hWV] := hc hV.
exists W°; first by split; [exact: open_interior|exact: hW].
move=> g [y [hy1 [w hw hwy]]] z [u hu hz].
apply: (hWV g); first by exists y; split; [exact: interior_subset|exists w=> //; exact: interior_subset].
by exists u=> //; exact: interior_subset.
Qed.

(** Source for [orbit_entourage_split]: for open V containing x there
    is a nonempty open W with beta_W o beta_W subset beta_V, Federer
    2.7.3, p. 123. Take the open W of the condition for V; then
    W subset V (case g = e). If a, b in A_g(W) and b, c in A_h(W), then
    W cap A_{g^{-1}h}(W) contains g^{-1}b, hence A_{g^{-1}h}(W) subset V
    and a, c in A_g(V). *)
Lemma orbit_entourage_split (V : set X) x : open V -> V x ->
  exists2 W, open W /\ W !=set0 & orbit_entourage A W \; orbit_entourage A W `<=` orbit_entourage A V.
Proof.
move=> hV hx.
have [W [hWo hWx] hWV] := uniform_action_condition_open (open_nbhs_nbhs (conj hV hx)).
have hsub : W `<=` V.
  have h := hWV e; rewrite (homogeneous_unit_identity hG hA) image_id in h.
  by apply: h; exists x.
exists W; first by split=> //; exists x.
move=> [a c] [b /orbit_entourageP [g [[wa hwa hab] [wb hwb hbb]]]]
  /orbit_entourageP [h [[wb' hwb' hbb'] [wc hwc hcc]]].
have hk : A (mul (inv g) h) @` W `<=` V.
  apply: hWV; exists wb; split=> //; exists wb'=> //.
  rewrite (homogeneous_action_compatible hA) hbb' -hbb.
  exact: (homogeneous_translation_inverse_left hG hA).
apply/orbit_entourageP; exists g; split; first by exists wa=> //; exact: hsub.
exists (A (mul (inv g) h) wc); first by apply: hk; exists wc.
rewrite -(homogeneous_action_compatible hA) (group_mulA hG) (group_mulgV hG) (group_mul1g hG).
exact: hcc.
Qed.

(** Source for [orbit_entourage_section_nbhs]: for a neighbourhood N
    of x there is a nonempty open W with
    {y : (x,y) in beta_W} subset N, Federer 2.7.3, p. 123. Take the open
    W of the condition for N; if x, y in A_g(W), then x lies in
    W cap A_g(W), hence A_g(W) subset N. *)
Lemma orbit_entourage_section_nbhs x (N : set X) : nbhs x N ->
  exists2 W, open W /\ W !=set0 & xsection (orbit_entourage A W) x `<=` N.
Proof.
move=> hN; have [W [hWo hWx] hWN] := uniform_action_condition_open hN.
exists W; first by split=> //; exists x.
move=> y /xsectionP /orbit_entourageP [g [hx hy]].
by apply: (hWN g)=> //; exists x.
Qed.

(** Source for [uniform_action_orbit_basis]: "when this condition
    holds one may take as B the family of the sets
    U_{g in G} A_g(V) x A_g(V) corresponding to all nonempty open
    subsets V of X", Federer 2.7.3, p. 123. Direct formalisation, for
    nonempty X: the sets containing some beta_V form a uniformity which
    induces the topology of X, the family of the beta_V is a G invariant
    basis of it. *)
Theorem uniform_action_orbit_basis : (exists x : X, True) ->
  let E := filter_from [set V : set X | open V /\ V !=set0] (orbit_entourage A) in
  [/\ is_uniformity E, uniformity_induces_topology E,
    is_uniformity_basis E (orbit_entourage_family A) &
    is_invariant_entourage_family A (orbit_entourage_family A)].
Proof.
move=> [x0 _] E.
have hF : Filter E.
  apply: filter_from_filter; first by exists setT; split; [exact: openT|exists x0].
  move=> V1 V2 h1 h2; exact: orbit_entourage_filter_base.
split.
- constructor=> //.
  + by move=> D [V [_ hV] hVD]; apply: subset_trans hVD; exact: orbit_entourage_diagonal.
  + move=> D [V hV hVD]; exists V=> // -[y z] hyz; apply: hVD.
    exact: orbit_entourage_inverse.
  + move=> D [V [hVo [x hx]] hVD].
    have [W hW hWV] := orbit_entourage_split hVo hx.
    exists (orbit_entourage A W); first by exists W.
    exact: subset_trans hWV hVD.
- move=> x; apply/seteqP; split=> N hN.
  + have [W hW hWN] := orbit_entourage_section_nbhs hN.
    by exists (orbit_entourage A W)=> //; exists W.
  + case: hN=> D [V [hVo hVne] hVD] hDN.
    apply: (@filterS _ _ _ (xsection (orbit_entourage A V) x)).
      by move=> y /xsectionP hy; apply: hDN; apply/xsectionP; exact: hVD.
    apply: open_nbhs_nbhs; split; first exact: orbit_entourage_section_open.
    by apply/xsectionP; exact: orbit_entourage_diagonal.
- split.
    by move=> _ [V hV <-]; exists V.
  by move=> D [V hV hVD]; exists (orbit_entourage A V)=> //; exists V.
- by move=> _ g y z [V _ <-]; exact: orbit_entourage_invariant.
Qed.

End Condition.

(** Source for [acts_uniformly_iff]: "One easily verifies that G acts
    uniformly on X if and only if for each neighborhood V of a point x
    in X there exists a neighborhood W of x such that g in G,
    W cap A_g(W) <> empty implies A_g(W) subset V", Federer 2.7.3,
    p. 123. Direct formalisation for a homogeneous space X of a group G.
    The sufficiency uses uniform_action_orbit_basis when X is nonempty;
    when X is empty, the family of all subsets of X x X is a uniformity
    inducing the topology, with itself as invariant basis. *)
Theorem acts_uniformly_iff : acts_uniformly A <-> uniform_action_condition A.
Proof.
split; first exact: acts_uniformly_condition.
move=> hc; case: (pselect (exists x : X, True))=> hX.
  have [hE hnb hB hinv] := uniform_action_orbit_basis hc hX.
  by do 2 eexists; split; [exact: hE|exact: hnb|exact: hB|exact: hinv].
have hno (x : X) : False by apply: hX; exists x.
exists [set: set (X * X)], [set: set (X * X)]; split.
- constructor.
  + by constructor.
  + by move=> D _ [x y]; case: (hno x).
  + by [].
  + by move=> D _; exists D=> // -[x y]; case: (hno x).
- by move=> x; case: (hno x).
- by split=> // D _; exists D.
- by move=> beta g x; case: (hno x).
Qed.

End Sufficiency.
