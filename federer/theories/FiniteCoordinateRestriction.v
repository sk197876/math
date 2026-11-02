(** Federer (1969), 2.6.6, p. 120: "Whenever a subset b in A, the projection
    p^b_a : X_b -> X_a shows that L_a subset L_b; moreover p^b_a#(mu_b) =
    mu_a because mu_b(f o p^b_a) = mu_a(f) mu_{b-a}(1) = mu_a(f) for f in
    K(X_a)." This file defines p^b_a, proves the separated-product formula
    mu_{a cup c}(f o p_a . g o p_c) = mu_a(f) mu_c(g) for disjoint finite
    sets a and c, identifies the image of mu_{a cup c} on X_a x X_c with the
    product of 2.6.4, p. 119, and derives the displayed chain of equalities.
    The finite products are given only through their abstract laws
    [is_finite_coordinate_product_family]. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp mathcomp_extra classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP DaniellIntegralUP MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralSum FunctionLatticeUP FunctionLatticeSeminormUP ConsistentCylinderFunctionalUP
  ProductCylinderLattice FiniteCoordinateProjection FiniteCoordinatePullback FiniteCoordinateMarginal
  FiniteCoordinateProductUP CoordinateDaniellOperator CoordinateDaniellDependence NormalizedProductSpace
  CompactContinuousPullback CompactSeparatedProduct HausdorffBinaryProduct SubtypeCompactHausdorff
  MonotoneCompactSupportFunctional DaniellSpaceCompactness DaniellSpaceCompactSpace DaniellProductUP
  DaniellProduct DaniellProductUniqueness TopologicalProductMaps DependentProductContinuity
  FiniteCoordinateSplit FiniteCoordinateAdjoinProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Restriction.
Variables (I : choiceType) (Y : I -> topologicalType).

(** Source for [finite_coordinate_restriction]: the projection
    p^b_a : X_b -> X_a for a subset b, Federer 2.6.6, p. 120. *)
Definition finite_coordinate_restriction (F G : {fset I}) (hFG : {subset F <= G})
    (u : finite_coordinate_space Y G) : finite_coordinate_space Y F :=
  fun j=>u (exist _ (val j) (hFG _ (valP j))).

(** Source for [finite_coordinate_restriction_projection]: p^b_a o p_b
    = p_a, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_restriction_projection (F G : {fset I}) (hFG : {subset F <= G})
    (x : prod_topology Y) :
  finite_coordinate_restriction hFG (finite_coordinate_projection (F:=G) x)=
    finite_coordinate_projection (F:=F) x.
Proof. by []. Qed.

(** Source for [finite_coordinate_restriction_continuous]: continuity
    of p^b_a, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_restriction_continuous (F G : {fset I}) (hFG : {subset F <= G}) :
  continuous (finite_coordinate_restriction hFG).
Proof.
apply: dependent_product_map_continuous=> j.
exact (@proj_continuous [the choiceType of {k : I | k \in G}] (fun k=>Y (val k))
  (exist _ (val j) (hFG _ (valP j)))).
Qed.

(** Source for [fset_subset_unionl]: supporting inclusion a subset
    a cup c of finite index sets, Federer 2.6.6, p. 120. *)
Lemma fset_subset_unionl (F H : {fset I}) : {subset F <= F `|` H}.
Proof. by move=> j hj; rewrite in_fsetU hj. Qed.

(** Source for [fset_subset_unionr]: supporting inclusion c subset
    a cup c of finite index sets, Federer 2.6.6, p. 120. *)
Lemma fset_subset_unionr (F H : {fset I}) : {subset H <= F `|` H}.
Proof. by move=> j hj; rewrite in_fsetU hj orbT. Qed.

(** Source for [finite_coordinate_pair_split]: the map
    X_{a cup c} -> X_a x X_c, u -> (p^{a cup c}_a(u), p^{a cup c}_c(u)),
    by which mu_{a cup c} is compared with the product of mu_a and
    mu_c in the sense of 2.6.4, p. 119; Federer 2.6.6, p. 120. *)
Definition finite_coordinate_pair_split (F H : {fset I}) (u : finite_coordinate_space Y (F `|` H)) :
    (finite_coordinate_space Y F * finite_coordinate_space Y H)%type :=
  (finite_coordinate_restriction (@fset_subset_unionl F H) u,
   finite_coordinate_restriction (@fset_subset_unionr F H) u).

(** Source for [finite_coordinate_pair_split_continuous]: continuity of
    the map X_{a cup c} -> X_a x X_c, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_pair_split_continuous (F H : {fset I}) :
  continuous (@finite_coordinate_pair_split F H).
Proof.
apply: topological_pair_continuous; exact: finite_coordinate_restriction_continuous.
Qed.

(** Source for [finite_coordinate_pair_join]: the inverse of the map
    X_{a cup c} -> X_a x X_c for disjoint a and c, supporting the
    decomposition of X_b as X_a x X_{b-a} in Federer 2.6.6, p. 120.
    The point x0 of X only fills the coordinates outside a cup c. *)
Definition finite_coordinate_pair_join (x0 : prod_topology Y) (F H : {fset I})
    (q : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type) :
    finite_coordinate_space Y (F `|` H) :=
  finite_coordinate_projection (F:=F `|` H)
    (finite_coordinate_section (finite_coordinate_section x0 q.2) q.1).

(** Source for [finite_coordinate_section_member]: the section s(u)
    of p_a has the coordinates of u on a, supporting Federer 2.6.6,
    p. 120. *)
Lemma finite_coordinate_section_member (x0 : prod_topology Y) (F : {fset I})
    (u : finite_coordinate_space Y F) (k : I) (hk : k \in F) :
  finite_coordinate_section x0 u k=u (exist _ k hk).
Proof.
rewrite /finite_coordinate_section; case: pselect=> h; last by exfalso; exact: h hk.
exact: finite_coordinate_coordinate_irrelevance.
Qed.

(** Source for [finite_coordinate_section_nonmember]: the section s(u)
    of p_a agrees with the base point off a, supporting Federer 2.6.6,
    p. 120. *)
Lemma finite_coordinate_section_nonmember (x0 : prod_topology Y) (F : {fset I})
    (u : finite_coordinate_space Y F) (k : I) :
  k \notin F -> finite_coordinate_section x0 u k=x0 k.
Proof.
move=> hk; rewrite /finite_coordinate_section; case: pselect=> h //.
by exfalso; move: hk; rewrite h.
Qed.

(** Source for [finite_coordinate_pair_join_continuous]: continuity of
    the inverse map X_a x X_c -> X_{a cup c}, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_pair_join_continuous (x0 : prod_topology Y) (F H : {fset I}) :
  continuous (@finite_coordinate_pair_join x0 F H).
Proof.
have hs : continuous (fun q : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type=>
    finite_coordinate_section (finite_coordinate_section x0 q.2) q.1).
  apply: dependent_product_map_continuous=> k.
  rewrite /finite_coordinate_section; case: pselect=> hkF.
  - move=> q; exact: (continuous_comp (@first_projection_continuous _ _ q)
      (@proj_continuous [the choiceType of {j : I | j \in F}] (fun j=>Y (val j)) (Sub k hkF) q.1)).
  - case: pselect=> hkH; last exact: cst_continuous.
    move=> q; exact: (continuous_comp (@second_projection_continuous _ _ q)
      (@proj_continuous [the choiceType of {j : I | j \in H}] (fun j=>Y (val j)) (Sub k hkH) q.2)).
move=> q; apply: continuous_comp (hs q) _.
exact: finite_coordinate_projection_continuous.
Qed.

(** Source for [finite_coordinate_pair_join_split]: the join is a left
    inverse of the map X_{a cup c} -> X_a x X_c, Federer 2.6.6,
    p. 120. *)
Lemma finite_coordinate_pair_join_split (x0 : prod_topology Y) (F H : {fset I})
    (u : finite_coordinate_space Y (F `|` H)) :
  finite_coordinate_pair_join x0 (finite_coordinate_pair_split u)=u.
Proof.
apply: functional_extensionality_dep=> -[k hk].
rewrite /finite_coordinate_pair_join /finite_coordinate_projection /=.
case: (boolP (k \in F))=> hkF.
- rewrite (finite_coordinate_section_member _ _ hkF) /finite_coordinate_restriction /=.
  exact: finite_coordinate_coordinate_irrelevance.
- have hkH : k \in H by move: hk; rewrite in_fsetU (negbTE hkF).
  rewrite (finite_coordinate_section_nonmember _ _ hkF) (finite_coordinate_section_member _ _ hkH).
  rewrite /finite_coordinate_restriction /=.
  exact: finite_coordinate_coordinate_irrelevance.
Qed.

(** Source for [finite_coordinate_pair_split_join]: for disjoint a and
    c the join is a right inverse of the map X_{a cup c} -> X_a x X_c,
    Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_pair_split_join (x0 : prod_topology Y) (F H : {fset I})
    (q : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type) :
  (forall j, j \in H -> j \notin F) -> finite_coordinate_pair_split (finite_coordinate_pair_join x0 q)=q.
Proof.
move=> hdisj; case: q=> v w.
rewrite /finite_coordinate_pair_split /finite_coordinate_pair_join; congr pair.
- apply: functional_extensionality_dep=> -[j hj].
  rewrite /finite_coordinate_restriction /finite_coordinate_projection /=.
  exact: finite_coordinate_section_member.
- apply: functional_extensionality_dep=> -[j hj].
  rewrite /finite_coordinate_restriction /finite_coordinate_projection /=.
  rewrite (finite_coordinate_section_nonmember _ _ (hdisj j hj)).
  exact: finite_coordinate_section_member.
Qed.

(** Source for [finite_coordinate_pair_split_homeomorphism]: for
    disjoint a and c the map X_{a cup c} -> X_a x X_c is a
    homeomorphism; in particular X_b is identified with X_a x X_{b-a}
    for a subset b, Federer 2.6.6, p. 120. *)
Theorem finite_coordinate_pair_split_homeomorphism (x0 : prod_topology Y) (F H : {fset I}) :
  (forall j, j \in H -> j \notin F) ->
  continuous (@finite_coordinate_pair_split F H) /\ continuous (@finite_coordinate_pair_join x0 F H) /\
  (forall u : finite_coordinate_space Y (F `|` H),
    finite_coordinate_pair_join x0 (finite_coordinate_pair_split u)=u) /\
  (forall q : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type,
    finite_coordinate_pair_split (finite_coordinate_pair_join x0 q)=q).
Proof.
move=> hdisj; split; first exact: finite_coordinate_pair_split_continuous.
split; first exact: finite_coordinate_pair_join_continuous.
split; first exact: finite_coordinate_pair_join_split.
move=> q; exact: finite_coordinate_pair_split_join.
Qed.
End Restriction.

Section DisjointProduct.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R).
Hypotheses (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Hypotheses (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
  (hA1 : forall i, @A i (fun _=>1) = 1).
Variable C : {fset I} -> (prod_topology Y -> R) -> R.
Hypothesis hC : is_finite_coordinate_product_family A C.
Local Notation X := (prod_topology Y).

(** Source for [hX]: compactness of X by Tychonoff's theorem, the
    standing situation of Federer 2.6.6, p. 120. *)
Let hX : compact (@setT X) := compact_factor_product_compact hc.

(** Source for [hCc]: the consistency laws of the finite products,
    Federer 2.6.6, p. 120. *)
Let hCc : is_consistent_cylinder_functional_family C := finite_coordinate_product_consistency hC.

(** Source for [finite_coordinate_pair_cylinder]: the functions
    k o (p_a, p_c), k in K(X_a x X_c), belong to L_{a cup c},
    Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_pair_cylinder (F H : {fset I})
    (k : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type -> R) :
  compactly_supported_continuous_functions k ->
  continuous_coordinate_functions (F `|` H)
    (fun x=>k (finite_coordinate_projection (F:=F) x, finite_coordinate_projection (F:=H) x)).
Proof.
move=> hk.
have he : (fun x=>k (finite_coordinate_projection (F:=F) x, finite_coordinate_projection (F:=H) x))=
    (k \o @finite_coordinate_pair_split I Y F H) \o finite_coordinate_projection (F:=F `|` H) by [].
rewrite he; apply: finite_coordinate_pullback_membership hX _.
apply: compact_continuous_pullback_membership hk.
- exact: (@finite_coordinate_space_compact I Y hc (F `|` H)).
- exact: finite_coordinate_pair_split_continuous.
Qed.

(** Source for [finite_coordinate_disjoint_separated_value]: the
    product formula mu_{a cup c}((f o p_a)(g o p_c)) = mu_a(f) mu_c(g)
    for disjoint a and c, f in K(X_a), g in K(X_c), Federer 2.6.6,
    p. 120, by the method of 2.6.4, p. 119, adjoining the factors
    of c one at a time. *)
Theorem finite_coordinate_disjoint_separated_value (F H : {fset I})
    (f : finite_coordinate_space Y F -> R) (g : finite_coordinate_space Y H -> R) :
  (forall j, j \in H -> j \notin F) ->
  compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
  C (F `|` H) (fun x=>f (finite_coordinate_projection (F:=F) x)*g (finite_coordinate_projection (F:=H) x))=
    finite_coordinate_marginal C F f*finite_coordinate_marginal C H g.
Proof.
move=> + hf; move: g; elim/fset1U_rect: H=> [|i H hi ih] g hdisj hg.
- have [x0 _] := normalized_daniell_product_nonempty hA hA1.
  have hp0 : forall x : X, finite_coordinate_projection (F:=fset0) x=finite_coordinate_projection (F:=fset0) x0.
    move=> x; apply: functional_extensionality_dep=> -[j hj].
    by exfalso; move: hj; rewrite in_fset0.
  rewrite fsetU0.
  have -> : (fun x : X=>f (finite_coordinate_projection (F:=F) x)*g (finite_coordinate_projection (F:=fset0) x))=
      (fun x=>g (finite_coordinate_projection (F:=fset0) x0)*(f \o finite_coordinate_projection (F:=F)) x).
    by apply: funext=> x; rewrite hp0 mulrC.
  have hl := (cylinder_family_linear hCc F).2 (g (finite_coordinate_projection (F:=fset0) x0)) _
    (finite_coordinate_pullback_membership hX hf).
  rewrite hl {2}/finite_coordinate_marginal.
  rewrite (finite_coordinate_product_empty hC (finite_coordinate_pullback_membership hX hg) x0).
  by rewrite mulrC.
- have hiF : i \notin F := hdisj i (fset1U1 i H).
  have hdisjH : forall j, j \in H -> j \notin F by move=> j hj; apply: hdisj; rewrite fset1Ur.
  have hiFH : i \notin F `|` H by rewrite in_fsetU negb_or hiF hi.
  have hm := finite_coordinate_pair_cylinder (compactly_supported_separated_product hf hg).
  rewrite /= fsetUCA in hm; rewrite fsetUCA.
  rewrite (finite_coordinate_product_adjoin hC hiFH hm).
  have hgX := finite_coordinate_pullback_membership hX hg.
  have hAi := daniell_compact_support_linear (monotone_daniell_integral_is_daniell (@hA i)).
  have hg'K := coordinate_daniell_operator_preserves_continuity (@hh i) (@hc i) hX
    (monotone_daniell_integral_is_daniell (@hA i)) hgX.1.
  have hg'd := @coordinate_daniell_operator_determined R I Y A i (i |` H) _ hgX.2.
  rewrite fsetU1K // in hg'd.
  have [x0 _] := normalized_daniell_product_nonempty hA hA1.
  have [g'' [hg'' he'']] := (proj1 (@finite_coordinate_cylinder_image R I Y x0 H _ hX)) (conj hg'K hg'd).
  have he : coordinate_daniell_operator A i
      (fun x=>f (finite_coordinate_projection (F:=F) x)*g (finite_coordinate_projection (F:=i |` H) x))=
      (fun x=>f (finite_coordinate_projection (F:=F) x)*g'' (finite_coordinate_projection (F:=H) x)).
    apply: funext=> x; rewrite /coordinate_daniell_operator.
    have -> : (fun u=>f (finite_coordinate_projection (F:=F) (dfwith x i u))*
        g (finite_coordinate_projection (F:=i |` H) (dfwith x i u)))=
        (fun u=>f (finite_coordinate_projection (F:=F) x)*
        (g \o finite_coordinate_projection (F:=i |` H)) (dfwith x i u)).
      by apply: funext=> u; rewrite (@finite_coordinate_projection_dfwith I Y F i x u hiF).
    rewrite (hAi.2 _ _ (coordinate_daniell_section_membership x (@hc i) hgX.1)).
    congr (_*_); exact: (congr1 (fun h=>h x) he'').
  rewrite he (ih g'' hdisjH hg''); congr (_*_).
  rewrite /finite_coordinate_marginal -he''.
  by rewrite (finite_coordinate_product_adjoin hC hi hgX).
Qed.

(** Source for [finite_coordinate_disjoint_functional]: the image of
    mu_{a cup c} on X_a x X_c, Federer 2.6.6, p. 120. *)
Definition finite_coordinate_disjoint_functional (F H : {fset I})
    (k : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type -> R) :=
  finite_coordinate_marginal C (F `|` H) (k \o @finite_coordinate_pair_split I Y F H).

(** Source for [finite_coordinate_disjoint_daniell_product]: for
    disjoint a and c, the image of mu_{a cup c} on X_a x X_c satisfies
    the laws of the product of mu_a and mu_c in Federer 2.6.4,
    p. 119; this is the decomposition mu_b = mu_a x mu_{b-a} behind
    the consistency computation of 2.6.6, p. 120. *)
Theorem finite_coordinate_disjoint_daniell_product (F H : {fset I}) :
  (forall j, j \in H -> j \notin F) ->
  is_daniell_product (finite_coordinate_marginal C F) (finite_coordinate_marginal C H)
    (@finite_coordinate_disjoint_functional F H).
Proof.
move=> hdisj; split.
- apply: monotone_daniell_integral_is_daniell.
  apply: monotone_compact_support_linear_daniell.
  + exact: hausdorff_binary_product (@finite_coordinate_space_hausdorff I Y hh F)
      (@finite_coordinate_space_hausdorff I Y hh H).
  + apply: compact_space_locally_compact.
    exact: (@binary_space_compact (finite_coordinate_space Y F) (finite_coordinate_space Y H)
      (@finite_coordinate_space_compact I Y hc F) (@finite_coordinate_space_compact I Y hc H)).
  + split.
    * move=> f g hf hg; rewrite /finite_coordinate_disjoint_functional /finite_coordinate_marginal.
      exact: (cylinder_family_linear hCc (F `|` H)).1 _ _
        (finite_coordinate_pair_cylinder hf) (finite_coordinate_pair_cylinder hg).
    * move=> c f hf; rewrite /finite_coordinate_disjoint_functional /finite_coordinate_marginal.
      exact: (cylinder_family_linear hCc (F `|` H)).2 c _ (finite_coordinate_pair_cylinder hf).
  + move=> f g hf hg hfg; rewrite /finite_coordinate_disjoint_functional /finite_coordinate_marginal.
    apply: (cylinder_family_monotone hCc (finite_coordinate_pair_cylinder hf)
      (finite_coordinate_pair_cylinder hg))=> x.
    exact: hfg.
- move=> f g hf hg; rewrite /finite_coordinate_disjoint_functional {1}/finite_coordinate_marginal.
  exact: (finite_coordinate_disjoint_separated_value hdisj hf hg).
Qed.

(** Source for [finite_coordinate_disjoint_daniell_product_value]: for
    disjoint a and c the image of mu_{a cup c} on X_a x X_c equals the
    product functional of mu_a and mu_c of Federer 2.6.4, p. 119, on
    K(X_a x X_c), for every choice of the proofs of its hypotheses;
    Federer 2.6.6, p. 120. *)
Theorem finite_coordinate_disjoint_daniell_product_value (F H : {fset I})
    (hXF : hausdorff_space (finite_coordinate_space Y F))
    (hlXF : locally_compact (@setT (finite_coordinate_space Y F)))
    (hXH : hausdorff_space (finite_coordinate_space Y H))
    (hlXH : locally_compact (@setT (finite_coordinate_space Y H)))
    (hmuF : is_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y F))
      (finite_coordinate_marginal C F))
    (hmuH : is_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y H))
      (finite_coordinate_marginal C H))
    (k : (finite_coordinate_space Y F * finite_coordinate_space Y H)%type -> R) :
  (forall j, j \in H -> j \notin F) -> compactly_supported_continuous_functions k ->
  @finite_coordinate_disjoint_functional F H k=daniell_product hXF hlXF hXH hlXH hmuF hmuH k.
Proof.
move=> hdisj hk.
exact: (daniell_product_unique hXF hlXF hXH hlXH (finite_coordinate_disjoint_daniell_product hdisj)
  (daniell_product_specification hXF hlXF hXH hlXH hmuF hmuH) hk).
Qed.

(** Source for [fset_union_difference]: supporting identity
    b = a cup (b - a) for a subset b, Federer 2.6.6, p. 120. *)
Lemma fset_union_difference (F G : {fset I}) : {subset F <= G} -> F `|` (G `\` F)=G.
Proof.
move=> hFG; apply/fsetP=> j; rewrite in_fsetU in_fsetD.
by case: (boolP (j \in F))=> hj //=; rewrite (hFG j hj).
Qed.

(** Source for [finite_coordinate_marginal_restriction_product]: the
    first equation mu_b(f o p^b_a) = mu_a(f) mu_{b-a}(1) of Federer
    2.6.6, p. 120, for a subset b and f in K(X_a). *)
Theorem finite_coordinate_marginal_restriction_product (F G : {fset I}) (hFG : {subset F <= G})
    (f : finite_coordinate_space Y F -> R) :
  compactly_supported_continuous_functions f ->
  finite_coordinate_marginal C G (f \o finite_coordinate_restriction hFG)=
    finite_coordinate_marginal C F f*finite_coordinate_marginal C (G `\` F) (fun _=>1).
Proof.
move=> hf.
have hdisj : forall j, j \in G `\` F -> j \notin F by move=> j; rewrite in_fsetD=> /andP[].
have h1 : compactly_supported_continuous_functions (fun _ : finite_coordinate_space Y (G `\` F)=>(1 : R)).
  exact: compact_space_constant_one (@finite_coordinate_space_compact I Y hc (G `\` F)).
rewrite -(finite_coordinate_disjoint_separated_value hdisj hf h1).
rewrite /finite_coordinate_marginal (fset_union_difference hFG).
by congr (C G); apply: funext=> x; rewrite /= mulr1.
Qed.

(** Source for [finite_coordinate_marginal_restriction]: the
    consistency p^b_a#(mu_b) = mu_a of Federer 2.6.6, p. 120, through
    the displayed chain mu_b(f o p^b_a) = mu_a(f) mu_{b-a}(1) = mu_a(f)
    for f in K(X_a). *)
Theorem finite_coordinate_marginal_restriction (F G : {fset I}) (hFG : {subset F <= G})
    (f : finite_coordinate_space Y F -> R) :
  compactly_supported_continuous_functions f ->
  finite_coordinate_marginal C G (f \o finite_coordinate_restriction hFG)=
    finite_coordinate_marginal C F f*finite_coordinate_marginal C (G `\` F) (fun _=>1) /\
  finite_coordinate_marginal C F f*finite_coordinate_marginal C (G `\` F) (fun _=>1)=
    finite_coordinate_marginal C F f.
Proof.
move=> hf; split; first exact: finite_coordinate_marginal_restriction_product.
by rewrite {2}/finite_coordinate_marginal (cylinder_family_one hCc) mulr1.
Qed.
End DisjointProduct.
