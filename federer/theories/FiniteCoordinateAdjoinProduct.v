(** Federer (1969), 2.6.6, p. 120: "the cartesian product mu_a of the
    Daniell integrals mu_j corresponding to j in a (constructed by the
    method of 2.6.4)". The finite products used in 2.6.6 are specified by
    the empty-product, adjoining-factor and consistency laws of
    [is_finite_coordinate_product_family]. This file identifies them with
    the products of 2.6.4, p. 119: for i not in a, the image of mu_{a cup
    {i}} under the homeomorphism psi of X_{a cup {i}} onto X_a x X_i
    satisfies the defining laws [is_daniell_product] of the product of mu_a
    and mu_i, hence equals [daniell_product] on K(X_a x X_i). It also proves
    the separated-product formula mu_a(prod_{j in a} f_j o pi_j) = prod_{j
    in a} mu_j(f_j) on L_a. The May 1987 erratum to p. 119 concerns only the
    last regularity assertion of 2.6.4 and is not used. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp mathcomp_extra classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP DaniellIntegralUP MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralSum FunctionLatticeUP FunctionLatticeSeminormUP ConsistentCylinderFunctionalUP
  ProductCylinderLattice FiniteCoordinateProjection FiniteCoordinatePullback FiniteCoordinateMarginal
  FiniteCoordinateProductUP CoordinateDaniellOperator NormalizedProductSpace CompactContinuousPullback
  CompactSeparatedProduct HausdorffBinaryProduct SubtypeCompactHausdorff MonotoneCompactSupportFunctional
  DaniellSpaceCompactness DaniellProductUP DaniellProduct DaniellProductUniqueness FiniteCoordinateSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section AdjoinProduct.
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

(** Source for [finite_coordinate_space_compact]: compactness of X_a,
    Federer 2.6.6, p. 120, by Tychonoff's theorem for the factors of
    X_a; no point of X is needed. *)
Lemma finite_coordinate_space_compact (F : {fset I}) :
  compact (@setT (finite_coordinate_space Y F)).
Proof.
have h := @compact_factor_product_compact _ (fun j : {j : I | j \in F}=>Y (val j)) (fun j=>@hc (val j)).
exact h.
Qed.

(** Source for [finite_coordinate_space_hausdorff]: X_a is a
    Hausdorff space, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_space_hausdorff (F : {fset I}) :
  hausdorff_space (finite_coordinate_space Y F).
Proof. exact: hausdorff_product (fun j=>@hh (val j)). Qed.

(** Source for [binary_space_compact]: compactness of a cartesian
    product of two compact spaces, supporting the binary product of
    Federer 2.6.4, p. 119, as used in 2.6.6, p. 120. *)
Lemma binary_space_compact (S T : topologicalType) :
  compact (@setT S) -> compact (@setT T) -> compact (@setT (S * T)%type).
Proof.
move=> hS hT; have hST := compact_setX hS hT.
have he : (@setT S `*` @setT T)%classic = [set: (S * T)%type] by apply/seteqP; split=> p hp; [|split].
by rewrite he in hST.
Qed.

(** Source for [finite_coordinate_split_space_compact]: X_a x X_i is
    compact, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_space_compact (F : {fset I}) (i : I) :
  compact (@setT (finite_coordinate_space Y F * Y i)%type).
Proof. exact: (@binary_space_compact (finite_coordinate_space Y F) (Y i) (@finite_coordinate_space_compact F) (@hc i)). Qed.

(** Source for [finite_coordinate_split_space_hausdorff]: X_a x X_i is
    a Hausdorff space, Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_space_hausdorff (F : {fset I}) (i : I) :
  hausdorff_space (finite_coordinate_space Y F * Y i)%type.
Proof. exact: hausdorff_binary_product (@finite_coordinate_space_hausdorff F) (@hh i). Qed.

(** Source for [finite_coordinate_split_pullback]: (k o psi) o
    p_{a cup {i}} = k o (p_a, pi_i), Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_pullback (F : {fset I}) (i : I)
    (k : (finite_coordinate_space Y F * Y i)%type -> R) :
  (k \o @finite_coordinate_split I Y F i) \o finite_coordinate_projection (F:=i |` F)=
    (fun x=>k (finite_coordinate_projection (F:=F) x, x i)).
Proof. by []. Qed.

(** Source for [finite_coordinate_split_membership]: psi induces a map
    of K(X_a x X_i) into K(X_{a cup {i}}), Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_membership (F : {fset I}) (i : I)
    (k : (finite_coordinate_space Y F * Y i)%type -> R) :
  compactly_supported_continuous_functions k ->
  compactly_supported_continuous_functions (k \o @finite_coordinate_split I Y F i).
Proof.
move=> hk; apply: compact_continuous_pullback_membership hk.
- exact: finite_coordinate_space_compact.
- exact: finite_coordinate_split_continuous.
Qed.

(** Source for [finite_coordinate_split_cylinder]: the functions
    k o (p_a, pi_i), k in K(X_a x X_i), belong to L_{a cup {i}},
    Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_cylinder (F : {fset I}) (i : I)
    (k : (finite_coordinate_space Y F * Y i)%type -> R) :
  compactly_supported_continuous_functions k ->
  continuous_coordinate_functions (i |` F) (fun x=>k (finite_coordinate_projection (F:=F) x, x i)).
Proof.
move=> hk; rewrite -finite_coordinate_split_pullback.
exact: finite_coordinate_pullback_membership hX (finite_coordinate_split_membership hk).
Qed.

(** Source for [finite_coordinate_projection_dfwith]: p_a ignores a
    change of the coordinate i outside a, supporting the iterated
    integration of Federer 2.6.4, p. 119, in 2.6.6, p. 120. *)
Lemma finite_coordinate_projection_dfwith (F : {fset I}) (i : I) (x : X) (u : Y i) :
  i \notin F -> finite_coordinate_projection (F:=F) (dfwith x i u)=finite_coordinate_projection (F:=F) x.
Proof.
move=> hi; apply: functional_extensionality_dep=> -[j hj].
rewrite /finite_coordinate_projection /= dfwithout //.
by apply/eqP=> hij; move: hi; rewrite hij hj.
Qed.

(** Source for [finite_coordinate_adjoined_functional]: the image
    psi#(mu_{a cup {i}}) of mu_{a cup {i}} under the homeomorphism psi
    of X_{a cup {i}} onto X_a x X_i, Federer 2.6.6, p. 120;
    psi#(mu)(k) = mu(k o psi). *)
Definition finite_coordinate_adjoined_functional (F : {fset I}) (i : I)
    (k : (finite_coordinate_space Y F * Y i)%type -> R) :=
  finite_coordinate_marginal C (i |` F) (k \o @finite_coordinate_split I Y F i).

(** Source for [finite_coordinate_adjoin_daniell_product]: mu_{a cup {i}}
    is the product of mu_a and mu_i "constructed by the method of
    2.6.4", Federer 2.6.6, p. 120: its image under psi satisfies the
    laws of the product functional of 2.6.4, p. 119, namely it is a
    Daniell integral on K(X_a x X_i) with value mu_a(f) mu_i(g) on
    every separated product f x g. *)
Theorem finite_coordinate_adjoin_daniell_product (F : {fset I}) (i : I) :
  i \notin F ->
  is_daniell_product (finite_coordinate_marginal C F) (@A i) (@finite_coordinate_adjoined_functional F i).
Proof.
move=> hi; split.
- apply: monotone_daniell_integral_is_daniell.
  apply: monotone_compact_support_linear_daniell.
  + exact: finite_coordinate_split_space_hausdorff.
  + exact: compact_space_locally_compact (@finite_coordinate_split_space_compact F i).
  + split.
    * move=> f g hf hg; rewrite /finite_coordinate_adjoined_functional /finite_coordinate_marginal.
      rewrite !finite_coordinate_split_pullback.
      exact: (cylinder_family_linear hCc (i |` F)).1 _ _
        (finite_coordinate_split_cylinder hf) (finite_coordinate_split_cylinder hg).
    * move=> c f hf; rewrite /finite_coordinate_adjoined_functional /finite_coordinate_marginal.
      rewrite !finite_coordinate_split_pullback.
      exact: (cylinder_family_linear hCc (i |` F)).2 c _ (finite_coordinate_split_cylinder hf).
  + move=> f g hf hg hfg; rewrite /finite_coordinate_adjoined_functional /finite_coordinate_marginal.
    rewrite !finite_coordinate_split_pullback.
    apply: (cylinder_family_monotone hCc (finite_coordinate_split_cylinder hf)
      (finite_coordinate_split_cylinder hg))=> x.
    exact: hfg.
- move=> f g hf hg; rewrite /finite_coordinate_adjoined_functional /finite_coordinate_marginal.
  rewrite finite_coordinate_split_pullback /=.
  have hm := finite_coordinate_split_cylinder (compactly_supported_separated_product hf hg).
  rewrite /= in hm.
  rewrite (finite_coordinate_product_adjoin hC hi hm).
  have hAi := daniell_compact_support_linear (monotone_daniell_integral_is_daniell (@hA i)).
  have he : coordinate_daniell_operator A i
      (fun x=>f (finite_coordinate_projection (F:=F) x)*g (x i))=
      (fun x=>@A i g*(f \o finite_coordinate_projection (F:=F)) x).
    apply: funext=> x; rewrite /coordinate_daniell_operator.
    have hu : (fun u=>f (finite_coordinate_projection (F:=F) (dfwith x i u))*g (dfwith x i u i))=
        (fun u=>f (finite_coordinate_projection (F:=F) x)*g u).
      by apply: funext=> u; rewrite dfwithin finite_coordinate_projection_dfwith.
    by rewrite hu (hAi.2 _ _ hg) mulrC.
  have hl := (cylinder_family_linear hCc F).2 (@A i g) _ (finite_coordinate_pullback_membership hX hf).
  by rewrite he hl mulrC.
Qed.

(** Source for [finite_coordinate_adjoin_daniell_product_value]: the
    identification of Federer 2.6.6, p. 120, with the product
    functional of 2.6.4, p. 119: psi#(mu_{a cup {i}}) equals the
    product of mu_a and mu_i on K(X_a x X_i), for every choice of the
    proofs of its hypotheses. *)
Theorem finite_coordinate_adjoin_daniell_product_value (F : {fset I}) (i : I)
    (hXF : hausdorff_space (finite_coordinate_space Y F))
    (hlXF : locally_compact (@setT (finite_coordinate_space Y F)))
    (hYi : hausdorff_space (Y i)) (hlYi : locally_compact (@setT (Y i)))
    (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y F))
      (finite_coordinate_marginal C F))
    (hAi : is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
    (k : (finite_coordinate_space Y F * Y i)%type -> R) :
  i \notin F -> compactly_supported_continuous_functions k ->
  @finite_coordinate_adjoined_functional F i k=daniell_product hXF hlXF hYi hlYi hmu hAi k.
Proof.
move=> hi hk.
exact: (daniell_product_unique hXF hlXF hYi hlYi (finite_coordinate_adjoin_daniell_product hi)
  (daniell_product_specification hXF hlXF hYi hlYi hmu hAi) hk).
Qed.

(** Source for [finite_coordinate_adjoin_product_inverse_value]: the
    same identification read on X_{a cup {i}}: mu_{a cup {i}}(h) is the
    product of mu_a and mu_i evaluated at h o psi^{-1}, Federer 2.6.6,
    p. 120, and 2.6.4, p. 119. *)
Theorem finite_coordinate_adjoin_product_inverse_value (x0 : X) (F : {fset I}) (i : I)
    (hXF : hausdorff_space (finite_coordinate_space Y F))
    (hlXF : locally_compact (@setT (finite_coordinate_space Y F)))
    (hYi : hausdorff_space (Y i)) (hlYi : locally_compact (@setT (Y i)))
    (hmu : is_daniell_integral (@compactly_supported_continuous_functions R (finite_coordinate_space Y F))
      (finite_coordinate_marginal C F))
    (hAi : is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i))
    (h : finite_coordinate_space Y (i |` F) -> R) :
  i \notin F -> compactly_supported_continuous_functions h ->
  finite_coordinate_marginal C (i |` F) h=
    daniell_product hXF hlXF hYi hlYi hmu hAi (h \o @finite_coordinate_join I Y x0 F i).
Proof.
move=> hi hh0.
have hj : compactly_supported_continuous_functions (h \o @finite_coordinate_join I Y x0 F i).
  apply: compact_continuous_pullback_membership hh0.
  - exact: finite_coordinate_split_space_compact.
  - exact: finite_coordinate_join_continuous.
rewrite -(finite_coordinate_adjoin_daniell_product_value hXF hlXF hYi hlYi hmu hAi hi hj).
rewrite /finite_coordinate_adjoined_functional.
have -> : (h \o @finite_coordinate_join I Y x0 F i) \o @finite_coordinate_split I Y F i=h.
  by apply: funext=> u; rewrite /= finite_coordinate_join_split.
by [].
Qed.

(** Source for [coordinate_product_continuous]: supporting continuity
    of x -> prod_{j in s} f_j(x_j), Federer 2.6.6, p. 120. *)
Lemma coordinate_product_continuous (s : seq I) (f : forall j, Y j -> R) :
  (forall j, j \in s -> continuous (f j : Y j -> real_line_metric R)) ->
  continuous ((fun x : X=>\prod_(j <- s) f j (x j)) : X -> real_line_metric R).
Proof.
elim: s=> [|j s ih] hs.
- have -> : (fun x : X=>\prod_(j <- [::]) f j (x j))=(fun _=>1) by apply: funext=> x; rewrite big_nil.
  exact: cst_continuous.
- have -> : (fun x : X=>\prod_(k <- j :: s) f k (x k))=(fun x=>f j (x j)*\prod_(k <- s) f k (x k)).
    by apply: funext=> x; rewrite big_cons.
  move=> x; apply: (@continuousM R X _ _ x).
  + exact: continuous_comp (@proj_continuous I Y j x) (hs j (mem_head _ _) (x j)).
  + by apply: ih=> k hk; apply: hs; rewrite in_cons hk orbT.
Qed.

(** Source for [coordinate_product_cylinder]: the function
    prod_{j in a} f_j o pi_j belongs to L_a when every f_j is in K(X_j),
    Federer 2.6.6, p. 120. *)
Lemma coordinate_product_cylinder (F : {fset I}) (f : forall j, Y j -> R) :
  (forall j, j \in F -> compactly_supported_continuous_functions (f j)) ->
  continuous_coordinate_functions F (fun x : X=>\prod_(j <- F) f j (x j)).
Proof.
move=> hf; split; first split.
- by apply: coordinate_product_continuous=> j hj; exact: (hf j hj).1.
- exact: subclosed_compact (@real_function_support_closed R X _) hX (@subsetT _ _).
- by move=> x y hxy; apply: eq_big_seq=> j hj; rewrite (hxy j hj).
Qed.

(** Source for [finite_coordinate_product_separated_value]: the
    product formula mu_a(prod_{j in a} f_j o pi_j) = prod_{j in a}
    mu_j(f_j) for the finite products of Federer 2.6.6, p. 120,
    obtained by the method of 2.6.4, p. 119, one factor at a time;
    the left side is mu_a evaluated on L_a. *)
Theorem finite_coordinate_product_separated_value (F : {fset I}) (f : forall j, Y j -> R) :
  (forall j, j \in F -> compactly_supported_continuous_functions (f j)) ->
  C F (fun x : X=>\prod_(j <- F) f j (x j))=\prod_(j <- F) @A j (f j).
Proof.
elim/fset1U_rect: F=> [|i F hi ih] hf.
- have -> : (fun x : X=>\prod_(j <- fset0) f j (x j))=(fun _=>1).
    by apply: funext=> x; rewrite big_seq_fset0.
  by rewrite big_seq_fset0 (cylinder_family_one hCc).
- have hfF : forall j, j \in F -> compactly_supported_continuous_functions (f j).
    by move=> j hj; apply: hf; rewrite fset1Ur.
  have hm := coordinate_product_cylinder hf.
  rewrite (finite_coordinate_product_adjoin hC hi hm) big_fsetU1 //.
  have hAi := daniell_compact_support_linear (monotone_daniell_integral_is_daniell (@hA i)).
  have he : coordinate_daniell_operator A i (fun x : X=>\prod_(j <- i |` F) f j (x j))=
      (fun x=>@A i (f i)*(fun y : X=>\prod_(j <- F) f j (y j)) x).
    apply: funext=> x; rewrite /coordinate_daniell_operator.
    have hu : (fun u=>\prod_(j <- i |` F) f j (dfwith x i u j))=
        (fun u=>(\prod_(j <- F) f j (x j))*f i u).
      apply: funext=> u; rewrite big_fsetU1 // dfwithin mulrC; congr (_*_).
      apply: eq_big_seq=> j hj; rewrite dfwithout //.
      by apply/eqP=> hij; move: hi; rewrite hij hj.
    by rewrite hu (hAi.2 _ _ (hf i (fset1U1 i F))) mulrC.
  have hl := (cylinder_family_linear hCc F).2 (@A i (f i)) _ (coordinate_product_cylinder hfF).
  by rewrite he hl (ih hfF).
Qed.
End AdjoinProduct.
