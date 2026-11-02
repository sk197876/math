(** Federer (1969), 2.7.16, printed p. 139, example (6), from the proof of
    the second display: "To prove this we assume |xi| = 1 = |eta|, choose q
    in O*(n, n - k) with R^n cap {v : v wedge eta = 0} = ker q = im(1_{R^n}
    - q* o q), and observe that, for any zeta in Lambda_m R^n, |zeta wedge
    eta| = |<zeta, Lambda_m(q* o q)> wedge eta| = |<zeta, Lambda_m q>|".
    Here eta is a simple k-vector of norm 1 in a space V with an inner
    product B and a basis b of n vectors (V = R^n), and <zeta, Lambda_m q> =
    (Lambda_m q) zeta. Federer gives no argument for the existence of q or
    for the two equations; they are supplied. By 1.7.5, p. 32
    (SimpleOrthonormalFactor.v), eta = c f_1 wedge ... wedge f_k with f
    orthonormal and |c| = 1. The family f extends to an orthonormal basis d
    of V (1.7.3, p. 30), and q* is the orthogonal injection of R^{n-k}
    sending the standard basis to d_{k+1}, ..., d_n. Then v - q*(q(v)) is
    the orthogonal projection of v onto the span of f, which is R^n cap {v :
    v wedge eta = 0} by 1.6.1, p. 23. Since v wedge eta = (q* o q)(v) wedge
    eta for every vector v, an induction on the number of factors, using the
    anticommutativity of 1.3.1, p. 13, gives zeta wedge eta = <zeta,
    Lambda_m(q* o q)> wedge eta for every simple zeta. The second equation
    follows from 1.7.5, p. 32: the factors q*(q(v_i)) are orthogonal to f,
    so |<zeta, Lambda_m(q* o q)> wedge eta| = |<zeta, Lambda_m(q* o q)>|
    |eta|, and Lambda_m q* is an isometry (1.7.6, p. 33). The equations are
    proved for simple zeta, which is the case used by Federer. neither
    treats this passage. The local erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthonormalFamilies OrthogonalMaps AdjointUP
  Adjoint LinearBasis FiniteIndependence FiniteBasisComparison FiniteSpans FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection OrthonormalCapacityExtension
  OrthogonalInjectionSpaces OrthonormalFrameMap OrthonormalProjection OrthonormalParseval Bilinear
  ModuleQuotient GradedAlgebra GradedComponents AlgebraUP ExteriorAlgebra ExteriorGrading
  ExteriorAnticommutativity ExteriorMaps ExteriorMapScaling FiniteExteriorPowers
  ExteriorHomogeneousProducts InnerExterior ExteriorNorm ExteriorProjectionNorm AssociatedSubspace
  SimpleElementary SimpleProducts SimpleOrthonormalFactor ProductAssociatedOrthogonality
  SimpleWedgeEquality ExteriorMapNormContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section WordInvariance.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [wedge_word_vector_invariance]: "|zeta wedge eta| =
    |<zeta, Lambda_m(q* o q)> wedge eta|", Federer 2.7.16, p. 139: if
    v wedge y = P(v) wedge y for every vector v, then (v_1 wedge ... wedge
    v_m) wedge y = (P(v_1) wedge ... wedge P(v_m)) wedge y. Supporting
    lemma; the proof moves each factor next to y by the anticommutativity
    of 1.3.1, p. 13. P need not be linear. *)
Lemma wedge_word_vector_invariance (P : V -> V) (y : exterior_space V) :
  (forall v, wedge (exterior_generator v) y = wedge (exterior_generator (P v)) y) ->
  forall s, wedge (exterior_word s) y = wedge (exterior_word (map P s)) y.
Proof.
move=> hP.
have hswap (u : V) (W : exterior_space V) j : homogeneous (exterior_grading V) j W ->
    wedge (wedge (exterior_generator u) W) y =
      (-1 : K) ^+ (1 * j) *: wedge W (wedge (exterior_generator u) y).
  move=> hW.
  rewrite (@exterior_anticommutative K V 1 j (exterior_generator u) W
    (exterior_generator_homogeneous u) hW).
  by rewrite (bilZl (wedge_bilinear V)) wedge_assoc.
elim=> [|v s ih] //=.
rewrite !exterior_word_cons -!wedge_assoc ih !wedge_assoc.
rewrite (hswap v _ _ (exterior_word_homogeneous (map P s))).
rewrite (hswap (P v) _ _ (exterior_word_homogeneous (map P s))).
by rewrite hP.
Qed.

End WordInvariance.

Section KernelProjection.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variables (n : nat) (b : 'I_n -> V).
Hypothesis hb : is_basis b.
Local Notation CE j := (@euclidean_inner_product R j).
Local Notation hCE j := (@euclidean_inner_productP R j).
Local Notation eb j := (@coordinate_basis R j).
Local Notation heb j := (@coordinate_basisP R j).

(** Source for [wedge_kernel_projection_exists]: "choose q in
    O*(n, n - k) with R^n cap {v : v wedge eta = 0} = ker q =
    im(1_{R^n} - q* o q), and observe that, for any zeta in Lambda_m R^n,
    |zeta wedge eta| = |<zeta, Lambda_m(q* o q)> wedge eta| = |<zeta,
    Lambda_m q>|", Federer 2.7.16, p. 139, for a simple k-vector eta with
    |eta| = 1. Direct formalisation, with the proof supplied (see the
    header). The map h is q*: it is an orthogonal injection with adjoint
    q, so that q is an orthogonal projection (1.7.4, p. 30). The norm
    equation is asserted for simple zeta. *)
Theorem wedge_kernel_projection_exists k (eta : exterior_power V k) :
  simple eta -> exterior_norm h2 hB eta = 1 ->
  exists (q : {linear V -> R_n R (n - k)}) (h : {linear R_n R (n - k) -> V}),
  [/\ is_orthogonal_map (CE (n - k)) B h, is_adjoint (CE (n - k)) B h q,
    forall v, wedge (exterior_generator v) (component_val eta) = 0 <-> q v = 0,
    forall v, wedge (exterior_generator v) (component_val eta) = 0 <-> exists w, v = w - h (q w) &
    forall m (zeta : exterior_power V m), simple zeta ->
      exterior_norm h2 hB (exterior_product zeta eta) =
        exterior_norm h2 (hCE (n - k)) (exterior_power_map q m zeta)].
Proof.
move=> hs h1.
have heta0 : eta != 0.
  by apply/eqP=> h0; move: h1; rewrite h0 exterior_norm_zero => /eqP; rewrite eq_sym oner_eq0.
have [f [c [hf [hc hetaf]]]] := @simple_orthonormal_factor R h2 V B hB k eta heta0 hs.
have hfe0 : e_lambda f (ord_tuple k) != 0.
  by apply/eqP=> hz; move: heta0; rewrite hetaf hz scaler0 eqxx.
have hkn : (k <= n)%N := orthonormal_dimension_bound hB hb hf.
have [d [hd hdf]] := orthonormal_capacity_extension hB (finite_basis_independent hb) hf hkn.
have hdb : is_basis d := orthonormal_family_full_basis hB hb hd.
have hcl (j : 'I_(n - k)) : (k + j < n)%N by rewrite -ltn_subRL.
pose cv (j : 'I_(n - k)) := d (Ordinal (hcl j)).
have hcv : orthonormal_family B cv.
  move=> i j; rewrite /cv hd; congr (if _ then _ else _).
  apply/eqP/eqP=> [he|->] //; apply: val_inj; move: (congr1 val he) => /=; exact: addnI.
have hcvf (j : 'I_(n - k)) (i : 'I_k) : B (cv j) (f i) = 0.
  rewrite -(hdf i) /cv hd; case: ifP=> // /eqP /(congr1 val) /= he.
  by have := ltn_ord i; rewrite -he ltnNge leq_addr.
have [h [hho hhe]] := orthonormal_frame_map_exists hB hcv.
pose q := inner_adjoint (hCE (n - k)) hB (heb (n - k)) h.
have hq : is_adjoint (CE (n - k)) B h q := inner_adjointP _ _ _ h.
have hqf i : q (f i) = 0.
  apply/ffunP=> j; rewrite ffunE /=.
  rewrite -(euclidean_inner_basis (q (f i)) j) (inner_symmetric (hCE (n - k))) hq hhe.
  exact: hcvf.
pose Pf := orthonormal_projection hB f.
have hBhq v i : B (h (q v)) (f i) = 0 by rewrite -hq hqf (bil0r (inner_bilinear (hCE (n - k)))).
have hres v : v - h (q v) = Pf v.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  set w := v - h (q v) - Pf v.
  have hwd l : B w (d l) = 0.
    rewrite /w !(bilBl (inner_bilinear hB)).
    case: (ltnP l k)=> hl.
    - have -> : l = widen_ord hkn (Ordinal hl) by apply: val_inj.
      rewrite hdf hBhq.
      have := orthonormal_projection_coordinate hB hf v (Ordinal hl).
      rewrite !inner_coordinateE -/Pf => ->.
      by rewrite subr0 subrr.
    - have hj : (l - k < n - k)%N := ltn_sub2r (leq_ltn_trans hl (ltn_ord l)) (ltn_ord l).
      have -> : l = Ordinal (hcl (Ordinal hj)) by apply: val_inj; rewrite /= subnKC.
      rewrite -/(cv (Ordinal hj)).
      have e1 : B (h (q v)) (cv (Ordinal hj)) = B v (cv (Ordinal hj)).
        rewrite -hhe hho (inner_symmetric (hCE (n - k))) hq (inner_symmetric hB) //.
      have e2 : B (Pf v) (cv (Ordinal hj)) = 0.
        rewrite -inner_coordinateE /Pf /orthonormal_projection linear_sum.
        apply: big1=> i _; rewrite linearZ [inner_coordinate hB (cv _) _]inner_coordinateE.
        rewrite (inner_symmetric hB (f i)) hcvf.
        exact: mulr0.
      by rewrite e1 e2 subrr subr0.
  have hww : B w w = 0.
    rewrite (orthonormal_parseval hB hd hdb w); apply: big1=> l _; by rewrite hwd expr0n.
  by apply/eqP; rewrite -(negbK (w == 0)) -(inner_positive hB) hww ltxx.
have hT v : wedge (exterior_generator v) (component_val eta) = 0 <-> in_finite_span f v.
  rewrite -FedererSimple.associated_left hetaf (associated_scale_nonzero _ hc).
  exact: product_associated_space hfe0 v.
have hqspan v : in_finite_span f v -> q v = 0.
  move=> [a ->]; rewrite linear_sum; apply: big1=> i _.
  by rewrite linearZ /= hqf scaler0.
exists q, h; split=> //.
- move=> v; split; first by move/hT; exact: hqspan.
  move=> hv; apply/hT; have := hres v; rewrite hv linear0 subr0 => ->.
  exact: orthonormal_projection_in_span.
- move=> v; split.
    move=> hv; exists v; by rewrite (hqspan v (proj1 (hT v) hv)) linear0 subr0.
  move=> [w ->]; apply/hT; rewrite hres; exact: orthonormal_projection_in_span.
move=> m zeta [t ->]; rewrite tuple_product.
set v := tnth t.
pose P := linear_comp h q.
have hwP u : wedge (exterior_generator u) (component_val eta) =
    wedge (exterior_generator (P u)) (component_val eta).
  apply/eqP; rewrite -subr_eq0 -(bilBl (wedge_bilinear V)) -linearB /=; apply/eqP.
  apply/hT; rewrite /P /linear_comp /= hres; exact: orthonormal_projection_in_span.
have hprod : exterior_product (e_lambda v (ord_tuple m)) eta =
    exterior_product (e_lambda (P \o v) (ord_tuple m)) eta.
  apply: val_inj.
  change (wedge (component_val (e_lambda v (ord_tuple m))) (component_val eta) =
    wedge (component_val (e_lambda (P \o v) (ord_tuple m))) (component_val eta)).
  rewrite !e_lambdaE.
  by rewrite (wedge_word_vector_invariance hwP) -map_comp.
have hPe : e_lambda (P \o v) (ord_tuple m) =
    exterior_power_map h m (exterior_power_map q m (e_lambda v (ord_tuple m))).
  by rewrite exterior_power_map_composition exterior_power_map_e_lambda.
have hhn y : exterior_norm h2 hB (exterior_power_map h m y) = exterior_norm h2 (hCE (n - k)) y.
  exact: (exterior_orthogonal_norm h2 (hCE (n - k)) hB hho).
rewrite hprod.
case: (eqVneq (e_lambda (P \o v) (ord_tuple m)) 0)=> hz.
  rewrite hz (bil0l (@exterior_product_bilinear R V m k)) exterior_norm_zero.
  by rewrite -hhn -hPe hz exterior_norm_zero.
have horth : forall x y, FedererSimple.T (e_lambda (P \o v) (ord_tuple m)) x ->
    FedererSimple.T eta y -> B x y = 0.
  move=> x y hx hy.
  have hy' : FedererSimple.T (e_lambda f (ord_tuple k)) y.
    by move: hy; rewrite hetaf (associated_scale_nonzero _ hc).
  apply: (proj2 (product_associated_orthogonality h2 hB hz hfe0)) hx hy'.
  move=> i j; exact: hBhq.
have he := proj2 (simple_wedge_norm_equality h2 hB hz heta0 (product_simple _) hs) horth.
by rewrite he h1 mulr1 hPe hhn.
Qed.

(** Source for [wedge_kernel_projection_star]: the map q of
    wedge_kernel_projection_exists is a point of O*(n, n - k), Federer
    2.7.16, p. 139, "choose q in O*(n, n - k)"; the orthogonal
    projections are the adjoints of the orthogonal injections, 1.7.4,
    p. 30. Supporting lemma. *)
Lemma wedge_kernel_projection_star k (q : {linear V -> R_n R (n - k)})
    (h : {linear R_n R (n - k) -> V}) :
  is_orthogonal_map (CE (n - k)) B h -> is_adjoint (CE (n - k)) B h q ->
  is_orthogonal_projection B (CE (n - k)) q.
Proof. by move=> hh hq; exists h; split. Qed.

End KernelProjection.
