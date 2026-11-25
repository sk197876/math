(** Blueprint label new:projection_formula, continuity part (supporting
    Allard (1972), 3.2, printed p. 427, and DDG Lemma A.1). For
    L ∈ Hom(R^n, R^p) and S ∈ G(n, k) set A = S ∘ L^* ∘ L ∘ S + 1 - S and
    P = L ∘ S ∘ A^{-1} ∘ L^*. The set of (L, S) for which A is invertible
    equals {(L, S) : ||∧_k(L ∘ S)|| > 0}, it is open in
    Hom(R^n, R^p) × G(n, k), and [(L, S) ↦ P] is continuous on it. The
    algebraic part is AllardProjectionFormula.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology subtype_topology normedtype.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  AdjointCriteria OrthonormalFamilies OrthonormalParseval OrthogonalMaps OrthonormalFrameMap
  GrassmannAbbreviations GrassmannSubspaces GrassmannHomogeneousSpace EuclideanInnerProduct
  FiniteCoordinates EuclideanRectangularAdjoint EuclideanLinearMaps EuclideanLinearJacobian
  LinearGroupTopology LinearGroupSealed OrthogonalInjectionSpaces TopologicalProductMaps
  NormMetricScaleContinuity MetricSubsetBackground ModuleQuotient SubspaceCarrier.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardGrassmannSubspaces AllardJacobians AllardProjectionFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Continuity.
Variable R : realType.
Variables n p k : nat.
Local Notation Rn := (R_n R n).
Local Notation Rp := (R_n R p).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bp := (@euclidean_inner_product R p).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBp := (@euclidean_inner_productP R p).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbp := (@coordinate_basisP R p).
Local Notation HEn := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation HEnp := (inner_metric_space (hom_inner_productP hBn hBp hbn)).
Local Notation HEpn := (inner_metric_space (hom_inner_productP hBp hBn hbp)).
Local Notation HEpp := (inner_metric_space (hom_inner_productP hBp hBp hbp)).
Local Notation GA := (projection_grassmann R n k).
Local Notation idn := (hom_of_linear (linear_id Rn)).

(** Source for [euclidean_adjoint_hom_inner]: Federer 1.7.9, p. 35:
    L^* • L^* = L • L for L ∈ Hom(R^n, R^p). Supporting lemma. *)
Lemma euclidean_adjoint_hom_inner (L : Hom Rn Rp) :
  hom_inner hBp hBn hbp (euclidean_rectangular_adjoint L) (euclidean_rectangular_adjoint L) =
  hom_inner hBn hBp hbn L L.
Proof.
rewrite (hom_inner_orthonormal_sum hBp hBn hbp hbp (@coordinate_basis_orthonormal R p)).
rewrite (hom_inner_orthonormal_sum hBn hBp hbn hbn (@coordinate_basis_orthonormal R n)).
under eq_bigr do rewrite (orthonormal_parseval hBn (@coordinate_basis_orthonormal R n) hbn).
under [RHS]eq_bigr do rewrite (orthonormal_parseval hBp (@coordinate_basis_orthonormal R p) hbp).
rewrite exchange_big; apply: eq_bigr=> i _; apply: eq_bigr=> l _.
by rewrite (inner_symmetric hBn) euclidean_rectangular_adjoint_pairing.
Qed.

(** Source for [euclidean_adjoint_continuous]: Federer 1.7.9, p. 35:
    [L ↦ L^*] is an isometry of Hom(R^n, R^p) onto Hom(R^p, R^n), hence
    continuous. Supporting lemma. *)
Lemma euclidean_adjoint_continuous :
  continuous (fun L : HEnp => (euclidean_rectangular_adjoint L : HEpn)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R HEnp HEpn _ 1 ler01)=> L M.
rewrite !inner_metric_distanceE mul1r.
have -> : euclidean_rectangular_adjoint L - euclidean_rectangular_adjoint M =
    euclidean_rectangular_adjoint (L - M) by rewrite linearB.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr; exact: esym (euclidean_adjoint_hom_inner (L - M)).
Qed.

(** Source for [hom_comp_continuous_param]: Federer 2.7.16, p. 134:
    composition of continuous families of linear maps is continuous.
    Supporting lemma. *)
Lemma hom_comp_continuous_param (T : topologicalType) (U V W : lmodType R)
    (CU : U -> U -> R) (CV : V -> V -> R) (CW : W -> W -> R)
    (hCU : is_inner_product CU) (hCV : is_inner_product CV) (hCW : is_inner_product CW)
    (a : nat) (eu : 'I_a -> U) (heu : is_basis eu) (c : nat) (ev : 'I_c -> V) (hev : is_basis ev)
    (f : T -> inner_metric_space (hom_inner_productP hCV hCW hev))
    (g : T -> inner_metric_space (hom_inner_productP hCU hCV heu)) :
  continuous f -> continuous g ->
  continuous (fun t => (hom_comp (f t : Hom V W) (g t : Hom U V) :
    inner_metric_space (hom_inner_productP hCU hCW heu))).
Proof.
move=> hf hg t.
have hfg := topological_pair_continuous hf hg.
exact: (continuous_comp (hfg t) (@hom_composition_continuous_general R U V W CU CV CW hCU hCV hCW a eu c ev heu hev (f t, g t))).
Qed.

(** Source for [inner_metric_continuousD]: Federer 2.7.16, p. 134:
    addition is continuous on a finite dimensional inner product space,
    hence the sum of two continuous maps is continuous. Supporting
    lemma. *)
Lemma inner_metric_continuousD (T : topologicalType) (V : lmodType R) (C : V -> V -> R)
    (hC : is_inner_product C) (f g : T -> inner_metric_space hC) :
  continuous f -> continuous g -> continuous (fun t => (f t + g t : inner_metric_space hC)).
Proof.
move=> hf hg t.
have hp := topological_pair_continuous hf hg.
have ha : continuous (fun z : (inner_metric_space hC * inner_metric_space hC)%type => z.1 + z.2).
  exact: add_continuous.
exact: (continuous_comp (hp t) (ha (f t, g t))).
Qed.

(** Source for [inner_metric_continuousB]: Federer 2.7.16, p. 134:
    addition and negation are continuous, hence the difference of two
    continuous maps is continuous. Supporting lemma. *)
Lemma inner_metric_continuousB (T : topologicalType) (V : lmodType R) (C : V -> V -> R)
    (hC : is_inner_product C) (f g : T -> inner_metric_space hC) :
  continuous f -> continuous g -> continuous (fun t => (f t - g t : inner_metric_space hC)).
Proof.
move=> hf hg; apply: (inner_metric_continuousD hf)=> t.
exact: (continuous_comp (hg t) (opp_continuous (g t))).
Qed.

(** Source for [continuous_first_factor]: general topology, used for
    the continuity assertion of blueprint new:projection_formula: a
    continuous map of the first factor of X × Y is continuous on X × Y.
    Supporting lemma. *)
Lemma continuous_first_factor (X Y Z : topologicalType) (g : X -> Z) :
  continuous g -> continuous (fun z : (X * Y)%type => g z.1).
Proof. by move=> hg z; exact: (continuous_comp (@first_projection_continuous X Y z) (hg z.1)). Qed.

(** Source for [continuous_second_factor]: general topology, used for
    the continuity assertion of blueprint new:projection_formula: a
    continuous map of the second factor of X × Y is continuous on X × Y.
    Supporting lemma. *)
Lemma continuous_second_factor (X Y Z : topologicalType) (g : Y -> Z) :
  continuous g -> continuous (fun z : (X * Y)%type => g z.2).
Proof. by move=> hg z; exact: (continuous_comp (@second_projection_continuous X Y z) (hg z.2)). Qed.

(** Source for [continuous_subspace_compose]: general topology, used
    for the continuity assertion of blueprint new:projection_formula: the
    restriction of a continuous map to a subset with the relative
    topology is continuous. Supporting lemma. *)
Lemma continuous_subspace_compose (X Z : topologicalType) (A : set X) (g : X -> Z) :
  continuous g -> continuous (fun z : set_type A => g (set_val z)).
Proof.
have hv : continuous (set_val : set_type A -> X) by exact: initial_continuous.
by move=> hg z; exact: (continuous_comp (hv z) (hg (set_val z))).
Qed.

(** Source for [projection_formula_domain]: blueprint
    new:projection_formula: the set of (L, S) ∈ Hom(R^n, R^p) ×
    Hom(R^n, R^n) for which A = S ∘ L^* ∘ L ∘ S + 1 - S is invertible.
    Its intersection with Hom(R^n, R^p) × G(n, k) is the domain of the
    blueprint (projection_formula_domainE). Definition. *)
Definition projection_formula_domain : set (HEnp * HEn)%type :=
  [set z | injective (projection_formula_operator (z.1 : Hom Rn Rp) (z.2 : Hom Rn Rn))].

(** Source for [projection_formula_domainE]: blueprint
    new:projection_formula: for S ∈ G(n, k), A is invertible if and only
    if ||∧_k(L ∘ S)|| > 0. Direct formalisation. *)
Theorem projection_formula_domainE (L : Hom Rn Rp) (S : GA) :
  projection_formula_domain (L, set_val S) <->
  0 < euclidean_linear_jacobian k (hom_comp L (set_val S : Hom Rn Rn)).
Proof. exact: (projection_formula_operator_injective_jacobian _ (projection_grassmannP S)). Qed.

(** Source for [projection_formula_operator_continuous]: blueprint
    new:projection_formula: "[(L, S) ↦ A] is continuous". Supporting
    lemma. *)
Lemma projection_formula_operator_continuous :
  continuous (fun z : (HEnp * HEn)%type =>
    (projection_formula_operator (z.1 : Hom Rn Rp) (z.2 : Hom Rn Rn) : HEn)).
Proof.
have hL : continuous (fun z : (HEnp * HEn)%type => z.1) := @first_projection_continuous _ _.
have hS : continuous (fun z : (HEnp * HEn)%type => z.2) := @second_projection_continuous _ _.
have hLa : continuous (fun z : (HEnp * HEn)%type => (euclidean_rectangular_adjoint z.1 : HEpn)).
  by apply: continuous_first_factor; exact: euclidean_adjoint_continuous.
have hLS := hom_comp_continuous_param hL hS.
have hLLS := hom_comp_continuous_param hLa hLS.
have hSLLS := hom_comp_continuous_param hS hLLS.
have hId : continuous (fun z : (HEnp * HEn)%type => (idn : HEn)) by move=> z; exact: cvg_cst.
exact: (inner_metric_continuousB (inner_metric_continuousD hSLLS hId) hS).
Qed.

(** Source for [projection_formula_domain_open]: blueprint
    new:projection_formula: "the set in question is open". Direct
    formalisation. *)
Theorem projection_formula_domain_open : open projection_formula_domain.
Proof.
have -> : projection_formula_domain = (fun z : (HEnp * HEn)%type =>
    (projection_formula_operator (z.1 : Hom Rn Rp) (z.2 : Hom Rn Rn) : HEn))
    @^-1` linear_group hBn hbn by [].
apply: open_comp; last exact: linear_group_set_open.
by move=> z _; exact: projection_formula_operator_continuous.
Qed.

Local Notation D := (set_type projection_formula_domain).

(** Source for [projection_formula_on]: blueprint new:projection_formula:
    the map [(L, S) ↦ P] on its domain, with values in Hom(R^p, R^p).
    Definition. *)
Definition projection_formula_on (z : D) : HEpp :=
  @projection_formula_map R n p (set_val z).1 (set_val z).2 (set_valP z).

(** Source for [projection_formula_onP]: blueprint new:projection_formula:
    if S ∈ G(n, k), then P ∈ G(p, k). Direct formalisation. *)
Theorem projection_formula_onP (z : D) :
  is_orthogonal_projector hBn hbn k (set_val z).2 ->
  is_orthogonal_projector hBp hbp k (projection_formula_on z : Hom Rp Rp).
Proof. by move=> hS; exact: (projection_formula_orthogonal_projector hS (set_valP z)). Qed.

(** Source for [projection_formula_continuous]: blueprint
    new:projection_formula: "Hence [(L, S) ↦ P] is continuous" on its
    open domain, with the relative topology. Direct formalisation. *)
Theorem projection_formula_continuous : continuous projection_formula_on.
Proof.
have hL : continuous (fun z : D => ((set_val z).1 : HEnp)).
  by apply: continuous_subspace_compose; exact: first_projection_continuous.
have hS : continuous (fun z : D => ((set_val z).2 : HEn)).
  by apply: continuous_subspace_compose; exact: second_projection_continuous.
have hLa : continuous (fun z : D => (euclidean_rectangular_adjoint (set_val z).1 : HEpn)).
  apply: (continuous_subspace_compose (g := fun w : (HEnp * HEn)%type =>
    (euclidean_rectangular_adjoint w.1 : HEpn))).
  by apply: continuous_first_factor; exact: euclidean_adjoint_continuous.
have hAg : continuous (fun z : D =>
    projection_formula_operator_group (set_valP z : injective
      (projection_formula_operator (set_val z).1 (set_val z).2))).
  apply: (@continuous_comp_initial _ _ _ (@set_val HEn (linear_group hBn hbn))).
  exact: (continuous_subspace_compose projection_formula_operator_continuous).
have hinv : continuous (fun z : D => (projection_formula_inverse (set_valP z : injective
      (projection_formula_operator (set_val z).1 (set_val z).2)) : HEn)).
  have hi : continuous (fun a : set_type (linear_group hBn hbn) =>
      (set_val (linear_group_inv hBn hbn a) : HEn)).
    have hginv := linear_group_inv_continuous (linear_group_operations hBn hbn).
    have hv : continuous (set_val : set_type (linear_group hBn hbn) -> HEn).
      exact: initial_continuous.
    by move=> a; exact: (continuous_comp (hginv a) (hv _)).
  by move=> z; exact: (continuous_comp (hAg z) (hi _)).
have h1 := hom_comp_continuous_param hinv hLa.
have h2 := hom_comp_continuous_param hS h1.
exact: hom_comp_continuous_param hL h2.
Qed.

(** Source for [open_product_preimage]: general topology, used for the
    openness assertion of blueprint new:projection_formula: if f and g
    are continuous and O is open, then {(x, y) : (f(x), g(y)) ∈ O} is
    open. Supporting lemma. *)
Lemma open_product_preimage (X Y U V : topologicalType) (f : X -> U) (g : Y -> V)
    (O : set (U * V)%type) :
  continuous f -> continuous g -> open O -> open [set z : (X * Y)%type | O (f z.1, g z.2)].
Proof.
move=> hf hg hO.
have h1 : continuous (fun z : (X * Y)%type => f z.1) by apply: continuous_first_factor.
have h2 : continuous (fun z : (X * Y)%type => g z.2) by apply: continuous_second_factor.
have hp := topological_pair_continuous h1 h2.
have -> : [set z : (X * Y)%type | O (f z.1, g z.2)] =
    (fun z : (X * Y)%type => (f z.1, g z.2)) @^-1` O by [].
apply: open_comp; last exact: hO.
by move=> z _; exact: hp.
Qed.

(** Source for [projection_formula_grassmann_open]: blueprint
    new:projection_formula: the set {(L, S) : ||∧_k(L ∘ S)|| > 0} is open
    in Hom(R^n, R^p) × G(n, k). Direct formalisation. *)
Theorem projection_formula_grassmann_open :
  open [set z : (HEnp * GA)%type |
    0 < euclidean_linear_jacobian k (hom_comp (z.1 : Hom Rn Rp) (set_val z.2 : Hom Rn Rn))].
Proof.
have -> : [set z : (HEnp * GA)%type |
    0 < euclidean_linear_jacobian k (hom_comp (z.1 : Hom Rn Rp) (set_val z.2 : Hom Rn Rn))] =
    [set z : (HEnp * GA)%type |
      projection_formula_domain ((fun L : HEnp => L) z.1, (fun S : GA => (set_val S : HEn)) z.2)].
  apply/seteqP; split=> z hz.
  - exact/(projection_formula_domainE z.1 z.2).
  - exact/(projection_formula_domainE z.1 z.2).
have hid : continuous (fun L : HEnp => L) by move=> L; exact: cvg_id.
have hS : continuous (fun S : GA => (set_val S : HEn)) by exact: metric_subset_inclusion_continuous.
exact: (open_product_preimage hid hS projection_formula_domain_open).
Qed.
End Continuity.

Arguments projection_formula_domain R n p : clear implicits.
