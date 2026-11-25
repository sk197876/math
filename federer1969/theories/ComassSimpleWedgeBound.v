(** Federer (1969), 1.8.1, p. 39: the binomial constant can be replaced by
    one when a wedge factor is simple. The supporting contraction estimate
    uses the associated subspace, simplicity under duality, and the Hodge
    isometry. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorNorm
  ExteriorNormNaturality ExteriorHomogeneousProducts AlternatingCoordinates
  AlternatingPairing AlternatingProduct CovectorProducts
  AssociatedSubspace SimpleCovectors SimpleUnitContraction LeftInterior
  LeftInteriorHom ComassUP ComassBounds ComassSimpleEquality ComassSphereBound
  LinearBasis ExteriorCovectorInner Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [left_contraction_pairing_add]: Federer 1.8.1,
    p. 39, supporting use of the characteristic identity in 1.5.1,
    p. 22. The reindexing only identifies (p+q)-p with q. *)
Lemma left_contraction_pairing_add (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) p q (x : exterior_power V (p+q))
    (phi : A_m V K^o p) (psi : A_m V K^o q) :
  pairing (exterior_reindex (addKn p q) (left_interior h2 (leq_addr q p) x phi)) psi =
    pairing x (form_wedge h2 (scalar_bilinear K) phi psi).
Proof.
change (form_homogeneous psi (component_val (exterior_reindex (addKn p q)
    (left_interior h2 (leq_addr q p) x phi))) =
  form_homogeneous (form_wedge h2 (scalar_bilinear K) phi psi) (component_val x)).
rewrite exterior_reindexE left_interiorE /form_wedge homogeneous_formK.
exact: left_interior_diagram.
Qed.

(** Source for [comass_simple_left_wedge_bound]: Federer 1.8.1,
    p. 39, sharp comass wedge inequality when the first factor
    is simple. The proof evaluates on simple unit vectors and uses
    the simple contraction from the associated top-dimensional space. *)
Theorem comass_simple_left_wedge_bound (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) p q
    (hp : (0 < p)%N) (hq : (0 < q)%N)
    (phi : A_m V R^o p) (psi : A_m V R^o q) a b c :
  simple_covector h2 phi -> is_comass h2 hB phi a -> is_comass h2 hB psi b ->
  is_comass h2 hB (form_wedge h2 (scalar_bilinear R) phi psi) c -> c <= a*b.
Proof.
move=> hs ha hb hc.
have ha0 := @comass_nonnegative R h2 V B hB p phi a hp ha.
have hb0 := @comass_nonnegative R h2 V B hB q psi b hq hb.
have hpq : (0 < p+q)%N := leq_trans hp (leq_addr q p).
apply: (@comass_simple_sphere_upper_bound R h2 V B hB (p+q) hpq
  (form_wedge h2 (scalar_bilinear R) phi psi) c (a*b) hc (mulr_ge0 ha0 hb0)) => x hx hNx.
have hlt : (p < p+q)%N by rewrite -{1}(addn0 p) ltn_add2l.
have [hz hNz] := @simple_unit_contraction R h2 V B hB n e he p (p+q)
  (leq_addr q p) x phi hlt hx hNx hs.
pose z := exterior_reindex (addKn p q) (left_interior h2 (leq_addr q p) x phi).
have hsz : simple z.
  have hr : forall j k (h : j=k) (u : exterior_power V j),
      simple u -> simple (exterior_reindex h u).
    by move=> j k h; case: k / h.
  exact: hr hz.
have hN : exterior_norm h2 hB z <= a.
  rewrite /z exterior_norm_reindex.
  have heq := @simple_comass_euclidean R h2 V B hB n e he p hp phi a hs ha.
  by rewrite heq.
rewrite -left_contraction_pairing_add.
have hh := @comass_simple_bound R h2 V B hB q hq psi b hb z hsz.
exact: (le_trans hh (ler_wpM2r hb0 hN)).
Qed.
