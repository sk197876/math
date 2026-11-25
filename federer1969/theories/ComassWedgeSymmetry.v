(** Federer (1969), 1.8.1, p. 39: either simple factor gives the sharp
    comass bound. The graded commutation law of 1.4.2, p. 19, transfers the
    first-factor proof to the second. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorHomogeneousProducts
  AlternatingCoordinates AlternatingPairing AlternatingSum AlternatingProduct
  LinearBasis SimpleCovectors ComassUP Comass ComassHomogeneity ComassSimpleWedgeBound Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [form_reindex_include]: Federer 1.8.1,
    p. 39, supporting identification of equal degrees when swapping
    the two factors. It changes no element of the full algebra. *)
Lemma form_reindex_include (K : fieldType) (V : lmodType K)
    p q (h : p=q) (phi : A_m V K^o p) :
  form_include (form_reindex h phi) = form_include phi.
Proof. by case: q / h. Qed.

(** Source for [form_wedge_reindex_swap]: Federer 1.8.1,
    p. 39, supporting signed interchange of factors from 1.4.2,
    p. 19. The sign disappears in the comass norm. *)
Lemma form_wedge_reindex_swap (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  form_wedge h2 (scalar_bilinear K) phi psi = (-1 : K)^+(p*q) *:
    form_reindex (addnC q p) (form_wedge h2 (scalar_bilinear K) psi phi).
Proof.
apply: (can_inj (@form_includeK K V K^o (p+q))).
rewrite linearZ.
change (form_include (form_wedge h2 (scalar_bilinear K) phi psi) =
  (-1 : K)^+(p*q) *: form_include (form_reindex (addnC q p)
    (form_wedge h2 (scalar_bilinear K) psi phi))).
rewrite form_reindex_include !form_wedge_include.
exact (@alternating_wedge_anticommutative K h2 V K^o (fun a b : K^o => a*b)
  (scalar_bilinear K) (@mulrC K) p q (form_include phi) (form_include psi)
  (form_include_homogeneous phi) (form_include_homogeneous psi)).
Qed.

(** Source for [comass_reindex]: Federer 1.8.1, p. 38,
    supporting invariance of the supremum under equality of degree indices. *)
Lemma comass_reindex (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    p q (h : p=q) (phi : A_m V R^o p) c :
  is_comass h2 hB phi c -> is_comass h2 hB (form_reindex h phi) c.
Proof. by case: q / h. Qed.

(** Source for [comass_simple_wedge_bound]: Federer 1.8.1,
    p. 39, the full sharp assertion when either factor is simple. *)
Theorem comass_simple_wedge_bound (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) p q
    (hp : (0 < p)%N) (hq : (0 < q)%N)
    (phi : A_m V R^o p) (psi : A_m V R^o q) a b c :
  (simple_covector h2 phi \/ simple_covector h2 psi) ->
  is_comass h2 hB phi a -> is_comass h2 hB psi b ->
  is_comass h2 hB (form_wedge h2 (scalar_bilinear R) phi psi) c -> c <= a*b.
Proof.
move=> [hs|hs] ha hb hc.
- exact: (@comass_simple_left_wedge_bound R h2 V B hB n e he p q hp hq phi psi a b c hs ha hb hc).
have hqp : (0 < q+p)%N := leq_trans hq (leq_addr p q).
pose theta := form_wedge h2 (scalar_bilinear R) psi phi.
pose d := @comass R h2 V B hB n e he (q+p) hqp theta.
have hd := @comassP R h2 V B hB n e he (q+p) hqp theta.
have hdr := @comass_reindex R h2 V B hB (q+p) (p+q) (addnC q p) theta d hd.
have hpq : (0 < p+q)%N := leq_trans hp (leq_addr q p).
rewrite form_wedge_reindex_swap in hc.
have hcd := @comass_absolute_homogeneity R h2 V B hB (p+q) hpq
  (form_reindex (addnC q p) theta) ((-1 : R)^+(p*q)) d c hdr hc.
rewrite normrX normrN normr1 expr1n mul1r in hcd.
rewrite hcd mulrC.
exact: (@comass_simple_left_wedge_bound R h2 V B hB n e he q p hq hp psi phi b a d hs hb ha hd).
Qed.
