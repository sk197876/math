(** Federer (1969), 1.6.3, p. 25, final corollary. The dimension equation is
    written k+n=p+r, equivalent to the book's integer equation k=p+r-n.
    Using truncated natural subtraction for the latter would give a false
    statement when p+r<n. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors Annihilator
  AnnihilatorIntersection AnnihilatorDimension DualityAnnihilator
  ScaledSimpleCovectors SubspaceSumDimension SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope nat_scope.

(** Source for [complementary_dimensions]: Federer 1.6.3, p. 25,
    dimension equation in the corollary. Supporting arithmetic:
    k+n=p+r iff the two annihilator dimensions add to n-k. *)
Lemma complementary_dimensions n p r k :
  (p <= n)%N -> (r <= n)%N -> (k <= n)%N ->
  ((k+n=p+r)%N <-> ((n-p)+(n-r)=n-k)%N).
Proof.
move=> hp hr hk.
have hs : ((n-p)+(n-r)+(p+r) = n+n)%N.
  by rewrite addnACA !subnK.
have hb : (((n-p)+(n-r) == n-k)%N) = ((k+n == p+r)%N).
  rewrite -(eqn_add2r k) (subnK hk) -(eqn_add2r (p+r)).
  by rewrite [((n-p)+(n-r)+k)+(p+r)]addnAC hs -addnA eqn_add2l [n+k]addnC.
split=> /eqP h; apply/eqP; [by rewrite hb | by rewrite -hb].
Qed.
Local Open Scope ring_scope.

Section Intersection.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variables p r : nat.
Hypotheses (hp : (p <= n)%N) (hr : (r <= n)%N).
Variable xi : exterior_power V p.
Variable eta : exterior_power V r.
Hypotheses (hx : xi != 0) (hy : eta != 0) (sx : simple xi) (sy : simple eta).
Local Notation ot := (omega_lambda h2 (fun i => one_form (dual_basis he i)) (Lambda_top n)).
Local Notation et := (e_lambda e (val (Lambda_top n))).
Local Notation T := (FedererSimple.T xi).
Local Notation U := (FedererSimple.T eta).
Local Notation I := (subspace_intersection T U).
Local Notation phi := (D_p ot hp xi).
Local Notation psi := (D_p ot hr eta).
Local Notation product := (form_wedge h2 (scalar_bilinear K) phi psi).

(** Source for [intersection_dimension_iff_dual_product]: Federer 1.6.3, p.
    25, first conclusion of the final corollary. Direct formalisation: if k
    is the dimension of the intersection, then k+n=p+r iff the alternating
    product of the dual covectors is nonzero. Endpoint degrees are included
    using the proved scalar-factor correction. *)
Theorem intersection_dimension_iff_dual_product k
  (a : 'I_k -> subspace_space I) (ha : is_basis a) :
  (k+n=p+r)%N <-> product != 0.
Proof.
have [hk [d hd]] := @annihilator_basis_exists K h2 V n e he I k a ha.
have [b hb] := @annihilator_simple_basis_exists K h2 V n e he p hp xi hx sx.
have [c hc] := @annihilator_simple_basis_exists K h2 V n e he r hr eta hy sy.
have hsum f : annihilator I f <->
    exists g h, annihilator T g /\ annihilator U h /\ f=g+h.
  exact: annihilator_intersection.
have hdim := @sum_dimension_iff_disjoint K (Hom V K^o)
  (annihilator T) (annihilator U) (annihilator I) hsum
  (n-p) (n-r) (n-k) b c d hb hc hd.
have hphi := @canonical_D_p_nonzero K h2 V n e he p hp xi hx.
have hpsi := @canonical_D_p_nonzero K h2 V n e he r hr eta hy.
have sphi := @D_p_scaled_simple K h2 V n e he p hp xi hx sx.
have spsi := @D_p_scaled_simple K h2 V n e he r hr eta hy sy.
have hprod := @scaled_covector_product_disjoint K h2 V (n-p) (n-r)
  phi psi hphi hpsi sphi spsi.
have ht := @D_p_associated_annihilator K h2 V n e he ot p hp xi
  (@canonical_top_covector_nonzero K h2 V n e he) hx sx.
have hu := @D_p_associated_annihilator K h2 V n e he ot r hr eta
  (@canonical_top_covector_nonzero K h2 V n e he) hy sy.
rewrite (complementary_dimensions hp hr hk) hdim.
by rewrite ht hu in hprod; symmetry.
Qed.

(** Source for [intersection_product_degree]: Federer 1.6.3,
    p. 25, degree of the final duality operation. Supporting bound:
    when the product of dual covectors is nonzero, its degree does
    not exceed n, so D to that degree is defined. *)
Lemma intersection_product_degree : product != 0 -> ((n-p)+(n-r) <= n)%N.
Proof.
move=> hz.
have [k [a [ha hk]]] := @finite_subspace_basis_exists K V n e he I.
have heq := proj2 (intersection_dimension_iff_dual_product ha) hz.
have hd := proj1 (complementary_dimensions hp hr hk) heq.
by rewrite hd; exact: leq_subr.
Qed.

(** Source for [intersection_dual_product_space]: Federer 1.6.3, p. 25,
    proof of the final conclusion. Supporting equality: the space associated
    with the nonzero covector product is the annihilator of T intersect U. *)
Lemma intersection_dual_product_space : product != 0 ->
  covector_subspace h2 product = annihilator I.
Proof.
move=> hz.
have hphi := @canonical_D_p_nonzero K h2 V n e he p hp xi hx.
have hpsi := @canonical_D_p_nonzero K h2 V n e he r hr eta hy.
have sphi := @D_p_scaled_simple K h2 V n e he p hp xi hx sx.
have spsi := @D_p_scaled_simple K h2 V n e he r hr eta hy sy.
have ht := @D_p_associated_annihilator K h2 V n e he ot p hp xi
  (@canonical_top_covector_nonzero K h2 V n e he) hx sx.
have hu := @D_p_associated_annihilator K h2 V n e he ot r hr eta
  (@canonical_top_covector_nonzero K h2 V n e he) hy sy.
apply: subspace_ext => f.
rewrite (@scaled_covector_product_space K h2 V (n-p) (n-r) phi psi
  hphi hpsi sphi spsi hz f) ht hu.
symmetry; exact: annihilator_intersection.
Qed.

(** Source for [intersection_duality_associated]: Federer 1.6.3, p. 25,
    final conclusion of the corollary. Direct formalisation: T intersect U
    is associated with D applied to the nonzero product D_p xi wedge D_r
    eta. Its input degree is written (n-p)+(n-r), equal to the book's 2n-p-r
    under hp and hr. The theorem includes all endpoint and zero-dimensional
    cases. *)
Theorem intersection_duality_associated (hz : product != 0) v :
  FedererSimple.T (D_upper h2 et (intersection_product_degree hz) product) v <->
    I v.
Proof.
have sphi := @D_p_scaled_simple K h2 V n e he p hp xi hx sx.
have spsi := @D_p_scaled_simple K h2 V n e he r hr eta hy sy.
have sp := scaled_simple_covector_product sphi spsi.
have het : et != 0 := @top_vector_nonzero K h2 n V e he.
rewrite (@D_upper_scaled_associated K h2 V n e he et ((n-p)+(n-r))
  (intersection_product_degree hz) product het hz sp v)
  (intersection_dual_product_space hz).
symmetry; exact: annihilator_separates.
Qed.
End Intersection.
