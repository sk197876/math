(** Federer (1969), 1.6.3, pp. 24-25, intersection corollary with endpoint
    degrees. The auxiliary predicate in this file permits a nonzero scalar
    factor before a literal simple covector. It makes the endpoint arguments
    uniform without changing Federer's definition of simple zero-covectors
    as empty products. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors CovectorBoundary
  CovectorSimpleProducts DualitySimplicity DualityAnnihilator AnnihilatorDimension
  SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Scaled.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.

(** Source for [scaled_simple_covector]: Federer 1.6.3, pp. 24-25,
    local endpoint correction to simplicity under duality. Auxiliary
    predicate: a nonzero scalar multiple of a literal simple covector.
    This is not a redefinition of the book's simplicity predicate. *)
Definition scaled_simple_covector m (phi : A_m V K^o m) :=
  exists (c : K) (alpha : A_m V K^o m),
    c != 0 /\ simple_covector h2 alpha /\ phi = c *: alpha.

(** Source for [scalar_covector_zero_form]: Federer 1.6.3, p. 24,
    degree-zero boundary. Supporting agreement between the scalar
    covector notation and the constant zero-form. *)
Lemma scalar_covector_zero_form c : scalar_covector h2 V c = zero_form V (c : K^o).
Proof.
apply: (can_inj (@form_includeK K V K^o 0)).
by rewrite scalar_covector_include.
Qed.

(** Source for [scalar_covector_scale]: Federer 1.6.3, p. 24,
    degree-zero boundary. Supporting scalar multiplication identity. *)
Lemma scalar_covector_scale c d : c *: scalar_covector h2 V d = scalar_covector h2 V (c*d).
Proof.
rewrite !scalar_covector_zero_form.
exact: esym (linZ (@zero_form_linear K V K^o) c d).
Qed.

(** Source for [nonzero_covector_scaled_simple]: Federer 1.6.3,
    pp. 24-25, corrected endpoint treatment. Supporting principle:
    if a nonzero covector is simple whenever its degree is positive,
    it is always a nonzero scalar multiple of a literal simple covector. *)
Lemma nonzero_covector_scaled_simple m (phi : A_m V K^o m) :
  phi != 0 -> ((0 < m)%N -> simple_covector h2 phi) -> scaled_simple_covector phi.
Proof.
case: m phi => [|m] phi hphi hs.
- pose c : K := zero_form_value phi.
  have he : phi = c *: scalar_covector h2 V 1.
    by rewrite scalar_covector_scale mulr1 scalar_covector_zero_form /c zero_form_valueK.
  have hc : c != 0.
    apply/eqP=> hz; move: hphi; by rewrite he hz scale0r eqxx.
  exists c, (scalar_covector h2 V 1); split=> //; split=> //.
  by apply/scalar_covector_simple.
- exists 1, phi; split; first exact: oner_neq0.
  split; [exact: hs | by rewrite scale1r].
Qed.

(** Source for [covector_subspace_scale]: Federer 1.6.3, pp. 24-25,
    associated space and scalar factors in adapted bases. Supporting
    equality: a nonzero scalar multiple has the same associated space. *)
Lemma covector_subspace_scale m (phi : A_m V K^o m) c : c != 0 ->
  covector_subspace h2 (c *: phi) = covector_subspace h2 phi.
Proof.
move=> hc; apply: subspace_ext => a.
exact: (@covector_associated_scale_nonzero K h2 V m phi c hc a).
Qed.

(** Source for [scaled_simple_covector_product]: Federer 1.6.3,
    p. 25, product of dual covectors in the corollary. Supporting
    closure statement including all endpoint degrees. *)
Theorem scaled_simple_covector_product p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  scaled_simple_covector phi -> scaled_simple_covector psi ->
  scaled_simple_covector (form_wedge h2 (scalar_bilinear K) phi psi).
Proof.
move=> [c [a [hc [ha ->]]]] [d [b [hd [hb ->]]]].
exists (c*d), (form_wedge h2 (scalar_bilinear K) a b); split.
- by rewrite mulf_neq0.
- split; first exact: simple_covector_product ha hb.
  by rewrite (bilZl (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) p q))
    (bilZr (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) p q)) scalerA.
Qed.

(** Source for [scaled_covector_product_disjoint]: Federer 1.6.3,
    p. 25, nonvanishing condition in the intersection corollary.
    Supporting corrected endpoint form: allowing nonzero scalar factors
    does not change the equivalence with zero intersection of the
    associated covector spaces. *)
Theorem scaled_covector_product_disjoint p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  phi != 0 -> psi != 0 -> scaled_simple_covector phi -> scaled_simple_covector psi ->
  (form_wedge h2 (scalar_bilinear K) phi psi != 0 <->
    forall a, covector_subspace h2 phi a -> covector_subspace h2 psi a -> a=0).
Proof.
move=> hp hq [c [a [hc [ha hphi]]]] [d [b [hd [hb hpsi]]]].
have hpa : a != 0 by apply/eqP=> hz; move: hp; rewrite hphi hz scaler0 eqxx.
have hqb : b != 0 by apply/eqP=> hz; move: hq; rewrite hpsi hz scaler0 eqxx.
rewrite hphi hpsi (covector_subspace_scale _ hc) (covector_subspace_scale _ hd)
  (bilZl (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) p q))
  (bilZr (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) p q))
  !scaler_eq0 (negbTE hc) (negbTE hd) !orFb.
exact: simple_covector_product_disjoint hpa hqb ha hb.
Qed.

(** Source for [scaled_covector_product_space]: Federer 1.6.3,
    p. 25, associated space of the product in the corollary. Supporting
    endpoint form: the associated space of a nonzero product is the sum
    of the two associated spaces even in the presence of scalar factors. *)
Theorem scaled_covector_product_space p q (phi : A_m V K^o p) (psi : A_m V K^o q) :
  phi != 0 -> psi != 0 -> scaled_simple_covector phi -> scaled_simple_covector psi ->
  form_wedge h2 (scalar_bilinear K) phi psi != 0 -> forall a,
  covector_subspace h2 (form_wedge h2 (scalar_bilinear K) phi psi) a <->
    exists b c, covector_subspace h2 phi b /\ covector_subspace h2 psi c /\ a=b+c.
Proof.
move=> hp hq [c [a [hc [ha hphi]]]] [d [b [hd [hb hpsi]]]].
have hpa : a != 0 by apply/eqP=> hz; move: hp; rewrite hphi hz scaler0 eqxx.
have hqb : b != 0 by apply/eqP=> hz; move: hq; rewrite hpsi hz scaler0 eqxx.
rewrite hphi hpsi
  (bilZl (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) p q))
  (bilZr (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) p q))
  !scaler_eq0 (negbTE hc) (negbTE hd) !orFb => hab v.
rewrite (covector_subspace_scale _ hc) (covector_subspace_scale _ hd)
  (covector_subspace_scale _ hc) (covector_subspace_scale _ hd).
exact: simple_covector_product_space hpa hqb ha hb hab v.
Qed.
End Scaled.

(** Source for [D_p_scaled_simple]: Federer 1.6.3, pp. 24-25,
    simplicity under duality, with the endpoint correction. The dual
    of every nonzero simple vector is a nonzero scalar multiple of a
    literal simple covector, with no restriction on the output degree. *)
Theorem D_p_scaled_simple (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  p (hp : (p <= n)%N) (xi : exterior_power V p) :
  xi != 0 -> simple xi -> scaled_simple_covector h2
    (D_p (omega_lambda h2 (fun i => one_form (dual_basis he i)) (Lambda_top n)) hp xi).
Proof.
move=> hx hs; apply: nonzero_covector_scaled_simple.
- exact: (@canonical_D_p_nonzero K h2 V n e he p hp xi hx).
- move=> hd; have hpn : (p < n)%N by move: hd; rewrite subn_gt0.
  exact: (@D_p_simple_nonzero K h2 V n e he _ p hp xi hpn hx hs).
Qed.

(** Source for [D_upper_scaled_associated]: Federer 1.6.3, p. 25, subspace
    associated with the dual of the product. *)
Theorem D_upper_scaled_associated (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : exterior_power V n) p (hp : (p <= n)%N)
  (phi : A_m V K^o p) : volume != 0 -> phi != 0 -> scaled_simple_covector h2 phi ->
  forall v, FedererSimple.T (D_upper h2 volume hp phi) v <->
    forall a, covector_subspace h2 phi a -> a v = 0.
Proof.
move=> hv hphi [c [a [hc [ha hphiE]]]] v.
have ha0 : a != 0 by apply/eqP=> hz; move: hphi; rewrite hphiE hz scaler0 eqxx.
rewrite hphiE linearZ (covector_subspace_scale h2 _ hc).
change (FedererSimple.T (c *: D_upper h2 volume hp a) v <->
  forall f, covector_subspace h2 a f -> f v = 0).
rewrite (@associated_scale_nonzero K V (n-p) _ c hc v).
exact: (@D_upper_associated_annihilator K h2 V n e he volume p hp a hv ha0 ha v).
Qed.
