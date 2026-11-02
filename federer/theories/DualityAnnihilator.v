(** Federer (1969), 1.6.3, pp. 24-25, associated subspaces under duality.
    Annihilator identities include the endpoint degrees, even when literal
    simplicity of the degree-zero image fails. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors SimpleCovectors SimpleAdaptedBasis
  CovectorDimension DualitySimplicity Annihilator SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [basis_vector_nonzero]: Federer 1.6.3, p. 25,
    adapted-basis proof. Supporting elementary fact: a member of a
    basis cannot be zero; derived from the basis universal property. *)
Lemma basis_vector_nonzero (K : fieldType) (I : choiceType) (V : lmodType K)
  (e : I -> V) (he : is_basis e) i : e i != 0.
Proof.
apply/eqP=> h.
have hi := congr1 (fun x => basis_coordinates he x i) h.
rewrite basis_coordinatesE linear0 deltaE eqxx free_zeroE in hi.
change ((1 : K) = 0) in hi.
by move: (oner_neq0 K); rewrite hi eqxx.
Qed.

(** Source for [biorthogonal_basis_unique]: Federer 1.6.3, p. 25,
    adapted dual bases. Supporting uniqueness: functionals with the
    prescribed Kronecker pairings are the coordinate dual basis. *)
Lemma biorthogonal_basis_unique (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) (a : 'I_n -> Hom V K^o) :
  (forall i j, a i (e j) = if i == j then 1 else 0) ->
  forall i, a i = dual_basis he i.
Proof.
move=> hd i; apply: hom_ext => v.
apply: (basis_linear_ext he (hom_as_linear (a i))
  (hom_as_linear (dual_basis he i))) v => j.
by rewrite hom_as_linearE hd hom_as_linearE dual_basisE eq_sym.
Qed.

(** Source for [basis_covector_associated]: Federer 1.6.3, p. 25,
    complementary covector product. Supporting instance: its associated
    subspace is the span of its factors, by transport through Omega. *)
Theorem basis_covector_associated (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  p (lambda : Lambda n p) a :
  covector_subspace h2
    (omega_lambda h2 (fun i => one_form (dual_basis he i)) lambda) a <->
  in_finite_span (fun j => dual_basis he (tnth (val lambda) j)) a.
Proof.
rewrite -(Omega_e_lambda h2 (dual_basis he) lambda) covector_associated_Omega.
have hx := basis_vector_nonzero (finite_e_lambda_basis (dual_basisP he) h2 p) lambda.
exact: (@indexed_product_associated K h2 (Choice.clone 'I_n _)
  (Hom V K^o) (dual_basis he) p (val lambda) hx a).
Qed.

(** Source for [basis_product_annihilator]: Federer 1.6.3, p. 25,
    first display and adapted-basis computation. Supporting equivalence:
    annihilating the associated subspace of a basis product means
    vanishing on precisely its selected basis vectors. *)
Theorem basis_product_annihilator (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  p (lambda : Lambda n p) a :
  annihilator (FedererSimple.T (e_lambda e (val lambda))) a <->
    forall i, i \in Lambda_set lambda -> a (e i) = 0.
Proof.
have hx : e_lambda e (val lambda) != 0.
  exact: basis_vector_nonzero (finite_e_lambda_basis he h2 p) lambda.
have ht : FedererSimple.T (e_lambda e (val lambda)) =
    finite_span_subspace (fun j => e (tnth (val lambda) j)).
  apply: subspace_ext => v.
  exact: (@indexed_product_associated K h2 (Choice.clone 'I_n _) V e p (val lambda) hx v).
rewrite ht annihilator_span; split.
- move=> ha i; rewrite /Lambda_set inE => /tnthP [j ->]; exact: ha.
- move=> ha j; apply: ha; rewrite /Lambda_set inE.
  exact: mem_tnth.
Qed.

(** Source for [D_p_associated_annihilator]: Federer 1.6.3, p. 25, first
    paragraph. Direct assertion: the associated space of the dual of a
    nonzero simple vector is the annihilator of its associated space. Any
    nonzero top form defines the same associated space; endpoint degrees are
    included. *)
Theorem D_p_associated_annihilator (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : A_m V K^o n) p (hp : (p <= n)%N)
  (xi : exterior_power V p) :
  volume != 0 -> xi != 0 -> simple xi ->
  covector_subspace h2 (D_p volume hp xi) = annihilator (FedererSimple.T xi).
Proof.
move=> hv hx hs.
have [b [hb hxi]] := simple_adapted_basis he hp hx hs.
pose c : K := pairing (e_lambda b (val (Lambda_top n))) volume.
have hc : c != 0.
  apply/eqP=> hz; apply: (elimT negP hv); apply/eqP.
  by rewrite (@top_covector_expansion K h2 V n b hb volume) -/c hz scale0r.
apply: subspace_ext => a.
rewrite hxi (@top_covector_expansion K h2 V n b hb volume) -/c /D_p
  (bilZr (@right_interior_bilinear K V K^o p n hp))
  (covector_associated_scale_nonzero h2 _ hc).
change (covector_subspace h2
  (D_p (omega_lambda h2 (fun i => one_form (dual_basis hb i)) (Lambda_top n)) hp
    (e_lambda b (val (Lambda_initial hp)))) a <->
  annihilator (FedererSimple.T (e_lambda b (val (Lambda_initial hp)))) a).
rewrite D_p_initial_basis.
have hsign : (-1 : K)^+(p*(n-p)) != 0 by rewrite expf_neq0 ?oppr_eq0 ?oner_eq0.
rewrite (covector_associated_scale_nonzero h2 _ hsign) (basis_covector_associated h2 hb)
  (basis_product_annihilator h2 hb).
exact: complementary_dual_span.
Qed.

(** Source for [basis_covector_common_kernel]: Federer 1.6.3, p. 25,
    annihilators under duality. Supporting equivalence: vanishing on the
    associated covector space of a basis product means vanishing on each of
    its factors. *)
Lemma basis_covector_common_kernel (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  p (lambda : Lambda n p) v :
  (forall a : Hom V K^o,
    covector_subspace h2
      (omega_lambda h2 (fun i => one_form (dual_basis he i)) lambda) a -> a v = 0)
  <-> forall i, i \in Lambda_set lambda -> dual_basis he i v = 0.
Proof.
split.
- move=> hv i; rewrite /Lambda_set inE => /tnthP [j ->].
  apply: hv; apply: (proj2 (basis_covector_associated h2 he lambda _)).
  exact: finite_span_generator.
- move=> hv a; rewrite (basis_covector_associated h2 he lambda) => [[c ->]].
  rewrite hom_sumE; apply: big1 => j _; rewrite hom_scaleE hv ?scaler0 //.
  rewrite /Lambda_set inE; exact: mem_tnth.
Qed.

(** Source for [D_upper_associated_annihilator]: Federer 1.6.3, pp. 24-25,
    duality identification of associated spaces. Endpoint degrees hold even
    when the literal simplicity of the image does not. *)
Theorem D_upper_associated_annihilator (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : exterior_power V n) p (hp : (p <= n)%N)
  (phi : A_m V K^o p) : volume != 0 -> phi != 0 -> simple_covector h2 phi ->
  forall v, FedererSimple.T (D_upper h2 volume hp phi) v <->
    forall a, covector_subspace h2 phi a -> a v = 0.
Proof.
move=> hv hphi hs v.
have [xi [hx hphiE]] := @Omega_nonzero_preimage K h2 V n e he p phi hphi.
rewrite hphiE simple_covector_Omega in hs.
have [a [ha hxiE]] := simple_adapted_basis (dual_basisP he) hp hx hs.
have [b [hb hba]] := dual_basis_realisation he ha.
have hae i : a i = dual_basis hb i := biorthogonal_basis_unique hb hba i.
have hphi' : phi = omega_lambda h2 (fun i => one_form (dual_basis hb i))
    (Lambda_initial hp).
  rewrite hphiE hxiE Omega_e_lambda.
  have heq : (fun i => one_form (a i)) = (fun i => one_form (dual_basis hb i)).
    by apply: funext => i; rewrite hae.
  by rewrite heq.
pose c : K := top_coordinate h2 hb volume.
have hc : c != 0.
  apply/eqP=> hz; apply: (elimT negP hv); apply/eqP.
  by rewrite (@top_expansion K h2 n V b hb volume) -/c hz scale0r.
rewrite hphi' (@top_expansion K h2 n V b hb volume) -/c /D_upper
  (bilZl (@left_interior_bilinear K h2 V p n hp))
  (@associated_scale_nonzero K V (n-p) _ c hc v).
change (FedererSimple.T
  (D_upper h2 (e_lambda b (val (Lambda_top n))) hp
    (omega_lambda h2 (fun i => one_form (dual_basis hb i)) (Lambda_initial hp))) v <->
  forall f, covector_subspace h2
    (omega_lambda h2 (fun i => one_form (dual_basis hb i)) (Lambda_initial hp)) f -> f v = 0).
rewrite (@D_upper_basis K h2 V n b (fun i => one_form (dual_basis hb i)) hb
  (@finite_dual_biorthogonal K V n b hb)) /top_complement initial_complement_N
  expr0 scale1r.
have hz := basis_vector_nonzero (finite_e_lambda_basis hb h2 (n-p))
  (top_complement (Lambda_initial hp)).
rewrite (@indexed_product_associated K h2 (Choice.clone 'I_n _) V b (n-p)
  (val (top_complement (Lambda_initial hp))) hz v)
  (basis_covector_common_kernel h2 hb).
exact: complementary_primal_span.
Qed.
