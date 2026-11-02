(** Federer (1969), 1.6.3, pp. 24-25, simplicity under duality. Preservation
    of literal simplicity requires positive output degree: an arbitrary
    scalar is not a simple zero-vector or zero-covector. This restriction is
    a local correction, absent from the erratum. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors CovectorDimension SimpleAdaptedBasis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [initial_complement_M]: Federer 1.6.3, p. 25, sign
    in the displayed duality formula. Supporting count: every one of
    the first p indices precedes every complementary index. *)
Lemma initial_complement_M p n (hp : (p <= n)%N) :
  FedererInteriorSigns.M (Lambda_initial hp)
    (top_complement (Lambda_initial hp)) = (p * (n-p))%N.
Proof.
have h := FedererInteriorSigns.M_add_N
  (top_complement_disjoint (Lambda_initial hp)).
by rewrite /top_complement initial_complement_N addn0 in h.
Qed.

(** Source for [D_p_initial_basis]: Federer 1.6.3, p. 25, displayed
    adapted-basis formula. Direct statement: duality sends the product of
    the first p vectors to the complementary covector product with sign (-1)
    to the power p(n-p). *)
Theorem D_p_initial_basis (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  p (hp : (p <= n)%N) :
  D_p (omega_lambda h2 (fun i => one_form (dual_basis he i)) (Lambda_top n))
    hp (e_lambda e (val (Lambda_initial hp))) =
  (-1 : K)^+(p*(n-p)) *:
    omega_lambda h2 (fun i => one_form (dual_basis he i))
      (top_complement (Lambda_initial hp)).
Proof.
rewrite (@D_p_basis K h2 V n e (fun i => one_form (dual_basis he i))
  he (@finite_dual_biorthogonal K V n e he) p hp (Lambda_initial hp)).
by rewrite initial_complement_M.
Qed.

(** Source for [D_p_simple_nonzero]: Federer 1.6.3, pp. 24-25, simplicity
    under D_p. Direct corrected implication for a nonzero simple input and
    positive output degree; the top form may be any top-degree form. *)
Theorem D_p_simple_nonzero (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : A_m V K^o n) p (hp : (p <= n)%N)
  (xi : exterior_power V p) :
  (p < n)%N -> xi != 0 -> simple xi -> simple_covector h2 (D_p volume hp xi).
Proof.
move=> hpn hx hs.
have [b [hb ->]] := simple_adapted_basis he hp hx hs.
have hd : (0 < n-p)%N by rewrite subn_gt0.
rewrite (@top_covector_expansion K h2 V n b hb volume) /D_p
  (bilZr (@right_interior_bilinear K V K^o p n hp)).
apply: simple_covector_scale hd _.
change (simple_covector h2
  (D_p (omega_lambda h2 (fun i => one_form (dual_basis hb i)) (Lambda_top n))
    hp (e_lambda b (val (Lambda_initial hp))))).
rewrite D_p_initial_basis.
apply: simple_covector_scale; first by rewrite subn_gt0.
exact: omega_lambda_simple.
Qed.

(** Source for [dual_basis_realisation]: Federer 1.6.3, p. 25, adapted dual
    bases. Supporting linear algebra: any basis of the dual of a
    finite-dimensional space is dual to a basis of the space. This proves
    existence rather than assuming reflexivity. *)
Theorem dual_basis_realisation (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) (a : 'I_n -> Hom V K^o) :
  is_basis a -> exists b : 'I_n -> V, is_basis b /\
    forall i j, a i (b j) = if i == j then 1 else 0.
Proof.
move=> ha; have [b hb] := biorthogonal_exists (finite_basis_independent ha).
exists b; split=> //.
apply: (@finite_independent_basis K (finite_basis_vect he) n b).
- by rewrite finite_basis_dimension card_ord.
- apply: (@finite_independent_separating K 'I_n V b
    (fun i => hom_as_linear (a i))) => i j; exact: hb.
Qed.

(** Source for [D_upper_simple_nonzero]: Federer 1.6.3, p. 24, simplicity
    under D^p. Direct corrected implication for a nonzero simple input and
    positive output degree; any top vector may be used. The proof chooses
    adapted dual bases and uses 1.5.2. *)
Theorem D_upper_simple_nonzero (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : exterior_power V n) p (hp : (p <= n)%N)
  (phi : A_m V K^o p) :
  (p < n)%N -> phi != 0 -> simple_covector h2 phi ->
    simple (D_upper h2 volume hp phi).
Proof.
move=> hpn hphi hs.
have [xi [hx hphiE]] := @Omega_nonzero_preimage K h2 V n e he p phi hphi.
rewrite hphiE simple_covector_Omega in hs.
have [a [ha hxiE]] := simple_adapted_basis (dual_basisP he) hp hx hs.
have [b [hb hba]] := dual_basis_realisation he ha.
have hd i j : one_form (a i) [tuple b j] = if i == j then 1 else 0.
  by rewrite one_formE hba.
rewrite hphiE hxiE Omega_e_lambda (@top_expansion K h2 n V b hb volume)
  /D_upper (bilZl (@left_interior_bilinear K h2 V p n hp)).
have hn : (0 < n-p)%N by rewrite subn_gt0.
apply: simple_scale hn _.
change (simple (D_upper h2 (e_lambda b (val (Lambda_top n))) hp
  (omega_lambda h2 (fun i => one_form (a i)) (Lambda_initial hp)))).
rewrite (@D_upper_basis K h2 V n b (fun i => one_form (a i)) hb hd).
apply: simple_scale; first by rewrite subn_gt0.
exists [tuple of map b (val (top_complement (Lambda_initial hp)))].
apply: val_inj.
change (component_val (e_lambda b (val (top_complement (Lambda_initial hp)))) =
  component_val (e_lambda idfun [tuple of map b (val (top_complement (Lambda_initial hp)))])).
by rewrite !e_lambdaE map_id.
Qed.
