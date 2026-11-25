(** Federer (1969), 1.10.5, p. 48: supporting finite-dimensional compactness
    for the Hilbert-input norm equality. We prove continuity of scalar
    symmetric forms from the project's coordinate expansion, then select a
    norm-maximizing unit tuple whose sum has maximal length. These are local
    intermediate results, not separately stated in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom InnerProductUP InnerNorm InnerNormInequalities
  InnerMetric InnerNormedTopology InnerCoordinateContinuity LinearBasis
  OrthonormalFamilies OrthonormalisationUP GramSchmidt RealNormUP FiniteNormCompactness
  SymmetricForms SymmetricFormIsomorphism SymmetricProductContinuity CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_real_norm]: Federer 1.10.5,
    pp. 47-48, compatibility of the inner-product length with the
    abstract norm hypotheses, using the proved laws of 1.7.1, p. 28. *)
Lemma inner_norm_real_norm (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) : is_real_norm (inner_norm hB).
Proof.
split.
- split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
- move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
Qed.

Section Continuity.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Variable f : S_m V R^o m.

(** Source for [finite_scalar_symmetric_form_continuous]: Federer
    1.10.5, p. 48, supporting continuity on a finite-dimensional
    tuple space. A finite sum of products of continuous inner-product
    coordinates gives the actual scalar form, in all degrees. *)
Theorem finite_scalar_symmetric_form_continuous :
  continuous (fun u : 'I_m -> M => f [tuple u i | i<m]).
Proof.
have [d [hd ho]] := orthonormal_basis_exists hB he.
have hf : (fun u : 'I_m -> M => f [tuple u i | i<m]) =
  (fun u : 'I_m -> M => \sum_(a : {ffun 'I_m -> 'I_n})
    (\prod_i inner_coordinate hB (d (a i)) (u i))*f [tuple d (a i) | i<m]).
  apply: funext=> u.
  rewrite -(sform_to_hom_tuple f).
  rewrite (@symmetric_product_coordinate_expansion R V B hB n d hd
    (orthonormalisation_orthonormal ho) m u) linear_sum.
  apply: eq_bigr=> a _; rewrite linearZ.
  change ((\prod_i inner_coordinate hB (d (a i)) (u i))*
    sform_to_hom f (symmetric_tuple_component [tuple d (a i) | i<m]) =
    (\prod_i inner_coordinate hB (d (a i)) (u i))*f [tuple d (a i) | i<m]).
  by rewrite sform_to_hom_tuple.
rewrite hf; apply: continuous_big; first exact: add_continuous.
move=> a _ u; apply: continuousM; last exact: cst_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ v.
apply: (@continuous_comp (Topological.clone ('I_m -> M) _)
  (Topological.clone M _) (Topological.clone R^o _)
  (fun v => v i) (inner_coordinate hB (d (a i))) v).
- exact: proj_continuous.
- exact: inner_coordinate_continuous.
Qed.

(** Source for [finite_hilbert_unit_tuple_compact]: Federer
    1.10.5, p. 48, supporting compactness of the parameter
    set for maximizing a form. It is a finite product of compact
    closed unit balls, including the empty product and the zero space. *)
Lemma finite_hilbert_unit_tuple_compact :
  compact [set u : 'I_m -> M | forall i, inner_norm hB (u i)<=1].
Proof.
have hc : compact [set x:M|inner_norm hB x<=1].
  exact (@finite_norm_ball_compact R V B hB _ (inner_norm_real_norm hB) n e he 1).
exact (@tychonoff _ (fun _ : 'I_m => (Topological.clone M _))
  (fun _=>[set x:M|inner_norm hB x<=1]) (fun _=>hc)).
Qed.

(** Source for [hilbert_tuple_sum_norm_continuous]: Federer
    1.10.5, p. 48, supporting continuous secondary objective:
    the length of the sum of a finite tuple of vectors. *)
Lemma hilbert_tuple_sum_norm_continuous :
  continuous (fun u : 'I_m -> M => inner_norm hB (\sum_i (u i : V))).
Proof.
have hs : continuous (fun u : 'I_m -> M => (\sum_i u i : M)).
  apply: continuous_big; first exact: add_continuous.
  move=> i _; exact: proj_continuous.
have heq : (fun u : 'I_m -> M => inner_norm hB (\sum_i (u i : V))) =
    (fun u : 'I_m -> M => `|(\sum_i u i : M)|).
  apply: funext=> u; exact: esym (@inner_norm_topologyE R V B hB _).
rewrite heq; move=> u.
apply: continuous_comp (hs u) _; exact: norm_continuous.
Qed.

(** Source for [finite_hilbert_form_secondary_maximum]: Federer
    1.10.5, p. 48, supporting choice of a maximizing tuple.
    Among all unit-ball tuples maximizing the absolute form value,
    one maximizes the length of the sum of its entries. This choice
    is the compactness step of the local proof of the diagonal norm equality. *)
Theorem finite_hilbert_form_secondary_maximum : exists u : 'I_m -> M,
  (forall i, inner_norm hB (u i)<=1) /\
  (forall v : 'I_m -> M, (forall i, inner_norm hB (v i)<=1) ->
    `|f [tuple v i | i<m]| <= `|f [tuple u i | i<m]|) /\
  (forall v : 'I_m -> M, (forall i, inner_norm hB (v i)<=1) ->
    `|f [tuple v i | i<m]| = `|f [tuple u i | i<m]| ->
    inner_norm hB (\sum_i (v i : V)) <= inner_norm hB (\sum_i (u i : V))).
Proof.
pose A : set ('I_m -> M) := fun u=>forall i, inner_norm hB (u i)<=1.
pose F (u : 'I_m -> M) : R^o := `|f [tuple u i | i<m]|.
have hne : A !=set0.
  exists (fun _=>0)=> i; by rewrite inner_norm0 ler01.
have hA : compact A := finite_hilbert_unit_tuple_compact.
have hF : continuous F.
  rewrite /F; move=> u.
  apply: (@continuous_comp (Topological.clone ('I_m -> M) _)
    (Topological.clone R^o _) (Topological.clone R^o _)
    (fun v => f [tuple v i | i<m]) (fun r:R^o => `|r|) u).
  - exact: finite_scalar_symmetric_form_continuous.
  - exact: norm_continuous.
have [a [ha hmax]] := continuous_compact_maximum hne hA hF.
pose C : set ('I_m -> M) := fun u => F u=F a.
have hC : closed C.
  change (closed (F @^-1` [set F a])).
  apply: preimage_closed; first by move=> u _; exact: hF.
  apply: compact_closed; [exact: norm_hausdorff | exact: compact_set1].
have hE : A `&` C !=set0 by exists a; split.
have hcE : compact (A `&` C) := compact_closedI hA hC.
have [u [[hu hFu] hsum]] := continuous_compact_maximum hE hcE
  hilbert_tuple_sum_norm_continuous.
change (F u=F a) in hFu.
exists u; split=> //; split.
- move=> v hv; rewrite /F in hFu; rewrite hFu; exact: hmax hv.
- move=> v hv hfv; apply: hsum; split=> //.
  rewrite /C /F hfv; exact: hFu.
Qed.
End Continuity.
