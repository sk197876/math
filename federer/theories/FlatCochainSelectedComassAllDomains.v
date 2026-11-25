(** Federer (1969), 4.1.19, p. 377: the
    selected bounded representation has the literal global
    comass formula with an explicit nonnegative endpoint.
    The original nonempty formula is separate, and
    no old global-comass definition is changed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain FlatCochainSpace CurrentLonePairFlatSealed
  CurrentGlobalComassSealed FlatCochainRepresentationUP
  FlatCochainOriginalRepresentation FlatCochainOriginalSelectedComass
  FlatCochainEmptyDomain CurrentWeakExteriorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [flat_cochain_selected_nonnegative_global_comass]:
    the selected literal global norm formula in
    Federer 4.1.19, p. 377, with
    its empty-domain endpoint stated explicitly. Every
    original open U and every natural degree are
    allowed; only the conclusion adjoins zero to
    the unchanged literal supremum at that endpoint. *)
Theorem flat_cochain_selected_nonnegative_global_comass
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : @flat_cochain_space R h2 n m U hU) :
  exists phi : R_n R n -> A_m (R_n R n) R^o m,
  exists psi : R_n R n -> A_m (R_n R n) R^o m.+1,
    @is_flat_cochain_pair_density R h2 n m U hU
      (@CurrentLonePairFlat.map R h2 n m U hU) alpha
      (fun x : current_domain R n U => phi (set_val x))
      (fun x : current_domain R n U => psi (set_val x)) /\
    @is_weak_current_exterior_pair R h2 n m U hU
      (fun x : current_domain R n U => phi (set_val x))
      (fun x : current_domain R n U => psi (set_val x)) /\
    (@flat_cochain_norm R h2 n m U hU alpha)%:E=Order.max 0%E
      (Order.max (@CurrentGlobalComass.value R h2 n m U phi)
        (@CurrentGlobalComass.value R h2 n m.+1 U psi)).
Proof.
case: (pselect (exists x, U x))=> hNonempty.
- have [phi [psi [hDensity [hWeak hGlobal]]]] :=
    @flat_cochain_original_selected_global_comass R h2 n m U hU alpha hNonempty.
  exists phi,psi; split; first exact: hDensity.
  split; first exact: hWeak.
  have hNonnegative : (0<=(@flat_cochain_norm R h2 n m U hU alpha)%:E)%E.
    rewrite lee_fin; exact: (@flat_cochain_norm_laws R h2 n m U hU alpha).1.1.
  by rewrite -hGlobal (max_idPr hNonnegative).
- have hEmpty (x : R_n R n) (hx : U x) : False.
    apply: hNonempty; by exists x.
  have [p [q [hDensity [hWeak _]]]] :=
    @flat_cochain_original_form_density_exists R h2 n m U hU alpha.
  have hP : p=(fun _ : current_domain R n U => 0).
    apply: funext=> x; exfalso; exact: (@hEmpty (set_val x) (set_valP x)).
  have hQ : q=(fun _ : current_domain R n U => 0).
    apply: funext=> x; exfalso; exact: (@hEmpty (set_val x) (set_valP x)).
  exists (fun _ => 0),(fun _ => 0); split.
  + by rewrite hP hQ in hDensity.
  split.
  + by rewrite hP hQ in hWeak.
  + exact: (@flat_cochain_empty_domain_global_comass R h2 n m U hU hEmpty
      alpha (fun _ => 0) (fun _ => 0)).
Qed.
