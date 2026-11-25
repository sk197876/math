(** Federer (1969), 4.1.19, p. 377: select
    the original bounded form representatives with literal
    global comass maximum equal to the cochain norm.
    Nonempty U is recorded explicitly because the earlier
    literal empty supremum is minus infinity. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain FlatCochainSpace CurrentLonePairFlatSealed
  CurrentGlobalComassSealed FlatCochainRepresentationUP
  FlatCochainOriginalPairCosts FlatCochainSelectedGlobalComass
  CurrentWeakExteriorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [flat_cochain_original_selected_global_comass]:
    the existential literal norm formula of
    Federer 4.1.19, p. 377, for the
    actual original cochain and actual q. No
    presentation, representation of currents or finite
    measure hypothesis is supplied by a caller. *)
Theorem flat_cochain_original_selected_global_comass
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : @flat_cochain_space R h2 n m U hU) :
  (exists x, U x) ->
  exists phi : R_n R n -> A_m (R_n R n) R^o m,
  exists psi : R_n R n -> A_m (R_n R n) R^o m.+1,
    @is_flat_cochain_pair_density R h2 n m U hU
      (@CurrentLonePairFlat.map R h2 n m U hU) alpha
      (fun x : current_domain R n U => phi (set_val x))
      (fun x : current_domain R n U => psi (set_val x)) /\
    @is_weak_current_exterior_pair R h2 n m U hU
      (fun x : current_domain R n U => phi (set_val x))
      (fun x : current_domain R n U => psi (set_val x)) /\
    (@flat_cochain_norm R h2 n m U hU alpha)%:E=
      Order.max (@CurrentGlobalComass.value R h2 n m U phi)
        (@CurrentGlobalComass.value R h2 n m.+1 U psi).
Proof.
exact: (@flat_cochain_selected_global_comass_exists R h2 n m U hU
  (@CurrentLonePairFlat.map R h2 n m U hU)
  (@CurrentLonePairFlat.laws R h2 n m U hU)
  (@flat_cochain_original_pair_first_cost R h2 n m U hU)
  (@flat_cochain_original_pair_second_cost R h2 n m U hU) alpha).
Qed.
