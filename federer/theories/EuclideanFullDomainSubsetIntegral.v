(** Federer (1969), 4.1.8, p. 362: the
    original Euclidean subset integral and its actual
    full-current-domain copy have the same definedness
    and value. Reuse the existing full-domain measure
    and exact image-integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations CurrentDomain EuclideanFullDomainMeasure
  EuclideanLebesgueDimensions ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  InjectiveSubsetIntegralTransport SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section EuclideanFullDomainSubsetIntegral.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation FT := (current_domain R n (fun _=>True)).
Local Notation gamma := (@euclidean_full_domain_measure R n).
Local Notation hGamma := (@euclidean_full_domain_measure_laws R n).1.
Local Notation Leb := (@euclidean_lebesgue_measure R n).

(** Source for [euclidean_full_domain_subset_integral_iff]:
    the original Euclidean subset integral agrees
    exactly with its full-domain copy, supporting
    the ordered-box current in Federer 4.1.8,
    p. 362, through the actual measure of
    4.1.7, pp. 357–358. *)
Theorem euclidean_full_domain_subset_integral_iff (B:set X) (g:X->R) a:
  is_measure_subset_integral Leb B (real_total_integrand g) a <->
  is_measure_subset_integral gamma (set_val @^-1` B)
    (real_total_integrand (fun x:FT=>g (set_val x))) a.
Proof.
have hInj:injective (set_val:FT->X).
  move=>x y h;apply:val_inj;exact:h.
have hIff:=@injective_image_subset_integral_iff R FT X gamma Leb hGamma
  (set_val:FT->X) B (real_total_integrand g) a hInj (@euclidean_full_domain_measure_ambient R n).
have hGraph x z:partial_function_graph (partial_function_zero_extension (0%E:extended_real_line R)
      (set_val @^-1` B) (partial_function_precompose (set_val:FT->X) (real_total_integrand g))) x z <->
    partial_function_graph (partial_function_zero_extension (0%E:extended_real_line R)
      (set_val @^-1` B) (real_total_integrand (fun x:FT=>g (set_val x)))) x z.
  have hInner:partial_function_graph (partial_function_precompose (set_val:FT->X)
      (real_total_integrand g)) x z <->
      partial_function_graph (real_total_integrand (fun x:FT=>g (set_val x))) x z.
    change (partial_function_graph (real_total_integrand g) (set_val x) z <->
      partial_function_graph (real_total_integrand (fun x:FT=>g (set_val x))) x z).
    by rewrite !real_total_integrand_graph.
  by rewrite !partial_function_zero_extension_graph hInner.
split=>hIntegral.
- exact:(measure_integral_graph_equivalent hGraph (hIff.1 hIntegral)).
- apply:hIff.2.
  exact:(measure_integral_graph_equivalent (fun x z=>iff_sym (hGraph x z)) hIntegral).
Qed.
End EuclideanFullDomainSubsetIntegral.
